const {
  default: makeWASocket, useMultiFileAuthState, DisconnectReason,
  fetchLatestBaileysVersion, downloadMediaMessage
} = require('@whiskeysockets/baileys');
const pino = require('pino');
const qrcode = require('qrcode-terminal');
const fs = require('fs');
const path = require('path');
const os = require('os');
const dns = require('dns').promises;
const https = require('https');
const http = require('http');
const { URL } = require('url');
const crypto = require('crypto');
const { execFile, spawn } = require('child_process');
const { promisify } = require('util');
const execFileAsync = promisify(execFile);
// Load .env from the bot folder first, then from its parent folder (older layout).
// dotenv never overrides a variable that is already set, so the bot-folder file wins.
try { require('dotenv').config({ path: path.resolve(__dirname, '.env') }); } catch {}
try { require('dotenv').config({ path: path.resolve(__dirname, '..', '.env') }); } catch {}

const ROOT = __dirname;
const fetcher = require('./fetcher.cjs');
const CFG = require(path.join(ROOT, 'config.json'));
const DATA_DIR = path.join(ROOT, 'data');
const DL_DIR = path.join(ROOT, 'downloads');
const TEMP_DIR = path.join(DL_DIR, 'temp');
const MPM_DIR = path.join(ROOT, 'mpm');
// `upload` = local drop folder: files placed here are uploaded to the selected target group by the ,up command.
const DOWN_DIR = path.join(ROOT, 'upload');
// Migrate the old `down` folder (with any files still in it) to `upload`.
try {
  const oldDir = path.join(ROOT, 'down');
  if (fs.existsSync(oldDir) && !fs.existsSync(DOWN_DIR)) fs.renameSync(oldDir, DOWN_DIR);
} catch (e) { console.error('[up] could not rename old down folder:', e.message); }
for (const d of [DATA_DIR, DL_DIR, TEMP_DIR, DOWN_DIR, MPM_DIR, path.join(ROOT, 'auth_info')]) fs.mkdirSync(d, { recursive: true });
const BOOT_TIME = Date.now();
const DB_FILE = path.join(DATA_DIR, 'state.json');

// ---- Upload rules -----------------------------------------------------------------------------------
// WhatsApp cannot take files of 2 GB or more, so anything above 1.99 GB is refused with an error message.
const UPLOAD_MAX_BYTES = Math.floor(1.99 * 1024 * 1024 * 1024);
const UPLOAD_MAX_TEXT = '1.99 GB';
// Wait this long after one upload finishes before the next one starts (also keeps WhatsApp from dropping the connection).
const UPLOAD_GAP_MS = 5000;
let lastUploadEndedAt = 0;
async function waitUploadGap(task) {
  while (true) {
    if (task && task.cancelled) return;
    const wait = lastUploadEndedAt + UPLOAD_GAP_MS - Date.now();
    if (wait <= 0) return;
    if (task) task.progress = 'Next upload in ' + Math.ceil(wait / 1000) + 's';
    await new Promise(r => setTimeout(r, Math.min(wait, 1000)));
  }
}
function markUploadDone() { lastUploadEndedAt = Date.now(); }

function loadDB() {
  // A crash or power cut while saving used to leave a broken state.json, which silently reset all admins/limits.
  // Try the main file first, then the last good backup, and only then start empty.
  for (const f of [DB_FILE, DB_FILE + '.bak']) {
    try {
      const raw = fs.readFileSync(f, 'utf8');
      if (raw && raw.trim()) {
        const parsed = JSON.parse(raw);
        if (f !== DB_FILE) console.warn('[state] state.json was unreadable - restored from state.json.bak');
        return parsed;
      }
    } catch { /* try the next file */ }
  }
  return { admins: [], users: {}, blocked: [], lastUse: {}, targetGroups: [], selectedGroupJid: '' };
}
let db = loadDB();
db.admins ||= [];
db.blocked ||= [];
db.users ||= {};
db.lastUse ||= {};
// Preconfigured administrator requested by the bot owner.
const PRECONFIGURED_ADMIN = '94722984072';
if (!db.admins.includes(PRECONFIGURED_ADMIN)) {
  db.admins.push(PRECONFIGURED_ADMIN);
}
db.targetGroups ||= [];
db.selectedGroupJid ||= '';
function saveDB() {
  const tmp = DB_FILE + '.tmp';
  fs.writeFileSync(tmp, JSON.stringify(db, null, 2));
  try { if (fs.existsSync(DB_FILE)) fs.copyFileSync(DB_FILE, DB_FILE + '.bak'); } catch { /* backup is best effort */ }
  fs.renameSync(tmp, DB_FILE);
}
function setLinkedOwner(number) {
  // sock.user.id looks like "947XXXXXXXX:12@s.whatsapp.net"; the ":12" device
  // suffix must be removed, otherwise its digits get glued onto the number.
  const normalized = jidNumber(number);
  if (!normalized) return;
  if (!owner) {
    owner = normalized;
    db.owner = normalized;
    saveDB();
  } else if (owner !== normalized && owner.startsWith(normalized) && owner.length - normalized.length <= 3) {
    // Repair an owner that an older version saved with the device suffix attached.
    owner = normalized;
    db.owner = normalized;
    saveDB();
  }
}
saveDB();
// The first WhatsApp account that successfully links this bot becomes the permanent owner.
let owner = normalizeNumber(db.owner || '');
function normalizeNumber(s) { return String(s || '').replace(/[^0-9]/g, ''); }
function jidNumber(jid) { return normalizeNumber((jid || '').split('@')[0].split(':')[0]); }
function isAdmin(n) { return n === owner || db.admins.includes(n); }
function isOwner(n) { return n === owner; }
function bytes(n) {
  if (n >= 1024**3) return (n/1024**3).toFixed(2)+' GB';
  if (n >= 1024**2) return (n/1024**2).toFixed(1)+' MB';
  return (n/1024).toFixed(1)+' KB';
}
function todayKey() { return new Date().toLocaleDateString('en-CA'); }
function usage(n) {
  db.users[n] ||= {};
  if (db.users[n].day !== todayKey()) {
    const previous = db.users[n];
    db.users[n] = { ...previous, day: todayKey(), used: 0, count: 0 };
  }
  const u = db.users[n];
  if (!Number.isFinite(u.quotaUsedBytes)) u.quotaUsedBytes = 0;
  if (!Number.isFinite(u.quotaBytes)) u.quotaBytes = 0;
  if (!Number.isFinite(u.quotaDays)) u.quotaDays = 0;
  if (!Number.isFinite(u.quotaStartAt)) u.quotaStartAt = 0;
  return u;
}
function quotaInfo(u) {
  if (!(u.quotaBytes > 0) || !(u.quotaDays > 0) || !(u.quotaStartAt > 0))
    return { enabled: false, remainingBytes: Infinity, daysLeft: 0, expired: false };
  const expiresAt = u.quotaStartAt + u.quotaDays * 86400000;
  const msLeft = Math.max(0, expiresAt - Date.now());
  return { enabled: true, remainingBytes: Math.max(0, u.quotaBytes - u.quotaUsedBytes),
    daysLeft: Math.ceil(msLeft / 86400000), expired: msLeft <= 0 || u.quotaUsedBytes >= u.quotaBytes,
    expiresAt };
}
function quotaStatusText(u) {
  const q = quotaInfo(u);
  if (!q.enabled) return '🎟️ Assigned limit: Not set (unlimited)';
  const used = Math.min(u.quotaUsedBytes, u.quotaBytes);
  const remaining = Math.max(0, u.quotaBytes - used);
  const date = new Date(q.expiresAt).toLocaleString();
  return `🎟️ Assigned limit: ${bytes(u.quotaBytes)}\n📊 Used: ${bytes(used)} / ${bytes(u.quotaBytes)}\n📥 Remaining: ${bytes(remaining)}\n🗓️ Days left: ${q.daysLeft} day(s)\n⏳ Expires: ${date}\n${q.expired ? '⛔ LIMIT EXPIRED / EXHAUSTED' : '✅ LIMIT ACTIVE'}`;
}
function parseSize(value) {
  const m = String(value || '').trim().match(/^(\d+(?:\.\d+)?)\s*(B|KB|MB|GB|TB)?$/i);
  if (!m) return 0;
  const unit = (m[2] || 'B').toUpperCase();
  const power = ({ B: 0, KB: 1, MB: 2, GB: 3, TB: 4 })[unit];
  const n = Number(m[1]) * (1024 ** power);
  return Number.isSafeInteger(Math.floor(n)) ? Math.floor(n) : 0;
}
function activeTaskText(onlySender) {
  const list = [...activeTasks.values()].filter(t => !onlySender || t.sender === onlySender);
  if (!list.length) return onlySender ? '📭 You have no active tasks right now.' : '📭 No active tasks right now.';
  return (onlySender ? '🧾 [MPM] YOUR TASKS\n' : '🧾 [MPM] ACTIVE TASKS\n') + list.map(t =>
    `#${t.id} • ${String(t.phase).toUpperCase()}\nTask: ${t.label || '—'}\nUser: ${t.sender}\nFile: ${t.file || 'Resolving link…'}\nProgress: ${t.progress || 'Starting…'}\nSpeed: ${t.speed || '—'}`
  ).join('\n\n') + '\n\nCancel one task: ,cancel <id>';
}
const activeTasks = new Map();
let taskCounter = 0;

// ---- Persistent queue --------------------------------------------------------------------------------
// Every queued / running task is saved to data/queue.json. If the bot crashes or is restarted, the tasks are
// restored on the next start (downloads continue from their partial files, finished links/files are not repeated).
const QUEUE_FILE = path.join(DATA_DIR, 'queue.json');
const QUEUE_FILES_DIR = path.join(DATA_DIR, 'queue-files');
try { fs.mkdirSync(QUEUE_FILES_DIR, { recursive: true }); } catch {}
const persistedJobs = new Map();   // task id -> job record
function loadPersistedJobs() {
  try {
    const j = JSON.parse(fs.readFileSync(QUEUE_FILE, 'utf8'));
    return { counter: Number(j.counter) || 0, jobs: Array.isArray(j.jobs) ? j.jobs.filter(x => x && x.type && x.jid && x.sender) : [] };
  } catch { return { counter: 0, jobs: [] }; }
}
const bootQueue = loadPersistedJobs();
taskCounter = Math.max(taskCounter, bootQueue.counter);
function persistJobs() {
  try {
    const tmp = QUEUE_FILE + '.tmp';
    const jobs = [...persistedJobs.values()].map(j => { const c = { ...j }; delete c.torrentBuffer; return c; });
    fs.writeFileSync(tmp, JSON.stringify({ counter: taskCounter, jobs }));
    fs.renameSync(tmp, QUEUE_FILE);
  } catch (e) { console.error('[queue] could not save queue.json:', e && e.message); }
}
function removeQueueFiles(id) {
  try { for (const f of fs.readdirSync(QUEUE_FILES_DIR)) if (f.startsWith('t' + id + '.')) fs.rmSync(path.join(QUEUE_FILES_DIR, f), { force: true }); } catch {}
}
// A task is finished (done, failed or cancelled): forget it for good.
function endTask(taskId, task) {
  activeTasks.delete(taskId);
  if (persistedJobs.delete(task.id)) persistJobs();
  removeQueueFiles(task.id);
}

// ---- MPM progress card (double-line style) -------------------------------------------------------------
const CARD_BAR_LEN = 12;
function cardBar(pct) {
  const filled = Math.max(0, Math.min(CARD_BAR_LEN, Math.floor((Number(pct) || 0) / 100 * CARD_BAR_LEN)));
  return '⬢'.repeat(filled) + '⬡'.repeat(CARD_BAR_LEN - filled);
}
function cardSize(n) {
  n = Number(n) || 0;
  if (n >= 1024 ** 3) return (n / 1024 ** 3).toFixed(2) + 'GB';
  if (n >= 1024 ** 2) return (n / 1024 ** 2).toFixed(2) + 'MB';
  return (n / 1024).toFixed(2) + 'KB';
}
function cardDur(sec) {
  sec = Math.max(0, Math.round(Number(sec) || 0));
  const h = Math.floor(sec / 3600), m = Math.floor((sec % 3600) / 60), x = sec % 60;
  return h ? `${h}h${m}m${x}s` : m ? `${m}m${x}s` : `${x}s`;
}
function cardShort(name, max = 40) {
  name = String(name || '');
  return name.length > max ? name.slice(0, max - 1) + '…' : name;
}
// o: { phase:'download'|'upload', pct, done, total, speed, elapsed, eta, file, peers, estimated }
function mpmCard(task, o) {
  const up = o.phase === 'upload';
  const head = [
    up ? '╔═══『 ⬆️ 𝗠𝗣𝗠 𝗨𝗣𝗟𝗢𝗔𝗗𝗜𝗡𝗚 』═══╗' : '╔═══『 ⬇️ 𝗠𝗣𝗠 𝗗𝗢𝗪𝗡𝗟𝗢𝗔𝗗𝗜𝗡𝗚 』═══╗',
    `Task By ${task?.senderName || task?.sender || 'User'}  ( #ID${task?.sender || ''} ) [${task?.source || 'Link'}]`
  ];
  // Upload: WhatsApp gives no upload progress, so no bar / speed / time is shown.
  if (up) {
    const lines = [...head];
    if (o.file) lines.push(`┟ File → ${o.file}`);
    lines.push(`${o.file ? '┠' : '┟'} Size → ${o.total > 0 ? cardSize(o.total) : 'Unknown'}`);
    lines.push('┠ Status → Upload');
    return lines.join('\n');
  }
  const known = Number.isFinite(o.pct) && o.total > 0;
  if (o.phase === 'rar') head[0] = '╔═══『 🗜️ 𝗠𝗣𝗠 𝗖𝗥𝗘𝗔𝗧𝗜𝗡𝗚 𝗥𝗔𝗥 』═══╗';
  const lines = [...head, `┟ [${cardBar(known ? o.pct : 0)}] ${known ? Number(o.pct).toFixed(2) + '%' : '--'}`];
  if (o.file) lines.push(`┠ File → ${o.file}`);
  lines.push(`┠ Processed → ${cardSize(o.done)} of ${o.total > 0 ? cardSize(o.total) : 'Unknown'}`);
  lines.push(o.phase === 'rar' ? `┠ Status → Creating RAR${o.parts ? ' ( ' + o.parts + ' parts )' : ''}` : '┠ Status → Download');
  lines.push(`┠ Speed → ${cardSize(o.speed)}/s`);
  if (o.peers !== undefined && o.peers !== null) lines.push(`┠ Peers → ${o.peers} connected`);
  const el = Number(o.elapsed) || 0;
  lines.push(Number.isFinite(o.eta) && o.eta >= 0
    ? `┠ Time → ${cardDur(el)} of ${cardDur(el + o.eta)} ( ${cardDur(o.eta)} )`
    : `┠ Time → ${cardDur(el)}`);
  return lines.join('\n');
}

// ---- Files over the WhatsApp limit: split into parts and send them one by one ---------------------------------
// Order of preference: RAR volumes (WinRAR's Rar.exe) -> 7-Zip volumes (.7z.001) -> plain byte split (.001, .002 ...).
// Default part size is 1 GB; the user can choose another size in MB (10..1900). Turn off with  "splitLarge": false  in config.json.
const SPLIT_DEFAULT_MB = 1024, SPLIT_MIN_MB = 10, SPLIT_MAX_MB = 1900;
const mbToBytes = mb => Math.round(Math.min(SPLIT_MAX_MB, Math.max(SPLIT_MIN_MB, Number(mb) || SPLIT_DEFAULT_MB)) * 1048576);
const splitEnabled = () => CFG.splitLarge !== false;
const hardMaxBytes = () => splitEnabled() ? (Number(CFG.maxSplitBytes) || 10 * 1024 ** 3) : UPLOAD_MAX_BYTES;
const hardMaxText = () => splitEnabled() ? bytes(hardMaxBytes()) : UPLOAD_MAX_TEXT;

async function findTool(cands) {
  for (const c of cands) {
    try {
      if (path.isAbsolute(c)) { if (fs.existsSync(c)) return c; continue; }
      await execFileAsync(c, [], { timeout: 8000, windowsHide: true });
      return c;
    } catch (e) { if (e && e.code !== 'ENOENT' && !path.isAbsolute(c)) return c; }
  }
  return null;
}
function runTool(cmd, args, task, cwd) {
  return new Promise((resolve, reject) => {
    const child = spawn(cmd, args, { windowsHide: true, stdio: ['ignore', 'ignore', 'pipe'], ...(cwd ? { cwd } : {}) });
    let err = '';
    child.stderr.on('data', d => { err = (err + d).slice(-600); });
    if (task) task.process = child;
    child.once('error', reject);
    child.once('close', code => { if (task) task.process = null; code === 0 ? resolve() : reject(new Error(cmd + ' failed (' + code + '): ' + err.trim().split(/\r?\n/).slice(-2).join(' '))); });
  });
}
async function rawSplit(file, outDir, stem, partBytes) {
  const size = (await fs.promises.stat(file)).size;
  const n = Math.ceil(size / partBytes);
  for (let i = 0; i < n; i++) {
    const out = path.join(outDir, stem + '.' + String(i + 1).padStart(3, '0'));
    await new Promise((resolve, reject) => {
      const rs = fs.createReadStream(file, { start: i * partBytes, end: Math.min(size, (i + 1) * partBytes) - 1 });
      const ws = fs.createWriteStream(out);
      rs.on('error', reject); ws.on('error', reject); ws.on('close', resolve);
      rs.pipe(ws);
    });
  }
  return 'plain split';
}
// Returns { method, parts: [{ file, name }] }. `file` is moved/copied into a work folder under its real name first.
async function splitFileForUpload(file, finalName, workDir, task, archiveName, partBytes) {
  const inDir = path.join(workDir, 'in'), outDir = path.join(workDir, 'out');
  await fs.promises.mkdir(inDir, { recursive: true }); await fs.promises.mkdir(outDir, { recursive: true });
  const stem = String(finalName || 'file').replace(/[\\/:*?"<>|]+/g, '_').slice(0, 150) || 'file';
  const named = path.join(inDir, stem);
  const arc = String(archiveName || '').replace(/\.(rar|7z|zip|\d{3})$/i, '').replace(/[\\/:*?"<>|]+/g, '_').trim().slice(0, 120) || stem;
  try { await fs.promises.rename(file, named); } catch { await fs.promises.copyFile(file, named); }
  const vol = String(partBytes) + 'b';   // exact bytes: works for both rar and 7z
  let method;
  const rar = await findTool(['rar', path.join(ROOT, 'winrar', 'Rar.exe'), 'C:\\Program Files\\WinRAR\\Rar.exe', 'C:\\Program Files (x86)\\WinRAR\\Rar.exe']);
  if (rar) { await runTool(rar, ['a', '-m0', '-v' + vol, '-ep', '-y', '-idq', path.join(outDir, arc + '.rar'), named], task); method = 'RAR'; }
  else {
    const z7 = await findTool(['7z', '7zz', 'C:\\Program Files\\7-Zip\\7z.exe', 'C:\\Program Files (x86)\\7-Zip\\7z.exe']);
    if (z7) { await runTool(z7, ['a', '-mx0', '-v' + vol, '-y', path.join(outDir, arc + '.7z'), named], task); method = '7-Zip'; }
    else method = await rawSplit(named, outDir, arc, partBytes);
  }
  await fs.promises.rm(inDir, { recursive: true, force: true });
  const names = (await fs.promises.readdir(outDir)).sort((a, b) => a.localeCompare(b, undefined, { numeric: true, sensitivity: 'base' }));
  return { method, parts: names.map(n => ({ file: path.join(outDir, n), name: n })) };
}
function splitHowTo(method) {
  if (method === 'RAR') return 'Download ALL parts into one folder, then open the first one (.part1.rar) with WinRAR / 7-Zip and extract.';
  if (method === '7-Zip') return 'Download ALL parts into one folder, then open the .7z.001 file with 7-Zip and extract.';
  return 'Download ALL parts into one folder, then open the .001 file with 7-Zip (Extract), or join them: copy /b name.001+name.002 output';
}

// The bot asks for the RAR name first, then (15 s) for the part size in MB. The user's next plain message in that chat
// (or ",rar <text>") answers the question that is waiting.
const pendingRar = new Map();   // "chatJid|sender" -> { timer, parse, done }
const RAR_ASK_TIMEOUT_MS = 10 * 60 * 1000;
const RAR_SIZE_TIMEOUT_MS = 15 * 1000;
const RAR_SIZE_CHOICES = [
  { n: 1, mb: 1024, label: '1 GB', note: 'Default split size.' },
  { n: 2, mb: 1536, label: '1.5 GB', note: 'Medium volume split.' },
  { n: 3, mb: 1900, label: '1.9 GB', note: 'Fewer split volumes.' }
];
const NUM_EMOJI = { 1: '1️⃣', 2: '2️⃣', 3: '3️⃣' };
function waitPending(key, ms, parse) {
  return new Promise(resolve => {
    const prev = pendingRar.get(key); if (prev) prev.done(null);
    const done = v => { clearTimeout(timer); if (pendingRar.get(key)?.done === done) pendingRar.delete(key); resolve(v); };
    const timer = setTimeout(() => done(null), ms);
    pendingRar.set(key, { timer, parse, done });
  });
}
// name stage: "Avengers 2012", "Avengers 2012 size=500", "skip"
function parseRarName(t) {
  t = String(t || '').trim(); if (!t) return undefined;
  if (/^skip$/i.test(t)) return { name: '', mb: 0 };
  const m = t.match(/\s*\bsize\s*=\s*(\d+)\s*(?:mb)?\s*$/i);
  return m ? { name: t.slice(0, m.index).trim(), mb: Number(m[1]) } : { name: t, mb: 0 };
}
// size stage: "1" / "2" / "3" pick from the list; a bigger number (10+) is taken as MB; "skip" = 1 GB
function parseRarSize(t) {
  t = String(t || '').trim();
  if (/^(skip|default)$/i.test(t)) return { mb: 0 };
  const m = t.match(/^(?:size\s*=?\s*)?(\d+)\s*(?:mb)?$/i);
  if (!m) return undefined;                       // anything else is not an answer: keep waiting
  const n = Number(m[1]);
  const pick = RAR_SIZE_CHOICES.find(c => c.n === n);
  if (pick) return { mb: pick.mb };
  return n >= SPLIT_MIN_MB ? { mb: n } : undefined;
}
// Called from index.js for plain (non-command) messages. Returns true when the message answered the waiting question.
async function tryPendingRarReply(sock, msg, text) {
  if (!msg?.message || msg.key.fromMe) return false;
  const jid = msg.key.remoteJid; if (!jid || !pendingRar.size) return false;
  const senderLid = jidNumber(sock.user?.lid || '');
  const rawSender = jidNumber(jid.endsWith('@g.us') ? (msg.key.participant || '') : jid);
  const sender = (senderLid && rawSender === senderLid && owner) ? owner : rawSender;
  const p = pendingRar.get(jid + '|' + sender);
  if (!p) return false;
  const v = p.parse(text);
  if (v === undefined) return false;
  p.done(v); return true;
}

async function sendLargeFile(sock, sendJid, file, finalName, progress, cardTask, task, batchFile, askCtx) {
  const size = (await fs.promises.stat(file)).size;
  if (!splitEnabled()) throw new Error('File too large: ' + bytes(size) + '. Maximum upload size is ' + UPLOAD_MAX_TEXT + '.');
  await fetcher.ensureDisk(TEMP_DIR, size, DISK_RESERVE);   // splitting needs about one more copy of the file on disk
  const workDir = path.join(TEMP_DIR, 'split-' + Date.now() + '-' + Math.random().toString(16).slice(2));
  try {
    if (task) { task.phase = 'splitting'; task.file = finalName; task.progress = 'splitting'; }
    let archiveName = '', partMB = 0;
    if (askCtx?.jid && askCtx?.sender) {
      const key = askCtx.jid + '|' + askCtx.sender;
      if (task) { task.phase = 'waiting'; task.file = finalName; task.progress = 'waiting for RAR name'; }
      const namePending = waitPending(key, RAR_ASK_TIMEOUT_MS, parseRarName);
      try {
        await sock.sendMessage(askCtx.jid, { text:
          '📦 *[MPM] BIG FILE*\n' + finalName + '\nSize: *' + bytes(size) + '* (WhatsApp max is ' + UPLOAD_MAX_TEXT + ')\n\n' +
          '✍️ Send the *name* you want for the RAR (just type it).\n' +
          'Next you will choose the part size (1 GB / 1.5 GB / 1.9 GB).\n\n' +
          '• Type *skip* → use the original file name\n' +
          '• No reply in 10 minutes → original name is used' });
      } catch {}
      const r = await namePending;
      if (task?.cancelled) throw new Error('Task cancelled by user.');
      if (r) { archiveName = r.name; partMB = r.mb; }
      if (!partMB) {
        // Part size: pick from a numbered list (no reply -> 1 GB).
        const sizePending = waitPending(key, RAR_SIZE_TIMEOUT_MS, parseRarSize);
        try {
          await sock.sendMessage(askCtx.jid, { text:
            '📦 *𝗥𝗔𝗥 𝗣𝗔𝗥𝗧𝗦*\n' +
            '┌─────────────────────────────\n' +
            RAR_SIZE_CHOICES.map(c => '│ ' + NUM_EMOJI[c.n] + ' `' + c.n + '` — **' + c.label + '**\n│    └ _' + c.note + '_\n').join('') +
            '└─────────────────────────────\n' +
            'Reply with `1`, `2`, or `3`\n' +
            '⏳ _No reply in ' + (RAR_SIZE_TIMEOUT_MS / 1000) + 's → 1 GB_' });
        } catch {}
        const z = await sizePending;
        if (task?.cancelled) throw new Error('Task cancelled by user.');
        if (z) partMB = z.mb;
      }
    }
    const partBytes = mbToBytes(partMB);
    const partsInfo = Math.ceil(size / partBytes);
    if (task) { task.phase = 'splitting'; task.progress = 'splitting'; }
    await sock.sendMessage(askCtx?.jid || sendJid, { text: '🗜️ [MPM] Creating RAR' + (archiveName ? ' *' + archiveName + '*' : '') + ': ' + partsInfo + ' parts × ' + Math.round(partBytes / 1048576) + ' MB, please wait…' });
    // Progress bar: poll the size of the parts written so far (works the same for RAR, 7-Zip and plain split).
    const outDir = path.join(workDir, 'out');
    const rarStart = Date.now(); let lastDone = 0, lastTick = rarStart, stopMon = false;
    const tickMs = Math.max(3, Number(CFG.progressIntervalSeconds) || 5) * 1000;
    const showRar = async (done, final) => {
      const now = Date.now();
      const speed = Math.max(0, done - lastDone) / Math.max(0.5, (now - lastTick) / 1000);
      lastDone = done; lastTick = now;
      const el = (now - rarStart) / 1000;
      const avg = done / Math.max(1, el);
      try {
        await progress.update(mpmCard(cardTask, {
          phase: 'rar', pct: final ? 100 : Math.min(99.9, done / size * 100), done: Math.min(done, size), total: size,
          speed: final ? avg : speed, elapsed: el, eta: final ? 0 : (avg > 0 ? Math.max(0, (size - done) / avg) : NaN),
          parts: partsInfo, file: finalName
        }));
      } catch {}
    };
    const dirSize = async () => { let t = 0; try { for (const n of await fs.promises.readdir(outDir)) { try { t += (await fs.promises.stat(path.join(outDir, n))).size; } catch {} } } catch {} return t; };
    const monitor = (async () => {
      await showRar(0, false);
      while (!stopMon) {
        for (let w = 0; w < tickMs && !stopMon; w += 500) await new Promise(r => setTimeout(r, 500));
        if (stopMon) break;
        await showRar(await dirSize(), false);
      }
    })();
    let splitResult;
    try { splitResult = await splitFileForUpload(file, finalName, workDir, task, archiveName, partBytes); }
    finally { stopMon = true; await monitor.catch(() => {}); }
    await showRar(size, true);
    const { method, parts } = splitResult;
    if (task?.cancelled) throw new Error('Task cancelled by user.');
    if (!parts.length) throw new Error('Splitting produced no files.');
    if (task) task.phase = 'uploading';
    for (let i = 0; i < parts.length; i++) {
      if (task?.cancelled) throw new Error('Task cancelled by user.');
      const part = parts[i]; const psize = (await fs.promises.stat(part.file)).size;
      await waitUploadGap(task);
      try {
        await uploadWithCard(progress, cardTask, { size: psize, file: 'Part ' + (i + 1) + '/' + parts.length + ' • ' + cardShort(part.name) }, () => sock.sendMessage(sendJid, {
          document: { url: part.file }, fileName: part.name, mimetype: 'application/octet-stream'
        }));
      } finally { markUploadDone(); }
      await fs.promises.rm(part.file, { force: true });   // free disk as we go
    }
    await sock.sendMessage(sendJid, { text: '✅ [MPM] Sent ' + parts.length + ' parts (' + method + ') for ' + finalName + '.\n' + splitHowTo(method) });
    return parts.length;
  } finally { await fs.promises.rm(workDir, { recursive: true, force: true }).catch(() => {}); }
}

async function uploadWithCard(progress, task, o, sendFn) {
  await progress.update(mpmCard(task, { phase: 'upload', total: Number(o.size) || 0, file: o.file }));
  // A WhatsApp connection drop mid-upload used to lose the whole file (it is deleted afterwards).
  // Retry transient failures up to 3 times, waiting longer each time so the bot can reconnect.
  const maxTries = 3;
  for (let attempt = 1; ; attempt++) {
    try { return await sendFn(); }
    catch (e) {
      const m = String((e && e.message) || e);
      const transient = /connection|closed|timed? ?out|reset|socket|stream|rate-overlimit|ECONN|ETIMEDOUT|EPIPE|network|fetch failed|upload/i.test(m);
      if (attempt >= maxTries || !transient || /cancel/i.test(m) || (task && task.cancelled)) throw e;
      console.warn('Upload failed (attempt ' + attempt + '/' + maxTries + '), retrying: ' + m);
      await new Promise(r => setTimeout(r, 8000 * attempt));
    }
  }
}
// Short human-readable name for a task (shown in the ,cancel list).
function taskLabel(input, extraCount = 0) {
  let text = String(input || '').trim();
  try {
    if (/^magnet:/i.test(text)) {
      const dn = text.match(/[?&]dn=([^&]+)/i);
      text = dn ? decodeURIComponent(dn[1].replace(/\+/g, ' ')) : 'Magnet link';
    } else if (/^https?:\/\//i.test(text)) {
      const u = new URL(text);
      const last = decodeURIComponent(u.pathname.split('/').filter(Boolean).pop() || '');
      text = last ? `${last} (${u.hostname})` : u.hostname;
    }
  } catch {}
  if (text.length > 70) text = text.slice(0, 67) + '…';
  return (text || 'Task') + (extraCount > 0 ? ` (+${extraCount} more)` : '');
}
// Registers a task right away (while it is still waiting in the queue) so it can be listed and cancelled by id.
function registerTask(jid, sender, label, senderName = '', forcedId = 0) {
  const id = forcedId || ++taskCounter;
  if (id > taskCounter) taskCounter = id;
  const task = { id, label, jid, sender, senderName: String(senderName || '').trim() || sender, source: 'Link', phase: 'queued', file: label, progress: 'Queued', speed: '—', controller: new AbortController(), cancelled: false };
  const key = `${jid}:${sender}:${Date.now()}:${Math.random()}`;
  activeTasks.set(key, task);
  return { key, task };
}
function cancelTask(key, task) {
  task.cancelled = true;
  try { task.controller?.abort(); } catch {}
  try { task.process?.kill('SIGTERM'); } catch {}
  // A task that has not started yet is simply removed from the queue.
  if (task.phase === 'queued') endTask(key, task);
}
function extractUrls(text) {
  return [...String(text || '').matchAll(/https?:\/\/[^\s<>"']+/gi)]
    .map(m => m[0].replace(/[),.!?]+$/, ''));
}
function safeName(name, addPrefix = true) {
  let n = path.basename(String(name || 'download')).replace(/[<>:"/\\|?*\x00-\x1F]/g, '_').trim();
  if (!n || n === '.' || n === '..') n = 'download';
  return (addPrefix ? (CFG.prefix + ' ' + n) : n).slice(0, 180);
}
function filenameFromResponse(headers, url) {
  const disposition = String(headers['content-disposition'] || '');
  let match = disposition.match(/filename\*\s*=\s*UTF-8''([^;]+)/i);
  if (match) {
    try { return decodeURIComponent(match[1].trim().replace(/^"|"$/g, '')); } catch {}
  }
  match = disposition.match(/filename\s*=\s*(?:"([^"]*)"|([^;]*))/i);
  if (match) return (match[1] || match[2] || '').trim();
  const last = url.pathname.split('/').pop() || 'download';
  try { return decodeURIComponent(last); } catch { return last; }
}
function mimeTypeFor(filename, contentType) {
  const ext = path.extname(filename).toLowerCase();
  const known = {
    '.mp4': 'video/mp4', '.m4v': 'video/x-m4v', '.mkv': 'video/x-matroska',
    '.avi': 'video/x-msvideo', '.mov': 'video/quicktime', '.webm': 'video/webm',
    '.mp3': 'audio/mpeg', '.m4a': 'audio/mp4', '.aac': 'audio/aac', '.wav': 'audio/wav',
    '.flac': 'audio/flac', '.ogg': 'audio/ogg', '.pdf': 'application/pdf',
    '.zip': 'application/zip', '.rar': 'application/vnd.rar', '.7z': 'application/x-7z-compressed',
    '.tar': 'application/x-tar', '.gz': 'application/gzip', '.doc': 'application/msword',
    '.docx': 'application/vnd.openxmlformats-officedocument.wordprocessingml.document',
    '.xls': 'application/vnd.ms-excel', '.xlsx': 'application/vnd.openxmlformats-officedocument.spreadsheetml.sheet',
    '.ppt': 'application/vnd.ms-powerpoint', '.pptx': 'application/vnd.openxmlformats-officedocument.presentationml.presentation',
    '.txt': 'text/plain', '.csv': 'text/csv', '.jpg': 'image/jpeg', '.jpeg': 'image/jpeg',
    '.png': 'image/png', '.gif': 'image/gif', '.webp': 'image/webp'
  };
  if (known[ext]) return known[ext];
  const headerType = String(contentType || '').split(';')[0].trim().toLowerCase();
  return /^[a-z0-9!#$&^_.+-]+\/[a-z0-9!#$&^_.+-]+$/.test(headerType) ? headerType : 'application/octet-stream';
}
function privateIPv4(ip) {
  const p = ip.split('.').map(Number);
  return p.length !== 4 || p.some(x => !Number.isInteger(x) || x < 0 || x > 255) ||
    p[0] === 10 || p[0] === 127 || p[0] === 0 || p[0] >= 224 ||
    (p[0] === 169 && p[1] === 254) || (p[0] === 172 && p[1] >= 16 && p[1] <= 31) ||
    (p[0] === 192 && p[1] === 168);
}
function privateIPv6(ip) {
  const x = ip.toLowerCase();
  return x === '::1' || x === '::' || x.startsWith('fc') || x.startsWith('fd') || x.startsWith('fe80:');
}
async function validatePublicUrl(raw) {
  const u = new URL(raw);
  if (!['http:', 'https:'].includes(u.protocol)) throw new Error('Only HTTP/HTTPS links are supported.');
  if (u.username || u.password) throw new Error('Links with embedded credentials are not supported.');
  const host = u.hostname.replace(/^\[|\]$/g, '');
  if (host === 'localhost' || host.endsWith('.localhost') || host.endsWith('.local')) throw new Error('Private/local links are blocked.');
  const records = await dns.lookup(host, { all: true });
  if (!records.length || records.some(r => r.family === 4 ? privateIPv4(r.address) : privateIPv6(r.address)))
    throw new Error('Private/local network addresses are blocked.');
  return u;
}
function requestStream(url, redirects = 0, extraHeaders = {}, signal = null) {
  return new Promise(async (resolve, reject) => {
    try {
      const u = await validatePublicUrl(url);
      const client = u.protocol === 'https:' ? https : http;
      const headers = { 'User-Agent': 'MPM-Downloader/1.0', ...extraHeaders };
      const req = client.get(u, { timeout: 30000, headers }, res => {
        if ([301,302,303,307,308].includes(res.statusCode)) {
          res.resume();
          if (redirects >= 5 || !res.headers.location) return reject(new Error('Too many redirects.'));
          const nextUrl = new URL(res.headers.location, u);
          const nextHeaders = { ...extraHeaders };
          if (nextUrl.hostname !== u.hostname) delete nextHeaders.Cookie;
          return resolve(requestStream(nextUrl.toString(), redirects + 1, nextHeaders, signal));
        }
        if (res.statusCode < 200 || res.statusCode >= 300) {
          res.resume(); return reject(new Error('Server returned HTTP ' + res.statusCode));
        }
        const name = filenameFromResponse(res.headers, u);
        resolve({ res, url: u, length: Number(res.headers['content-length']) || 0,
          name, mimetype: mimeTypeFor(name, res.headers['content-type']) });
      });
      req.on('timeout', () => req.destroy(new Error('Connection timed out.')));
      if (signal) { if (signal.aborted) req.destroy(new Error('Task cancelled.')); else signal.addEventListener('abort', () => req.destroy(new Error('Task cancelled.')), { once: true }); }
      req.on('error', reject);
    } catch (e) { reject(e); }
  });
}
// ---- Friendly errors + retry --------------------------------------------------------------------------
// Turns raw network/HTTP errors into a short, clear message for the WhatsApp user.
function friendlyError(e) {
  const raw = String((e && e.message) || e || 'Unknown error').trim();
  const m = raw + ' ' + String((e && e.code) || '');
  const http = raw.match(/HTTP (\d{3})/i);
  if (http) {
    const c = Number(http[1]);
    if (c === 404 || c === 410) return '🔗 Broken link: the file was not found or has been removed (HTTP ' + c + '). Check the link and try again.';
    if (c === 401 || c === 403) return '🔒 Access denied (HTTP ' + c + '). The link may be private, expired, need a login, or be blocked from this server\'s country (geo-block).';
    if (c === 451) return '🌍 This content is blocked in this region (HTTP 451).';
    if (c === 429) return '⏳ The website is rate-limiting requests (HTTP 429). Wait a few minutes and try again.';
    if (c >= 500) return '🛠️ The file server is having problems (HTTP ' + c + '). Try again later.';
    return '❌ The server rejected the request (HTTP ' + c + ').';
  }
  if (/Invalid URL/i.test(m)) return '🔗 That does not look like a valid link.';
  if (/ENOTFOUND/i.test(m)) return '🌐 That website could not be found. Check the link for typos.';
  if (/EAI_AGAIN/i.test(m)) return '🌐 DNS lookup failed (network problem). Try again in a moment.';
  if (/timed? ?out|ETIMEDOUT|ESOCKETTIMEDOUT/i.test(m)) return '⌛ The server took too long to respond (timeout). Try again later.';
  if (/ECONNREFUSED/i.test(m)) return '🚫 The server refused the connection.';
  if (/ECONNRESET|EPIPE|socket hang up|closed before|ENETUNREACH|ENETDOWN|EHOSTUNREACH/i.test(m)) return '📡 The connection dropped during the download. Please try again.';
  if (/ENOSPC/i.test(m)) return '💾 The bot server is out of disk space. Please tell the admin.';
  if (/CERT|SSL|self[- ]signed|unable to verify/i.test(m)) return '🔐 The website has an invalid security certificate.';
  return raw.length > 300 ? raw.slice(0, 297) + '…' : raw;
}
// Errors worth retrying (temporary network problems). 404/403/DNS errors are NOT retried.
function isTransientNetError(e) {
  const m = String((e && e.message) || e || '') + ' ' + String((e && e.code) || '');
  if (/cancel/i.test(m)) return false;
  return /timed? ?out|ETIMEDOUT|ECONNRESET|ECONNREFUSED|EPIPE|socket hang up|closed before|ENETUNREACH|ENETDOWN|EHOSTUNREACH|EAI_AGAIN|HTTP (429|500|502|503|504)/i.test(m);
}
// Marks an error as coming from the download phase (before upload/quota), so it is safe to retry.
function tagDl(e) { if (e && typeof e === 'object') e.dlStage = true; return e; }
// Download engine (multi-part + resume + disk check + site resolvers) lives in fetcher.cjs.
fetcher.init({ validatePublicUrl, filenameFromResponse, mimeTypeFor });
const DISK_RESERVE = Number.isFinite(CFG.reserveDiskBytes) ? CFG.reserveDiskBytes : 1024 ** 3;
const DL_CONNECTIONS = Math.max(1, Math.min(16, Number(CFG.connections) || 4));
const DL_MULTIPART_MIN = Number(CFG.multipartMinBytes) > 0 ? Number(CFG.multipartMinBytes) : 8 * 1024 * 1024;
async function downloadOneWithRetry(sock, jid, sender, url, admin, options = {}) {
  const maxTries = 3;
  for (let attempt = 1; ; attempt++) {
    try { return await downloadOne(sock, jid, sender, url, admin, options); }
    catch (e) {
      const cancelled = options.task?.cancelled || options.signal?.aborted || /cancel/i.test(String((e && e.message) || ''));
      if (e && typeof e === 'object') e.attempts = attempt;
      if (cancelled || !e || !e.dlStage || !isTransientNetError(e) || attempt >= maxTries) throw e;
      const waitS = 4 * attempt;
      console.warn('[retry] download attempt ' + attempt + '/' + maxTries + ' failed: ' + ((e && e.message) || e));
      try { await sock.sendMessage(jid, { text: friendlyError(e).replace(/\s*Please try again\.?$/i, '') + '\n🔁 Retrying in ' + waitS + 's (attempt ' + (attempt + 1) + '/' + maxTries + ')…' }); } catch { /* ignore */ }
      await new Promise(r => setTimeout(r, waitS * 1000));
      if (options.task?.cancelled || options.signal?.aborted) throw new Error('Task cancelled by user.');
    }
  }
}

// ---- Per-user command cooldown (anti-flood / anti-ban) ---------------------------------------------
// Admins and the owner are never limited. Set "cooldownSeconds" in config.json (0 turns it off).
const cmdTimes = new Map();   // sender -> { last, warned, strikes }
const COOLDOWN_EXEMPT = /^[.,](cancel|cancelall|task|tasks|restart|reboot)\b/i;
setInterval(() => { const cut = Date.now() - 10 * 60 * 1000; for (const [k, v] of cmdTimes) if (v.last < cut) cmdTimes.delete(k); }, 5 * 60 * 1000).unref();
// Returns true when the command must be ignored (the user is sending too fast).
async function throttleCommand(sock, msg) {
  try {
    const cd = Number(CFG.cooldownSeconds);
    if (!(cd > 0)) return false;
    const text = String(msg.message?.conversation || msg.message?.extendedTextMessage?.text || '').trim();
    if (!text || COOLDOWN_EXEMPT.test(text)) return false;
    const jid = msg.key.remoteJid;
    if (!jid || jid === 'status@broadcast') return false;
    const fromMe = Boolean(msg.key.fromMe);
    const linkedOwner = jidNumber(sock.user?.id || '') || owner;
    const senderLid = jidNumber(sock.user?.lid || '');
    const rawSender = fromMe ? (linkedOwner || owner) : jidNumber(jid.endsWith('@g.us') ? (msg.key.participant || '') : jid);
    const sender = (senderLid && rawSender === senderLid && owner) ? owner : rawSender;
    if (!sender || isAdmin(sender)) return false;
    const now = Date.now();
    const st = cmdTimes.get(sender) || { last: 0, warned: false, strikes: 0 };
    const wait = st.last + cd * 1000 - now;
    if (wait > 0) {
      st.strikes++;
      if (st.strikes >= 8) {            // keeps hammering: pause that user for a minute
        st.last = now + 60000 - cd * 1000; st.strikes = 0; st.warned = true; cmdTimes.set(sender, st);
        await sock.sendMessage(jid, { text: '🚫 [MPM] Too many commands too fast. You are paused for 60 seconds.' }).catch(() => {});
      } else if (!st.warned) {            // warn once, then stay silent so the bot never floods back
        st.warned = true; cmdTimes.set(sender, st);
        await sock.sendMessage(jid, { text: '⏳ [MPM] Slow down a little. Please wait ' + Math.ceil(wait / 1000) + 's before your next command.' }).catch(() => {});
      } else cmdTimes.set(sender, st);
      return true;
    }
    st.last = now; st.warned = false; st.strikes = 0; cmdTimes.set(sender, st);
    return false;
  } catch (e) { console.error('[throttle]', e && e.message || e); return false; }
}
// Real free-disk check lives in fetcher.cjs (fs.statfs); downloads refuse to start when the disk is too full.
async function createProgressReporter(sock, jid, initialText) {
  // Edit one WhatsApp message throughout the download and upload lifecycle.
  const sent = await sock.sendMessage(jid, { text: initialText });
  const key = sent?.key;
  let lastText = initialText;
  return {
    async update(nextText) {
      if (!key || nextText === lastText) return;
      try {
        await sock.sendMessage(jid, { text: nextText, edit: key });
        lastText = nextText;
      } catch (err) {
        // Avoid sending a new message on every progress tick if editing fails.
        console.warn('Progress message edit failed:', err?.message || err);
      }
    }
  };
}

async function downloadOne(sock, jid, sender, url, admin, options = {}) {
  const u = usage(sender);
  const max = Math.min(admin ? CFG.adminMaxFileBytes : (u.maxFileBytes || CFG.userMaxFileBytes), hardMaxBytes());
  const task = options.task || [...activeTasks.values()].find(t => t.jid === jid && t.sender === sender && t.phase !== 'queued');
  if (task?.cancelled || options.signal?.aborted) throw new Error('Task cancelled by user.');
  if (task) { task.phase = 'downloading'; task.file = 'Preparing download'; task.progress = '0%'; task.speed = '—'; }
  const assignedQuota = admin ? null : quotaInfo(u);
  if (!admin && assignedQuota?.enabled && assignedQuota.expired) throw new Error('Your assigned limit is expired or fully used. Ask an admin to renew it.');
  if (!admin && CFG.dailyLimitBytes > 0 && u.used >= CFG.dailyLimitBytes) throw new Error('Daily quota used. ' + bytes(CFG.dailyLimitBytes) + ' limit resets tomorrow.');
  const progress = options.progressReporter || await createProgressReporter(sock, jid, options.progressInitialText || '⏬ [MPM] Preparing download…');

  // Google Drive / Mediafire / Dropbox / Pixeldrain / OneDrive / GitHub links -> direct file link.
  const resolved = await fetcher.resolveLink(url, { signal: options.signal }).catch(e => { throw tagDl(e); });
  const reqHeaders = { ...(resolved.headers || {}), ...(options.headers || {}) };

  let remaining = max;
  if (!admin && CFG.dailyLimitBytes > 0) remaining = Math.min(remaining, CFG.dailyLimitBytes - u.used);
  if (!admin && assignedQuota?.enabled) remaining = Math.min(remaining, assignedQuota.remainingBytes);

  // Resumable partial file: same link -> same file name, so a retry (or a restart) continues where it stopped.
  let outPath = fetcher.partPathFor(TEMP_DIR, resolved.url);
  if (fetcher.activeParts.has(outPath)) outPath = path.join(TEMP_DIR, Date.now() + '-' + Math.random().toString(16).slice(2) + '.part');
  fetcher.activeParts.add(outPath);

  let name = '', mimetype = '', finalName = '', length = 0;
  let lastProgress = 0, lastReceived = 0, windowStart = Date.now();
  const dlStart = Date.now();
  const cardTask = task || { sender, senderName: sender, source: 'Link' };
  let keepPartial = false, downloaded = null;
  const runFetch = (connections) => fetcher.download({
    url: resolved.url, headers: reqHeaders, signal: options.signal, outPath,
    connections, minMultipart: DL_MULTIPART_MIN, reserveBytes: DISK_RESERVE,
    onMeta: (m) => {
      length = m.length || 0;
      name = options.fileName || resolved.fileName || m.name;
      mimetype = options.mimetype || m.mimetype;
      if (length && length > hardMaxBytes()) throw new Error('File too large: ' + (options.fileName || m.name || 'file') + ' is ' + bytes(length) + '. Maximum allowed size is ' + hardMaxText() + ', so it was not downloaded.');
      if (length && length > max) throw new Error('File is ' + bytes(length) + '. Your maximum is ' + bytes(max) + '.');
      if (length && length > remaining) throw new Error('File is ' + bytes(length) + ' but your remaining limit is ' + bytes(Math.max(0, remaining)) + '.');
      const baseName = safeName(name, options.addPrefix !== false);
      const customPrefix = String(options.customPrefix || '').trim();
      finalName = customPrefix ? safeName(customPrefix + ' ' + name, false) : baseName;
      if (task) task.file = finalName;
      progress.update(mpmCard(cardTask, { phase: 'download', pct: 0, done: 0, total: length, speed: 0, elapsed: 0, file: options.batchIndex && options.batchTotal ? `${options.batchIndex}/${options.batchTotal} • ${cardShort(finalName)}` : '' })).catch(() => {});
    },
    onChunk: (received) => {
      if (received > remaining) throw new Error('Download exceeded your remaining limit (' + bytes(Math.max(0, remaining)) + ').');
      if (received > max) throw new Error(max >= hardMaxBytes() ? 'File too large: it is bigger than the maximum allowed size of ' + hardMaxText() + '.' : 'File exceeded the maximum size of ' + bytes(max) + '.');
      const now = Date.now();
      if (now - lastProgress >= (CFG.progressIntervalSeconds || 5) * 1000) {
        const elapsed = Math.max(1, now - windowStart) / 1000;
        const speed = Math.max(0, received - lastReceived) / elapsed;
        lastProgress = now; windowStart = now; lastReceived = received;
        const pct = length ? Math.min(99, Math.floor(received / length * 100)) + '%' : bytes(received);
        if (task) { task.phase = 'downloading'; task.progress = pct; task.speed = bytes(speed) + '/s'; }
        progress.update(mpmCard(cardTask, {
          phase: 'download', pct: length ? Math.min(99.99, received / length * 100) : NaN, done: received, total: length,
          speed, elapsed: (now - dlStart) / 1000, eta: length && speed > 0 ? (length - received) / speed : NaN,
          file: options.batchIndex && options.batchTotal ? `${options.batchIndex}/${options.batchTotal} • ${cardShort(finalName)}` : ''
        })).catch(() => {});
      }
    }
  });
  try {
    try { downloaded = await runFetch(DL_CONNECTIONS); }
    catch (e) {
      // Some hosts refuse several connections at once (HTTP 403/429): start over with a single connection.
      if (DL_CONNECTIONS > 1 && (e.statusCode === 403 || e.statusCode === 429) && !task?.cancelled) {
        console.warn('[download] host refused parallel connections (HTTP ' + e.statusCode + '); retrying with 1 connection');
        fetcher.discardPartial(outPath); lastReceived = 0;
        downloaded = await runFetch(1);
      } else throw e;
    }
    if (task?.cancelled) throw new Error('Task cancelled by user.');
    const received = downloaded.size;
    // Confirm the completed download is present and readable before starting upload.
    await fs.promises.access(outPath, fs.constants.R_OK);
    const savedFile = await fs.promises.stat(outPath);
    if (!savedFile.isFile() || savedFile.size !== received) {
      throw new Error('Downloaded file is missing or incomplete. Please try the link again.');
    }
    await waitUploadGap(task);
    if (task?.cancelled) throw new Error('Task cancelled by user.');
    if (task) { task.phase = 'uploading'; task.progress = '0%'; task.speed = '—'; }
    // Baileys expects a file path (string) in document.url and gives no per-byte upload progress,
    // so the card shows the file, its size and the elapsed time while uploading.
    const batchFile = options.batchIndex && options.batchTotal ? `${options.batchIndex}/${options.batchTotal} • ${cardShort(finalName)}` : '';
    if (received > UPLOAD_MAX_BYTES) {
      await sendLargeFile(sock, options.uploadJid || jid, outPath, finalName, progress, cardTask, task, batchFile, { jid, sender });
    } else try {
      await uploadWithCard(progress, cardTask, { size: received, file: batchFile }, () => sock.sendMessage(options.uploadJid || jid, {
        document: { url: outPath },
        fileName: finalName,
        mimetype
      }));
    } finally {
      markUploadDone();
    }
    // The user's limit is charged ONLY now: the upload succeeded, and only for the bytes that were really downloaded.
    if (!admin) {
      const uNow = usage(sender);
      uNow.used = (uNow.used || 0) + received; uNow.quotaUsedBytes = (uNow.quotaUsedBytes || 0) + received; uNow.count = (uNow.count || 0) + 1;
      db.lastUse[sender] = Date.now();
    }
    recordStats(sender, received); saveDB();
    if (task) { task.phase = 'completed'; task.progress = '100%'; }
    // Do not announce completion for each individual file. The queue sends one summary after all files finish.
    return { sent: true, fileName: finalName, size: received };
  } catch (e) {
    // A dropped connection keeps the partial file so the next attempt resumes; anything else cleans up.
    keepPartial = !task?.cancelled && !downloaded && fetcher.isTransient(e);
    throw downloaded ? e : tagDl(e);   // only download-stage errors are retried (never re-send after an upload error)
  } finally {
    fetcher.activeParts.delete(outPath);
    if (!keepPartial) fetcher.discardPartial(outPath);
  }
}
const GOFILE_USER_AGENT = 'Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/126.0.0.0 Safari/537.36';
const GOFILE_LANGUAGE = 'en-US';
// Gofile's website token uses a "salt" that Gofile changes from time to time. It is refreshed automatically
// (best effort, from Gofile's own web script) when the API starts refusing requests; GOFILE_WT_SALT in .env overrides it.
let gofileSalt = process.env.GOFILE_WT_SALT || '12af056dacea0b';
let gofileStaticWt = '';
let gofileSaltRefreshedAt = 0;
const GOFILE_GUEST_FILE = path.join(DATA_DIR, 'gofile_guest.json');

function gofileContentId(raw) {
  try {
    const u = new URL(raw);
    if (!/(^|\.)gofile\.io$/i.test(u.hostname)) return null;
    const m = u.pathname.match(/^\/(?:d|download)\/([A-Za-z0-9-]+)/i);
    return m ? m[1] : null;
  } catch { return null; }
}
function gofileWebsiteToken(accountToken, windowOffset = 0) {
  const window = Math.floor(Date.now() / 1000 / 14400) + windowOffset;
  const raw = `${GOFILE_USER_AGENT}::${GOFILE_LANGUAGE}::${accountToken}::${window}::${gofileSalt}`;
  return crypto.createHash('sha256').update(raw, 'utf8').digest('hex');
}
function gofileJsonRequest(method, url, headers = {}, body = null) {
  return new Promise((resolve, reject) => {
    const u = new URL(url);
    const payload = body ? Buffer.from(JSON.stringify(body)) : null;
    const req = https.request(u, {
      method, timeout: 45000,
      headers: {
        'User-Agent': GOFILE_USER_AGENT, 'X-BL': GOFILE_LANGUAGE,
        'Accept': '*/*', 'Origin': 'https://gofile.io', 'Referer': 'https://gofile.io/',
        ...(payload ? { 'Content-Type': 'application/json', 'Content-Length': payload.length } : {}),
        ...headers
      }
    }, res => {
      let data = '';
      res.setEncoding('utf8');
      res.on('data', chunk => data += chunk);
      res.on('end', () => {
        let parsed;
        try { parsed = JSON.parse(data); } catch { return reject(new Error('Gofile returned an invalid API response.')); }
        if (parsed && typeof parsed === 'object') parsed.httpStatus = res.statusCode;
        if ((res.statusCode < 200 || res.statusCode >= 300) && !(parsed && parsed.status)) return reject(new Error('Gofile API HTTP ' + res.statusCode));
        resolve(parsed);
      });
    });
    req.on('timeout', () => req.destroy(new Error('Gofile API timed out.')));
    req.on('error', reject);
    if (payload) req.write(payload);
    req.end();
  });
}
async function getGofileGuestToken(force = false) {
  if (!force) {
    try {
      const saved = JSON.parse(fs.readFileSync(GOFILE_GUEST_FILE, 'utf8'));
      if (saved.token) return saved.token;
    } catch {}
  }
  const result = await gofileJsonRequest('POST', 'https://api.gofile.io/accounts');
  if (result.status !== 'ok' || !result.data?.token) throw new Error('Could not create a temporary Gofile guest session.');
  fs.writeFileSync(GOFILE_GUEST_FILE, JSON.stringify({ token: result.data.token, savedAt: Date.now() }, null, 2));
  return result.data.token;
}
// Best effort: read Gofile's web script for the current website-token salt. Returns true when something changed.
async function refreshGofileSalt() {
  if (Date.now() - gofileSaltRefreshedAt < 10 * 60 * 1000) return false;
  gofileSaltRefreshedAt = Date.now();
  try {
    const page = await fetcher.getText('https://gofile.io/dist/js/global.js', { headers: { 'User-Agent': GOFILE_USER_AGENT } });
    const js = page.body || '';
    let changed = false;
    const wt = /appdata\.wt\s*=\s*["']([^"']+)["']/.exec(js);
    if (wt && wt[1] !== gofileStaticWt) { gofileStaticWt = wt[1]; changed = true; }
    for (const m of js.matchAll(/\$\{[^}`]*\}::([A-Za-z0-9]{6,32})`/g)) { if (m[1] !== gofileSalt) { gofileSalt = m[1]; changed = true; } break; }
    if (changed) console.log('[gofile] refreshed website-token data from gofile.io');
    return changed;
  } catch (e) { console.warn('[gofile] could not refresh salt:', e.message); return false; }
}
// tokenRef = { token }. Handles rate limits (waits), expired guest tokens (creates a new one) and token-window / salt changes.
async function getGofileContent(contentId, tokenRef, page = 1) {
  const params = new URLSearchParams({ contentFilter: '', page: String(page), pageSize: '1000', sortField: 'createTime', sortDirection: '-1' });
  const url = `https://api.gofile.io/contents/${encodeURIComponent(contentId)}?${params}`;
  const plan = [[0, false], [-1, false], [1, false]];
  let saltTried = false, tokenTried = false, rateWaits = 0, i = 0;
  while (i < plan.length) {
    const [offset, useStatic] = plan[i];
    const headers = { Authorization: 'Bearer ' + tokenRef.token, 'X-Website-Token': useStatic ? gofileStaticWt : gofileWebsiteToken(tokenRef.token, offset) };
    const result = await gofileJsonRequest('GET', url, headers);
    if (result.status === 'ok') return result;
    const st = String(result.status || '');
    if (st === 'error-rateLimit' || result.httpStatus === 429) {
      if (rateWaits >= 3) throw new Error('Gofile free access rate limit reached. Please wait a few minutes and try again.');
      await new Promise(r => setTimeout(r, 5000 * 2 ** rateWaits++)); continue;
    }
    if (st === 'error-passwordRequired' || result.data?.passwordStatus) throw new Error('This Gofile folder is password protected; password support is not enabled in this bot.');
    if (st === 'error-notFound') throw new Error('This Gofile folder was not found (deleted or expired).');
    if (/^error-(auth|token|unauthorized)/.test(st) || result.httpStatus === 401) {
      if (tokenTried) throw new Error('Gofile rejected the guest session (' + st + ').');
      tokenTried = true; tokenRef.token = await getGofileGuestToken(true); i = 0; continue;   // expired guest token -> new one
    }
    if (st === 'error-notPremium' || /website|token|premium/i.test(st) || result.httpStatus === 403) {
      i++;                                                   // try the neighbouring token windows first
      if (i >= plan.length && !saltTried) {                  // then ask gofile.io for a new salt
        saltTried = true;
        if (await refreshGofileSalt()) { plan.push([0, false], [-1, false]); if (gofileStaticWt) plan.push([0, true]); }
      }
      continue;
    }
    throw new Error('Gofile could not open this folder (' + (st || 'unknown error') + ').');
  }
  throw new Error('Gofile could not open this folder (website token refused). Gofile may have changed its protection; set GOFILE_WT_SALT in .env or try again later.');
}
async function listGofileFiles(contentId, tokenRef, files = [], visited = new Set(), depth = 0) {
  if (depth > 12) throw new Error('Gofile folder nesting is too deep.');
  if (visited.has(contentId)) return files;
  visited.add(contentId);
  let page = 1, totalPages = 1, rootData = null;
  do {
    const result = await getGofileContent(contentId, tokenRef, page);
    const data = result.data || {};
    if (!rootData) rootData = data;
    if (data.type === 'file') {
      if (!data.link) throw new Error('Gofile did not provide a download link for ' + (data.name || contentId));
      files.push({ id: data.id || contentId, name: data.name || 'download', link: data.link, size: Number(data.size) || 0, mimetype: data.mimetype || 'application/octet-stream' });
      return files;
    }
    const children = data.children && typeof data.children === 'object' ? Object.values(data.children) : [];
    for (const child of children) {
      if (child.type === 'folder') await listGofileFiles(child.id, tokenRef, files, visited, depth + 1);
      else if (child.type === 'file' && child.link) files.push({ id: child.id, name: child.name || 'download', link: child.link, size: Number(child.size) || 0, mimetype: child.mimetype || 'application/octet-stream' });
    }
    totalPages = Number(result.metadata?.totalPages) || 1;
    page++;
  } while (page <= totalPages && page <= 100);
  return files;
}
async function processGofileFolder(sock, jid, sender, url, admin, customPrefix = '', defaultPrefix = '', uploadJid = jid, task = null) {
  const contentId = gofileContentId(url);
  if (!contentId) throw new Error('Invalid Gofile folder link.');
  if (task) task.source = 'Gofile';
  const folderProgress = await createProgressReporter(sock, jid, '📂 [MPM] Reading Gofile folder…');
  const tokenRef = { token: await getGofileGuestToken() };
  const files = await listGofileFiles(contentId, tokenRef);
  const token = tokenRef.token;
  await folderProgress.update(`📂 [MPM] Found ${files.length} file(s). Preparing…`);
  if (!files.length) throw new Error('No downloadable files found in this Gofile folder.');
  if (files.length > 500) throw new Error('This folder has ' + files.length + ' files. The current safety limit is 500 files per folder.');
  // Sort filenames naturally so multipart archives are processed as 1, 2, ... 9, 10 (not 1, 10, 2).
  const naturalNameOrder = new Intl.Collator(undefined, { numeric: true, sensitivity: 'base' });
  files.sort((a, b) => naturalNameOrder.compare(a.name, b.name));
  const progress = folderProgress;
  await progress.update(`⏬ [MPM] Downloading 1/${files.length}`);
  let sent = 0;
  const doneIds = new Set(task?.job?.doneIds || []);
  for (let index = 0; index < files.length; index++) {
    if (task?.cancelled) break;
    const file = files[index];
    if (doneIds.has(file.id)) { sent++; continue; }   // already sent before a bot restart
    await progress.update(`⏬ [MPM] Downloading ${index + 1}/${files.length}\nFile: ${file.name}`);
    try {
      await downloadOne(sock, jid, sender, file.link, admin, {
        uploadJid, task, signal: task?.controller?.signal, fileName: file.name, mimetype: file.mimetype, addPrefix: false, customPrefix: customPrefix || (defaultPrefix ? defaultPrefix : ''),
        progressReporter: progress, batchIndex: index + 1, batchTotal: files.length,
        headers: { Cookie: 'accountToken=' + token, 'User-Agent': GOFILE_USER_AGENT, Referer: 'https://gofile.io/' }
      });
      sent++;
      if (task?.job) { (task.job.doneIds ||= []).push(file.id); persistJobs(); }
    } catch (e) {
      if (task?.cancelled) break;
      await sock.sendMessage(jid, { text: `❌ [MPM] Gofile file failed: ${file.name}\n${e.message || 'Unknown error'}` });
    }
  }
  if (!task?.cancelled && sent === files.length) await sock.sendMessage(jid, { text: '✅ MPM DONE ✓' });
  return { sent, total: files.length };
}

async function extractAndUploadZip(sock, jid, sender, url, admin, prefix, task) {
  let uploadedCount = 0, zipCharged = false, zipReceived = 0;
  const chargeZip = () => {   // charge only the downloaded archive size, and only once something was really uploaded
    if (admin || zipCharged || uploadedCount < 1 || !(zipReceived > 0)) return;
    zipCharged = true;
    const uz = usage(sender);
    uz.used = (uz.used || 0) + zipReceived; uz.quotaUsedBytes = (uz.quotaUsedBytes || 0) + zipReceived; uz.count = (uz.count || 0) + 1;
    recordStats(sender, zipReceived); saveDB();
  };
  const work = path.join(TEMP_DIR, 'zip-' + crypto.randomBytes(8).toString('hex'));
  const archive = path.join(work, 'source.zip'); const extracted = path.join(work, 'extracted');
  await fs.promises.mkdir(extracted, { recursive: true });
  try {
    task.phase = 'downloading'; task.file = 'ZIP archive'; task.progress = 'Downloading';
    const max = admin ? CFG.adminMaxFileBytes : CFG.userMaxFileBytes;
    const zipUser = usage(sender);
    const zipQuota = admin ? null : quotaInfo(zipUser);
    if (!admin && zipQuota?.enabled && zipQuota.expired) throw new Error('Your assigned limit is expired or fully used. Ask an admin to renew it.');
    const zipRemaining = !admin && zipQuota?.enabled ? Math.min(max, zipQuota.remainingBytes) : max;
    const resolvedZip = await fetcher.resolveLink(url, { signal: task.controller?.signal });
    const zipDl = await fetcher.download({
      url: resolvedZip.url, headers: resolvedZip.headers || {}, signal: task.controller?.signal, outPath: archive,
      connections: DL_CONNECTIONS, minMultipart: DL_MULTIPART_MIN, reserveBytes: DISK_RESERVE,
      onMeta: async (m) => {
        if (m.length && m.length > zipRemaining) throw new Error('ZIP exceeds your remaining limit (' + bytes(zipRemaining) + ').');
        if (m.length) await fetcher.ensureDisk(TEMP_DIR, m.length, DISK_RESERVE);   // room for the extracted files too
      },
      onChunk: (n) => { if (n > zipRemaining) throw new Error('ZIP exceeded your remaining limit (' + bytes(zipRemaining) + ').'); }
    });
    zipReceived = zipDl.size;
    // Validate archive paths before extraction to prevent ZIP Slip traversal.
    const entries = await zipListEntries(archive);
    if (!entries.length || entries.length > 1000) throw new Error('ZIP is empty or contains too many entries (limit 1000).');
    for (const entry of entries) {
      const normalized = entry.replace(/\\/g, '/');
      if (normalized.startsWith('/') || /^[a-zA-Z]:/.test(normalized) || normalized.split('/').includes('..')) throw new Error('Unsafe ZIP entry path blocked.');
    }
    await zipExtractAll(archive, extracted);
    const files = [];
    async function walk(dir) { for (const ent of await fs.promises.readdir(dir, { withFileTypes: true })) { const full = path.join(dir, ent.name); if (ent.isSymbolicLink()) continue; if (ent.isDirectory()) await walk(full); else if (ent.isFile()) files.push(full); } }
    await walk(extracted);
    files.sort((a,b) => new Intl.Collator(undefined,{numeric:true,sensitivity:'base'}).compare(path.relative(extracted,a),path.relative(extracted,b)));
    if (!files.length) throw new Error('ZIP contains no regular files.');
    const progress = await createProgressReporter(sock, jid, `📦 [MPM] Extracted ${files.length} file(s). Uploading…`);
    task.phase = 'uploading';
    for (let i=0;i<files.length;i++) {
      if (task.cancelled) break;
      const file = files[i]; const rel = path.relative(extracted,file).split(path.sep).join('/');
      const prefixed = safeName(prefix + ' ' + rel.replace(/[\/]+/g, '__'), false);
      task.file = rel; task.progress = `${i+1}/${files.length}`;
      const zipFileSize = (await fs.promises.stat(file)).size;
      if (zipFileSize > hardMaxBytes()) {
        await sock.sendMessage(jid, { text: `❌ [MPM] File too large: ${rel} (${bytes(zipFileSize)}).\nMaximum allowed size is ${hardMaxText()}. This file was skipped.` });
        continue;
      }
      if (zipFileSize > UPLOAD_MAX_BYTES) {
        try { await sendLargeFile(sock, jid, file, prefixed, progress, task, task, `${i+1}/${files.length}`, { jid, sender }); uploadedCount++; }
        catch (e) { await sock.sendMessage(jid, { text: `❌ [MPM] Could not send ${rel}: ${e.message || e}` }); }
        continue;
      }
      await waitUploadGap(task);
      if (task.cancelled) break;
      try {
        await uploadWithCard(progress, task, { size: zipFileSize, file: `${i+1}/${files.length} • ${cardShort(rel)}` }, () =>
          sock.sendMessage(jid, { document: { url: file }, fileName: prefixed, mimetype: mimeTypeFor(file), caption: `Path: ${path.dirname(rel) === '.' ? '' : path.dirname(rel)}` }));
        uploadedCount++;
      } finally { markUploadDone(); }
    }
    chargeZip();
    await sock.sendMessage(jid, { text: '✅ MPM DONE ✓' });
    return files.length;
  } finally { try { chargeZip(); } catch {} await fs.promises.rm(work, { recursive:true, force:true }); }
}


// ZIP helpers that need NO extra software: `unzip` (Linux/macOS) -> `tar` (built into Windows 10+) -> adm-zip (npm package).
const ZIP_EXEC_OPTS = { maxBuffer: 16 * 1024 * 1024, windowsHide: true };
async function zipListEntries(archive) {
  let lastErr = null;
  const attempts = [
    async () => (await execFileAsync('unzip', ['-Z1', archive], ZIP_EXEC_OPTS)).stdout,
    async () => (await execFileAsync('tar', ['-tf', archive], ZIP_EXEC_OPTS)).stdout
  ];
  for (const run of attempts) {
    try { const list = (await run()).split(/\r?\n/).filter(Boolean); if (list.length) return list; } catch (e) { lastErr = e; }
  }
  try { const AdmZip = require('adm-zip'); return new AdmZip(archive).getEntries().map(e => e.entryName); }
  catch (e) { throw new Error('Could not read the ZIP file: ' + (e.message || (lastErr && lastErr.message) || 'unknown error')); }
}
async function zipExtractAll(archive, dest) {
  const attempts = [
    () => execFileAsync('unzip', ['-o', archive, '-d', dest], ZIP_EXEC_OPTS),
    () => execFileAsync('tar', ['-xf', archive, '-C', dest], ZIP_EXEC_OPTS)
  ];
  for (const run of attempts) { try { await run(); return; } catch (e) { /* try the next method */ } }
  const AdmZip = require('adm-zip');
  new AdmZip(archive).extractAllTo(dest, true);
}

async function runTorrentDownload(sock, jid, sender, input, admin, task, customPrefix = '') {
  const u = usage(sender);
  const max = admin ? CFG.adminMaxFileBytes : (u.maxFileBytes || CFG.userMaxFileBytes);
  const assigned = admin ? null : quotaInfo(u);
  const initialQuotaUsed = u.quotaUsedBytes || 0;
  if (!admin && assigned?.enabled && assigned.expired) throw new Error('Your assigned limit is expired or fully used.');
  if (!admin && CFG.dailyLimitBytes > 0 && u.used >= CFG.dailyLimitBytes) throw new Error('Daily quota used.');
  const localTorrent = typeof input === 'string' && /\.torrent$/i.test(input) && fs.existsSync(input);
  if (!input || !(localTorrent || /^(magnet:\?xt=urn:btih:|https?:\/\/)/i.test(input))) throw new Error('Send a magnet link or a public .torrent URL.');
  // Fixed folder per task id: after a bot restart the restored task re-uses it and aria2 continues (--continue=true).
  const work = path.join(TEMP_DIR, 'torrent-t' + task.id);
  await fs.promises.mkdir(work, { recursive: true });
  await fetcher.ensureDisk(TEMP_DIR, 0, DISK_RESERVE);
  task.phase = 'downloading'; task.file = 'Torrent metadata'; task.progress = 'Starting'; task.source = 'Torrent';
  const progress = await createProgressReporter(sock, jid, '🧲 [MPM] Connecting to torrent peers…');
  let child;
  try {
    await new Promise((resolve, reject) => {
      const args = ['--dir', work, '--continue=true', '--seed-time=0', '--max-tries=5', '--retry-wait=5', '--summary-interval=3', '--console-log-level=notice', '--file-allocation=none', '--bt-stop-timeout=30', '--allow-overwrite=true', input];
      args.unshift('--enable-color=false');
      child = spawn('aria2c', args, { windowsHide: true, stdio: ['ignore', 'pipe', 'pipe'] });
      task.process = child;
      let stderr = '', last = 0, outBuf = '', lastDisk = 0, diskStop = '';
      const tStart = Date.now();
      const unitBytes = t => { const m = String(t || '').match(/^([\d.]+)\s*([KMGT]?)i?B?$/i); if (!m) return 0; const u = (m[2] || '').toUpperCase(); return Number(m[1]) * (u ? 1024 ** ('KMGT'.indexOf(u) + 1) : 1); };
      const etaSec = t => { const m = String(t || '').match(/^(?:(\d+)d)?(?:(\d+)h)?(?:(\d+)m)?(?:(\d+)s)?$/i); return m && t ? (+m[1]||0)*86400 + (+m[2]||0)*3600 + (+m[3]||0)*60 + (+m[4]||0) : NaN; };
      child.stderr.on('data', chunk => { stderr = (stderr + chunk.toString()).slice(-5000); });
      // aria2 prints: [#gid 12MiB/1.2GiB(1%) CN:4 SD:3 DL:2.5MiB ETA:8m12s]
      child.stdout.on('data', chunk => {
        outBuf = (outBuf + chunk.toString()).slice(-3000);
        const now = Date.now();
        if (now - lastDisk > 10000) {   // stop the torrent before the disk is completely full
          lastDisk = now;
          fetcher.freeDiskBytes(TEMP_DIR).then(free => {
            if (!diskStop && free < Math.floor(DISK_RESERVE / 2)) { diskStop = '💾 Not enough disk space on the bot server (' + fetcher.fmtBytes(free) + ' free). Torrent stopped.'; try { child.kill('SIGTERM'); } catch {} }
          }).catch(() => {});
        }
        if (now - last < 2500) return;
        const all = [...outBuf.matchAll(/\[#\w+\s+([\d.]+\w*)\/([\d.]+\w*)(?:\((\d+)%\))?(?:\s+CN:(\d+))?(?:\s+SD:\d+)?(?:\s+DL:([\d.]+\w*))?(?:\s+ETA:(\w+))?/g)];
        const m = all[all.length - 1];
        if (!m) return;
        last = now;
        const done = unitBytes(m[1]), total = unitBytes(m[2]);
        const pct = total > 0 ? Math.min(99.99, done / total * 100) : NaN;
        task.progress = (Number.isFinite(pct) ? pct.toFixed(1) + '%' : bytes(done));
        task.speed = cardSize(unitBytes(m[5])) + '/s';
        progress.update(mpmCard(task, {
          phase: 'download', pct, done, total, speed: unitBytes(m[5]), peers: m[4] !== undefined ? Number(m[4]) : null,
          elapsed: (now - tStart) / 1000, eta: etaSec(m[6])
        })).catch(()=>{});
      });
      child.once('error', err => reject(err.code === 'ENOENT' ? new Error('aria2c is not installed. Install aria2 and restart the bot.') : err));
      child.once('close', code => code === 0 ? resolve() : diskStop ? reject(new Error(diskStop)) : reject(new Error('aria2c failed (' + code + '): ' + (stderr.trim().split(/\r?\n/).slice(-2).join(' ') || 'No peers or invalid torrent.'))));
    });
    const files = [];
    async function walk(dir) {
      for (const ent of await fs.promises.readdir(dir, { withFileTypes: true })) {
        const full = path.join(dir, ent.name);
        if (ent.isDirectory()) await walk(full);
        else if (ent.isFile() && (await fs.promises.stat(full)).size > 0) files.push(full);
      }
    }
    await walk(work);
    if (!files.length) throw new Error('Torrent completed but no files were downloaded.');
    files.sort((a,b) => a.localeCompare(b, undefined, { numeric:true, sensitivity:'base' }));
    let sent = 0, tooLarge = 0;
    for (const file of files) {
      if (task.cancelled) break;
      const stat = await fs.promises.stat(file);
      if (stat.size > hardMaxBytes()) {
        tooLarge++;
        await sock.sendMessage(jid, { text: `❌ [MPM] File too large: ${path.basename(file)} (${bytes(stat.size)}).\nMaximum allowed size is ${hardMaxText()}. This file was skipped.` });
        continue;
      }
      const remainingDaily = admin || CFG.dailyLimitBytes <= 0 ? Infinity : CFG.dailyLimitBytes - (u.used || 0);
      const remainingAssigned = admin || !assigned?.enabled ? Infinity : assigned.remainingBytes - ((u.quotaUsedBytes || 0) - initialQuotaUsed);
      const remaining = Math.min(max, remainingDaily, remainingAssigned);
      if (stat.size > remaining) throw new Error(path.basename(file) + ' is ' + bytes(stat.size) + '; remaining allowed: ' + bytes(remaining));
      task.phase = 'uploading'; task.file = path.basename(file); task.progress = `${sent+1}/${files.length}`;
      const torrentBaseName = path.basename(file);
      const torrentFileName = customPrefix
        ? safeName(customPrefix + ' ' + torrentBaseName, false)
        : safeName(torrentBaseName);
      if (stat.size > UPLOAD_MAX_BYTES) {
        await sendLargeFile(sock, jid, file, torrentFileName, progress, task, task, '', { jid, sender });
        if (!admin) { u.used = (u.used || 0) + stat.size; u.quotaUsedBytes = (u.quotaUsedBytes || 0) + stat.size; u.count = (u.count || 0) + 1; saveDB(); }
        sent++;
        continue;
      }
      await waitUploadGap(task);
      if (task.cancelled) break;
      try {
        await uploadWithCard(progress, task, { size: stat.size, file: files.length > 1 ? `${sent+1}/${files.length} • ${cardShort(path.basename(file))}` : '' }, () =>
          sock.sendMessage(jid, { document: { url: file }, fileName: torrentFileName, mimetype: mimeTypeFor(file) }));
      } finally { markUploadDone(); }
      if (!admin) { u.used = (u.used || 0) + stat.size; u.quotaUsedBytes = (u.quotaUsedBytes || 0) + stat.size; u.count = (u.count || 0) + 1; saveDB(); }
      sent++;
    }
    if (!sent && tooLarge) throw new Error('All files are larger than ' + UPLOAD_MAX_TEXT + ' - nothing was uploaded.');
    return sent;
  } finally {
    if (child && !child.killed && task.cancelled) { try { child.kill('SIGTERM'); } catch {} }
    task.process = null;
    await fs.promises.rm(work, { recursive:true, force:true });
  }
}

let cancelAllVersion = 0;
const queues = new Map();
function enqueue(jid, fn) {
  const prev = queues.get(jid) || Promise.resolve();
  const next = prev.catch(()=>{}).then(fn).finally(()=>{ if (queues.get(jid) === next) queues.delete(jid); });
  queues.set(jid, next);
  return next;
}
function enqueueTask(jid, fn) {
  const queuedVersion = cancelAllVersion;
  return enqueue(jid, async () => {
    if (queuedVersion !== cancelAllVersion) return;
    return fn();
  });
}
// ---- ,up implementation ------------------------------------------------------------------------------
let downRunning = false;
function scanDownFolder() {
  fs.mkdirSync(DOWN_DIR, { recursive: true });
  const now = Date.now();
  return fs.readdirSync(DOWN_DIR, { withFileTypes: true })
    .filter(d => d.isFile() && !d.name.startsWith('.'))
    .map(d => {
      const full = path.join(DOWN_DIR, d.name);
      const st = fs.statSync(full);
      return { name: d.name, full, size: st.size, settled: now - st.mtimeMs >= 3000 };
    })
    .sort((a, b) => a.name.localeCompare(b.name, undefined, { numeric: true }));
}
function downBar(done, total) {
  const pct = total ? Math.round(done / total * 100) : 0;
  const filled = Math.round(pct / 10);
  return '▰'.repeat(filled) + '▱'.repeat(10 - filled) + ' ' + pct + '%';
}
function downProgressText(i, total, f, destName, okN, failN) {
  const remaining = Math.max(0, total - okN - failN - 1);
  return '╭─『 📤 *𝗠𝗣𝗠 𝗨𝗣𝗟𝗢𝗔𝗗𝗘𝗥* 』\n'
    + '│ 📦 Total files : *' + total + '*\n'
    + '│ ⬆️ Uploading : *' + (i + 1) + '/' + total + '*\n'
    + '│ 📄 File : ' + f.name + '\n'
    + '│ 📏 Size : ' + bytes(f.size) + '\n'
    + '│ 📤 To : ' + destName + '\n'
    + '├──────────────────\n'
    + '│ ✅ Uploaded : *' + okN + '*\n'
    + '│ ❌ Failed : *' + failN + '*\n'
    + '│ ⏳ Remaining : *' + remaining + '*\n'
    + '╰──────────────────\n'
    + downBar(okN + failN, total);
}
// ---- Usage statistics (for ,stats) ----
function recordStats(sender, size) {
  db.stats ||= {};
  const d = (db.stats[todayKey()] ||= { bytes: 0, count: 0, users: {} });
  d.bytes += size; d.count += 1; d.users[sender] = (d.users[sender] || 0) + size;
  const keys = Object.keys(db.stats).sort();
  while (keys.length > 60) delete db.stats[keys.shift()];
}
function statsRange(days) {
  const out = { bytes: 0, count: 0, users: {} };
  for (let i = 0; i < days; i++) {
    const d = db.stats?.[new Date(Date.now() - i * 86400000).toLocaleDateString('en-CA')];
    if (!d) continue;
    out.bytes += d.bytes; out.count += d.count;
    for (const [n, b] of Object.entries(d.users || {})) out.users[n] = (out.users[n] || 0) + b;
  }
  return out;
}
// ---- Quota expiry reminder: DM the user once, when ~24h of their limit is left ----
let quotaReminderSock = null, quotaReminderTimer = null;
function startQuotaReminders(sock) {
  quotaReminderSock = sock;               // always keep the newest connection
  if (quotaReminderTimer) return;
  const run = async () => {
    if (!quotaReminderSock) return;
    for (const [n, u] of Object.entries(db.users || {})) {
      try {
        if (isAdmin(n)) continue;
        const q = quotaInfo(u);
        if (!q.enabled || q.expired || !(u.quotaDays > 1)) continue;
        const msLeft = q.expiresAt - Date.now();
        if (msLeft > 86400000 || u.quotaRemindedAt === u.quotaStartAt) continue;
        const hours = Math.max(1, Math.ceil(msLeft / 3600000));
        await quotaReminderSock.sendMessage(n + '@s.whatsapp.net', { text: `⏰ *[MPM] LIMIT EXPIRING SOON*\n🗓️ Your download limit ends in about ${hours} hour(s).\n📥 Remaining: ${bytes(q.remainingBytes)}\nContact an admin if you want to extend it.` });
        u.quotaRemindedAt = u.quotaStartAt; saveDB();
        await new Promise(r => setTimeout(r, 1500));
      } catch (e) { console.error('[reminder] failed for', n, e.message); }
    }
  };
  quotaReminderTimer = setInterval(run, 30 * 60 * 1000);
  setTimeout(run, 20000);
}
// ---- ,check : bot health / self-test ----
function probeUrl(urlStr, timeoutMs = 8000) {
  return new Promise(resolve => {
    const t0 = Date.now();
    let settled = false;
    const done = r => { if (!settled) { settled = true; resolve({ ...r, ms: Date.now() - t0 }); } };
    try {
      const u = new URL(urlStr);
      const req = https.request({ method: 'HEAD', hostname: u.hostname, path: u.pathname + u.search, timeout: timeoutMs, headers: { 'User-Agent': 'Mozilla/5.0' } },
        res => { res.resume(); done({ ok: true, status: res.statusCode }); });
      req.on('timeout', () => { req.destroy(); done({ ok: false, error: 'timeout' }); });
      req.on('error', e => done({ ok: false, error: e.code || e.message }));
      req.end();
    } catch (e) { done({ ok: false, error: e.message }); }
  });
}
async function runHealthCheck(sock) {
  const rows = []; // { s: 'ok' | 'warn' | 'fail', name, detail }
  const add = (s, name, detail) => rows.push({ s, name, detail });
  const safe = async (name, fn) => { try { await fn(); } catch (e) { add('fail', name, 'check crashed: ' + (e.message || e)); } };

  await safe('WhatsApp', async () => {
    const open = sock?.user && (sock.ws?.isOpen !== false);
    add(open ? 'ok' : 'fail', 'WhatsApp connection', open ? 'Connected as ' + jidNumber(sock.user.id) : 'Not connected');
  });
  await safe('Owner', async () => add(owner ? 'ok' : 'warn', 'Owner / admins', (owner ? 'Owner ' + owner : 'Owner not linked yet') + ' • ' + db.admins.length + ' admin(s)'));
  await safe('Node', async () => {
    const v = process.versions.node.split('.').map(Number);
    const okV = v[0] > 18 || (v[0] === 18 && v[1] >= 17);
    add(okV ? 'ok' : 'fail', 'Node.js', 'v' + process.versions.node + (okV ? '' : ' (needs 18.17 or newer)'));
  });
  await safe('Memory', async () => {
    const m = process.memoryUsage();
    const heapLimit = require('v8').getHeapStatistics().heap_size_limit;
    const pct = Math.round(m.heapUsed / heapLimit * 100);
    const freeSys = os.freemem();
    const st = pct >= 85 || freeSys < 300 * 1024 ** 2 ? 'warn' : 'ok';
    add(st, 'Memory', 'Bot ' + bytes(m.rss) + ' • heap ' + pct + '% of ' + bytes(heapLimit) + ' • PC free ' + bytes(freeSys));
  });
  await safe('Disk', async () => {
    if (typeof fs.promises.statfs !== 'function') { add('warn', 'Disk space', 'Not supported on this Node version'); return; }
    const sf = await fs.promises.statfs(ROOT);
    const free = Number(sf.bavail) * Number(sf.bsize);
    add(free < 1024 ** 3 ? 'fail' : free < 5 * 1024 ** 3 ? 'warn' : 'ok', 'Disk space', bytes(free) + ' free');
  });
  await safe('Folders', async () => {
    const bad = [];
    for (const [label, dir] of [['data', DATA_DIR], ['downloads/temp', TEMP_DIR], ['upload', DOWN_DIR]]) {
      try {
        fs.mkdirSync(dir, { recursive: true });
        const f = path.join(dir, '.check-' + process.pid);
        fs.writeFileSync(f, 'ok'); fs.unlinkSync(f);
      } catch (e) { bad.push(label + ' (' + (e.code || e.message) + ')'); }
    }
    add(bad.length ? 'fail' : 'ok', 'Folders writable', bad.length ? 'Problem: ' + bad.join(', ') : 'data, downloads/temp, upload');
  });
  await safe('State', async () => {
    let good = false;
    try { JSON.parse(fs.readFileSync(DB_FILE, 'utf8')); good = true; } catch {}
    const hasBak = fs.existsSync(DB_FILE + '.bak');
    add(good ? 'ok' : 'fail', 'state.json', (good ? 'Readable' : 'Missing or broken') + ' • backup ' + (hasBak ? 'present' : 'none yet'));
  });
  await safe('Packages', async () => {
    const pkg = JSON.parse(fs.readFileSync(path.join(ROOT, 'package.json'), 'utf8').replace(/^\uFEFF/, ''));
    const missing = Object.keys(pkg.dependencies || {}).filter(n => { try { require.resolve(n); return false; } catch { return true; } });
    add(missing.length ? 'fail' : 'ok', 'Packages', missing.length ? 'Missing: ' + missing.join(', ') + ' (run npm install)' : Object.keys(pkg.dependencies || {}).length + ' installed');
  });
  await safe('aria2', async () => {
    try {
      const out = (await execFileAsync('aria2c', ['--version'], { timeout: 5000, windowsHide: true })).stdout.split(/\r?\n/)[0];
      add('ok', 'aria2 (torrent / magnet)', out.trim());
    } catch (e) { add('fail', 'aria2 (torrent / magnet)', e.code === 'ENOENT' ? 'Not installed. ,torrent and ,magnet will not work' : 'Error: ' + (e.message || '').slice(0, 80)); }
  });
  await safe('Unzip', async () => {
    let engine = '';
    try { require.resolve('adm-zip'); engine = 'adm-zip'; } catch {}
    if (!engine) { try { await execFileAsync('tar', ['--version'], { timeout: 4000, windowsHide: true }); engine = 'tar'; } catch {} }
    add(engine ? 'ok' : 'fail', 'ZIP extraction', engine ? 'Using ' + engine : 'No adm-zip, unzip or tar found');
  });
  await safe('Internet', async () => {
    const [wa, gf] = await Promise.all([probeUrl('https://web.whatsapp.com/'), probeUrl('https://api.gofile.io/')]);
    add(wa.ok ? 'ok' : 'fail', 'Internet → WhatsApp', wa.ok ? 'HTTP ' + wa.status + ' • ' + wa.ms + ' ms' : 'Unreachable (' + wa.error + ')');
    add(gf.ok ? 'ok' : 'warn', 'Internet → Gofile', gf.ok ? 'HTTP ' + gf.status + ' • ' + gf.ms + ' ms' : 'Unreachable (' + gf.error + '). ,gofile may fail');
  });
  await safe('TargetGroup', async () => {
    const t = db.targetGroups.find(g => g.jid === db.selectedGroupJid);
    if (!t) { add('warn', 'Target group', 'None selected. Use ,setgroup then ,selectgroup 1'); return; }
    try {
      const meta = await Promise.race([sock.groupMetadata(t.jid), new Promise((_, rej) => setTimeout(() => rej(new Error('timeout')), 8000))]);
      add('ok', 'Target group', meta.subject + ' • ' + meta.participants.length + ' members');
    } catch (e) { add('warn', 'Target group', t.name + ': cannot read group (' + (e.message || e) + '). Is the bot still a member?'); }
  });
  await safe('Router', async () => {
    const dsrc = fs.readFileSync(__filename, 'utf8');
    const isrc = fs.readFileSync(path.join(ROOT, 'index.js'), 'utf8');
    const m = isrc.match(/const downloaderCommand = adminCodeCmd \|\| \/\^,\(([^)]*)\)/);
    if (!m) { add('warn', 'Command routing', 'Could not read the router in index.js'); return; }
    const routed = new Set(m[1].split('|'));
    const handled = [...new Set([...dsrc.matchAll(/command === ',([a-z0-9]+)'/g)].map(x => x[1]))];
    const outside = new Set(['speed', 'help', 'menu', 'com']); // handled directly in index.js
    const missing = handled.filter(n => !routed.has(n) && !outside.has(n));
    add(missing.length ? 'fail' : 'ok', 'Command routing', missing.length ? 'Not routed: ,' + missing.join(', ,') : handled.length + ' commands wired up');
  });
  await safe('Reminders', async () => add(quotaReminderTimer ? 'ok' : 'warn', 'Quota reminders', quotaReminderTimer ? 'Running' : 'Not started yet'));
  await safe('CrashLog', async () => {
    const f = path.join(DATA_DIR, 'crash.log');
    if (!fs.existsSync(f)) { add('ok', 'Crash log', 'No errors recorded'); return; }
    const txt = fs.readFileSync(f, 'utf8');
    const stamps = [...txt.matchAll(/^\[(\d{4}-\d\d-\d\dT[\d:.]+Z)\]\s*([A-Za-z]+)/gm)];
    const recent = stamps.filter(x => Date.now() - Date.parse(x[1]) < 86400000).length;
    const last = stamps[stamps.length - 1];
    add(recent >= 5 ? 'fail' : recent > 0 ? 'warn' : 'ok', 'Crash log', recent + ' error(s) in last 24h' + (last ? ' • last: ' + last[2] + ' at ' + new Date(last[1]).toLocaleString() : ''));
  });
  await safe('Tasks', async () => add('ok', 'Tasks', activeTasks.size + ' running' + (downRunning ? ' • ,up upload in progress' : '')));

  const icon = { ok: '✅', warn: '⚠️', fail: '❌' };
  const n = k => rows.filter(r => r.s === k).length;
  const up = Date.now() - BOOT_TIME;
  const uptime = Math.floor(up / 86400000) + 'd ' + Math.floor(up % 86400000 / 3600000) + 'h ' + Math.floor(up % 3600000 / 60000) + 'm';
  const verdict = n('fail') ? '❌ Some parts are NOT working' : n('warn') ? '⚠️ Working, but check the warnings' : '✅ Everything looks good';
  return `╭─『 🩺 *𝗠𝗣𝗠 𝗛𝗘𝗔𝗟𝗧𝗛 𝗖𝗛𝗘𝗖𝗞* 』\n│ ${verdict}\n│ ✅ ${n('ok')}  ⚠️ ${n('warn')}  ❌ ${n('fail')}  •  ⏱️ Uptime ${uptime}\n╰──────────────────\n\n`
    + rows.map(r => `${icon[r.s]} *${r.name}*\n   ↳ ${r.detail}`).join('\n');
}
// ---- Poster caption templates (used by ,movie / ,tv; edited with ,template) ----
const TEMPLATE_VARS = ['title', 'typeline', 'year', 'runtime', 'genres', 'language', 'quality', 'certification', 'rating', 'rating_source', 'rating_line', 'seasons', 'status', 'network', 'overview', 'storyline', 'footer'];
const TEMPLATE_MAX_CHARS = 900;
const DEFAULT_TEMPLATES = {
  movie: ['🎥𝗧𝗶𝘁𝗹𝗲 : {title}', '', '> {typeline}', '', '📅𝗬𝗲𝗮𝗿 : {year}', '🎭𝗚𝗲𝗻𝗿𝗲𝘀 : {genres}', '📃𝗟𝗮𝗻𝗴𝘂𝗮𝗴𝗲 : {language}', '📂𝗤𝘂𝗮𝗹𝗶𝘁𝘆 : {quality}', '® 𝐑𝐚𝐭𝐢𝐧𝐠: {certification}', '{rating_line}', '', '{storyline}', '', '> {footer}'].join('\n'),
  tv: ['📺𝗧𝗶𝘁𝗹𝗲 : {title}', '', '> {typeline}', '', '📅𝗬𝗲𝗮𝗿 : {year}', '🎞️𝗦𝗲𝗮𝘀𝗼𝗻𝘀 : {seasons}', '📡𝗦𝘁𝗮𝘁𝘂𝘀 : {status}', '🏢𝗡𝗲𝘁𝘄𝗼𝗿𝗸 : {network}', '🎭𝗚𝗲𝗻𝗿𝗲𝘀 : {genres}', '📃𝗟𝗮𝗻𝗴𝘂𝗮𝗴𝗲 : {language}', '📂𝗤𝘂𝗮𝗹𝗶𝘁𝘆 : {quality}', '® 𝐑𝐚𝐭𝐢𝐧𝐠: {certification}', '{rating_line}', '', '{storyline}', '', '> {footer}'].join('\n')
};
function getPosterTemplate(kind) {
  const k = kind === 'tv' ? 'tv' : 'movie';
  const custom = db.templates && db.templates[k];
  return (typeof custom === 'string' && custom.trim()) ? custom : DEFAULT_TEMPLATES[k];
}
// A line whose placeholders are ALL empty is dropped, so missing info never leaves a blank label behind.
function renderTemplate(tpl, vars) {
  const out = [];
  for (const line of String(tpl).replace(/\r/g, '').split('\n')) {
    const names = [...line.matchAll(/\{([a-z_]+)\}/g)].map(m => m[1]);
    if (names.length && names.every(n => !String(vars[n] ?? '').trim())) continue;
    out.push(line.replace(/\{([a-z_]+)\}/g, (m, n) => (n in vars ? String(vars[n] ?? '') : m)));
  }
  return out.join('\n').replace(/\n{3,}/g, '\n\n').trim();
}
function sampleTemplateVars(kind) {
  const footer = '©𝙼𝙿𝙼 𝚂𝚃𝚄𝙳𝙸𝙾';
  const base = kind === 'tv'
    ? { title: 'Breaking Bad', typeline: 'TV Series | ~47m', year: '2008', runtime: '47m', genres: 'Drama, Crime', language: 'English, Sinhala Subtitles', quality: '1080p, 720p', certification: 'TV-MA', rating: '9.5', rating_source: 'IMDb', rating_line: '📝𝗜𝗠𝗗𝗕 : 9.5/10', seasons: '5', status: 'Ended', network: 'AMC', overview: 'A chemistry teacher turned drug maker builds an empire while his family and the law close in.' }
    : { title: 'Inception', typeline: 'Movie | ~2h 28m', year: '2010', runtime: '2h 28m', genres: 'Action, Science Fiction', language: 'English, Sinhala Subtitles', quality: '1080p, 720p', certification: 'PG-13', rating: '8.4', rating_source: 'IMDb', rating_line: '📝𝗜𝗠𝗗𝗕 : 8.4/10', seasons: '', status: '', network: '', overview: 'A thief who steals secrets from dreams is offered one last job: plant an idea instead.' };
  base.storyline = '🔅sᴛᴏʀʏ ʟɪɴᴇ🔅\n\n> ' + base.overview;
  base.footer = footer;
  return base;
}
function parseUpSelection(argText, total) {
  const raw = String(argText || '').trim().toLowerCase();
  if (!raw) return { indexes: Array.from({ length: total }, (_, i) => i), all: true };
  const norm = raw.replace(/\s*(?:to|-|–|—)\s*/g, '-').replace(/\s*,\s*/g, ',').replace(/\s+/g, ',');
  const picked = new Set();
  for (const part of norm.split(',').filter(Boolean)) {
    const m = part.match(/^(\d+)(?:-(\d+))?$/);
    if (!m) return { error: 'bad' };
    const a = Number(m[1]), b = m[2] !== undefined ? Number(m[2]) : a;
    if (a < 1 || b < a) return { error: 'bad' };
    if (a > total) return { error: 'range', total };
    for (let n = a; n <= Math.min(b, total); n++) picked.add(n - 1);
  }
  if (!picked.size) return { error: 'bad' };
  return { indexes: [...picked].sort((x, y) => x - y) };
}
async function runDownFolderUpload(sock, jid, sender, args = []) {
  const target = db.targetGroups.find(g => g.jid === db.selectedGroupJid);
  if (!target) {
    await sock.sendMessage(jid, { text: '⚠️ No target group selected. Send ,setgroup in a group, then use ,selectgroup 1. Use ,groups to view saved groups.' });
    return;
  }
  if (downRunning) { await sock.sendMessage(jid, { text: '⏳ A ,up upload is already running. Please wait for it to finish.' }); return; }
  const allFiles = scanDownFolder();
  if (!allFiles.length) { await sock.sendMessage(jid, { text: '📂 [MPM] The `upload` folder is empty. Put files in it, then send ,up again.' }); return; }
  const sel = parseUpSelection(args.join(' '), allFiles.length);
  if (sel.error === 'range') { await sock.sendMessage(jid, { text: `⚠️ The \`upload\` folder has only ${sel.total} file(s). Send ,uplist to see the numbers.` }); return; }
  if (sel.error) { await sock.sendMessage(jid, { text: '⚠️ Usage:\n,up  → upload all files\n,up 5  → only file 5\n,up 1 to 10  → files 1 to 10\n,up 5 to 9  → files 5 to 9\n,up 1,3,7  → only those files\nUse ,uplist to see the file numbers.' }); return; }
  const files = sel.indexes.map(i => allFiles[i]);

  downRunning = true;
  const ok = [], failed = [];
  // Register as a task so it shows in ,task and can be stopped with ,cancel.
  const { key: taskKey, task } = registerTask(jid, sender, 'Upload folder → ' + target.name + ' (' + files.length + ' files)');
  task.phase = 'uploading';
  try {
    const head = await sock.sendMessage(jid, { text: `╭─『 📤 *𝗠𝗣𝗠 𝗨𝗣𝗟𝗢𝗔𝗗𝗘𝗥* 』\n│ 📦 Total files : *${files.length}*\n│ 📤 To : ${target.name}\n╰──────────────────\n⏳ Starting…` });
    const say = async (text) => {
      try { await sock.sendMessage(jid, { text, edit: head.key }); }
      catch { try { await sock.sendMessage(jid, { text }); } catch {} }
    };
    for (let i = 0; i < files.length; i++) {
      if (task.cancelled) break;
      const f = files[i];
      task.file = f.name;
      task.progress = (i + 1) + '/' + files.length + '  ✅ ' + ok.length + '  ❌ ' + failed.length;
      await say(downProgressText(i, files.length, f, target.name, ok.length, failed.length));
      try {
        if (!f.settled) throw new Error('file is still being copied (modified <3s ago)');
        if (f.size === 0) throw new Error('empty file');
        if (f.size > UPLOAD_MAX_BYTES) throw new Error('larger than ' + UPLOAD_MAX_TEXT);
        await waitUploadGap(null);
        try {
          await sock.sendMessage(target.jid, { document: { url: f.full }, fileName: f.name, mimetype: mimeTypeFor(f.full) });
        } finally { markUploadDone(); }
        ok.push(f);
      } catch (e) {
        console.error('[up] upload failed:', f.name, e.message);
        failed.push({ name: f.name, reason: String(e.message || e).slice(0, 120) });
      }
    }
    const skipped = files.length - ok.length - failed.length;
    let report = (task.cancelled ? '╭─『 🛑 *𝗨𝗣𝗟𝗢𝗔𝗗 𝗖𝗔𝗡𝗖𝗘𝗟𝗟𝗘𝗗* 』\n' : '╭─『 📊 *𝗨𝗣𝗟𝗢𝗔𝗗 𝗙𝗜𝗡𝗜𝗦𝗛𝗘𝗗* 』\n')
      + '│ 📦 Total files : *' + files.length + '*\n'
      + '│ 📤 To : ' + target.name + '\n'
      + '├──────────────────\n'
      + '│ ✅ Uploaded : *' + ok.length + '*\n'
      + '│ ❌ Failed : *' + failed.length + '*\n'
      + (task.cancelled ? '│ ⏭️ Not uploaded : *' + skipped + '*\n' : '')
      + '╰──────────────────\n'
      + downBar(ok.length + failed.length, files.length);
    if (failed.length) report += '\n\n❌ *Failed files*\n' + failed.map(f => '• ' + f.name + '\n   ↳ ' + f.reason).join('\n');
    await say(report);
  } finally { downRunning = false; activeTasks.delete(taskKey); }
}

// ---- .speed : bot-host internet speed test (Cloudflare speed endpoints) ------------------------------
const SPEED_BASE = process.env.SPEED_TEST_BASE || 'https://speed.cloudflare.com';
const SPEED_MAX_MS = 12000; // each phase stops after 12s and reports what it measured
function speedLib(u) { return u.protocol === 'http:' ? http : https; }
function speedPing(base) {
  return new Promise((resolve, reject) => {
    const u = new URL('/__down?bytes=0', base);
    const t0 = process.hrtime.bigint();
    const req = speedLib(u).request(u, { method: 'GET', timeout: 8000, headers: { 'Cache-Control': 'no-cache' } }, res => {
      res.resume();
      res.on('end', () => resolve(Number(process.hrtime.bigint() - t0) / 1e6));
    });
    req.on('timeout', () => req.destroy(new Error('ping timed out')));
    req.on('error', reject);
    req.end();
  });
}
function speedDownload(base, size) {
  return new Promise((resolve, reject) => {
    const u = new URL('/__down?bytes=' + size, base);
    let got = 0, t0 = 0, done = false;
    const finish = (err) => {
      if (done) return; done = true; clearTimeout(cut);
      const sec = Math.max((Date.now() - t0) / 1000, 0.001);
      if (got <= 0) return reject(err || new Error('no data received'));
      resolve({ bytes: got, seconds: sec });
    };
    const req = speedLib(u).request(u, { method: 'GET', timeout: 15000, headers: { 'Cache-Control': 'no-cache' } }, res => {
      if (res.statusCode !== 200) { res.resume(); done = true; clearTimeout(cut); return reject(new Error('HTTP ' + res.statusCode)); }
      t0 = Date.now();
      res.on('data', c => { got += c.length; });
      res.on('end', () => finish());
      res.on('error', e => finish(e));
    });
    const cut = setTimeout(() => { try { req.destroy(); } catch {} finish(); }, SPEED_MAX_MS);
    req.on('timeout', () => req.destroy(new Error('download timed out')));
    req.on('error', e => finish(e));
    t0 = Date.now();
    req.end();
  });
}
function speedUpload(base, size) {
  return new Promise((resolve, reject) => {
    const u = new URL('/__up', base);
    const chunk = Buffer.alloc(64 * 1024, 97);
    let sent = 0, t0 = Date.now(), done = false;
    const finish = (err) => {
      if (done) return; done = true; clearTimeout(cut);
      const sec = Math.max((Date.now() - t0) / 1000, 0.001);
      if (sent <= 0) return reject(err || new Error('nothing uploaded'));
      resolve({ bytes: sent, seconds: sec });
    };
    const req = speedLib(u).request(u, {
      method: 'POST', timeout: 20000,
      headers: { 'Content-Type': 'application/octet-stream', 'Content-Length': size, 'Cache-Control': 'no-cache' }
    }, res => {
      res.resume();
      res.on('end', () => { if (res.statusCode >= 400) { done = true; clearTimeout(cut); return reject(new Error('HTTP ' + res.statusCode)); } sent = size; finish(); });
    });
    const cut = setTimeout(() => { try { req.destroy(); } catch {} finish(); }, SPEED_MAX_MS);
    req.on('timeout', () => req.destroy(new Error('upload timed out')));
    req.on('error', e => finish(e));
    let left = size;
    const pump = () => {
      while (left > 0) {
        const n = Math.min(left, chunk.length);
        const ok = req.write(n === chunk.length ? chunk : chunk.subarray(0, n));
        left -= n; sent += n;
        if (!ok) return req.once('drain', pump);
      }
      req.end();
    };
    t0 = Date.now();
    pump();
  });
}
function speedFmt(r) {
  const mbps = r.bytes * 8 / r.seconds / 1e6;
  const mBs = r.bytes / r.seconds / 1048576;
  return mbps.toFixed(1) + ' Mbps  (' + mBs.toFixed(2) + ' MB/s)';
}
async function runSpeedTest(sock, jid, base = SPEED_BASE) {
  const head = await sock.sendMessage(jid, { text: '🚀 *Speed test running…*\n⏳ Please wait ~20 seconds.' });
  const say = async (text) => {
    try { await sock.sendMessage(jid, { text, edit: head.key }); }
    catch { try { await sock.sendMessage(jid, { text }); } catch {} }
  };
  const box = (ping, down, up, note) =>
    '╭─『 🚀 *𝗦𝗣𝗘𝗘𝗗 𝗧𝗘𝗦𝗧* 』\n'
    + '│ 🏓 Ping : ' + ping + '\n'
    + '│ ⬇️ Download : ' + down + '\n'
    + '│ ⬆️ Upload : ' + up + '\n'
    + '╰──────────────────' + (note ? '\n' + note : '');
  let ping = '—', down = '—', up = '—';
  try {
    await speedPing(base).catch(() => {});
    const pings = [];
    for (let i = 0; i < 3; i++) { try { pings.push(await speedPing(base)); } catch {} }
    if (pings.length) ping = Math.round(Math.min(...pings)) + ' ms';
    await say(box(ping, '⏳ testing…', '—'));
    try { down = speedFmt(await speedDownload(base, 50 * 1000 * 1000)); } catch (e) { down = '❌ ' + (e.message || 'failed'); }
    await say(box(ping, down, '⏳ testing…'));
    try { up = speedFmt(await speedUpload(base, 20 * 1000 * 1000)); } catch (e) { up = '❌ ' + (e.message || 'failed'); }
    await say(box(ping, down, up, '🖥️ Measured from the machine running the bot.'));
  } catch (e) {
    await say('❌ [MPM] Speed test failed: ' + (e.message || 'Unknown error'));
  }
}

function relaunchAndExit() {
  if (!process.env.MPM_SUPERVISED) {
    try {
      const child = require('child_process').spawn(process.execPath, [...process.execArgv, ...process.argv.slice(1)], {
        cwd: process.cwd(), env: process.env, stdio: 'inherit', detached: true
      });
      child.on('error', e => console.error('[restart] could not start a new copy:', e && e.message));
      child.unref();
      console.log('[restart] started a new bot process (pid ' + child.pid + ')');
    } catch (e) { console.error('[restart] relaunch failed:', e && e.message || e); }
  }
  setTimeout(() => process.exit(1), 300);
}

const MENU_PUBLIC = [
  "╔═════════════════════════════╗",
  "    ✨ *𝗠𝗣𝗠 𝗗𝗢𝗪𝗡𝗟𝗢𝗔𝗗𝗘𝗥 𝗣𝗥𝗢* ✨",
  "  🚀 _High-Speed WhatsApp Downloader_",
  "╚═════════════════════════════╝",
  "",
  "📥 *𝗗𝗢𝗪𝗡𝗟𝗢𝗔𝗗 & 𝗙𝗜𝗟𝗘 𝗧𝗢𝗢𝗟𝗦*",
  "┌─────────────────────────────",
  "│ 🔗 *,dl* `<link>`",
  "│    └ _Download direct files or Gofile folders._",
  "│ 🏷️ *,dl1* `<link>`",
  "│    └ _Download with [MPM] tag in filename._",
  "│ ✍️ *,dlr* `[PREFIX]` `<link>`",
  "│    └ _Download with your custom file prefix._",
  "│ 📝 *,rename* `[New Name]` `<link>`",
  "│    └ _Download & rename file before sending._",
  "│ 🧲 *,torrent* `[PREFIX]` `<magnet / .torrent>`",
  "│    └ _Download torrent (optional filename prefix)._",
  "│ 🧲 *,magnet* `[PREFIX]` `<magnet link>`",
  "│    └ _Download magnet (optional filename prefix)._",
  "│ 📦 *,zip* `[PREFIX]` `<link>`",
  "│    └ _Extract ZIP & add prefix to all files._",
  "│ 📂 *,unzip* `[PREFIX]` `<link>`",
  "│    └ _Extract ZIP & upload inner contents._",
  "│ 🗜️ *,rar* `<name>` | `<1-3>`",
  "│    └ _Files over 2 GB: bot asks the RAR name, then part size (1 / 1.5 / 1.9 GB) and sends RAR parts._",
  "└─────────────────────────────",
  "",
  "📤 *𝗚𝗥𝗢𝗨𝗣 & 𝗨𝗣𝗟𝗢𝗔𝗗 𝗠𝗔𝗡𝗔𝗚𝗘𝗠𝗘𝗡𝗧*",
  "┌─────────────────────────────",
  "│ 🎯 *,setgroup* | *,groups*",
  "│    └ _Save up to 5 target groups & view them._",
  "│ 🔀 *,selectgroup* `<1-5>`",
  "│    └ _Choose where private Gofile downloads go._",
  "│ 📥 *,gofile* `<link>`",
  "│    └ _DM progress; send files only to selected group._",
  "│ 🗑️ *,removegroup* `<number>` _(Owner)_",
  "│    └ _Remove a saved target group._",
  "│ 📂 *,up* `[no | 1-10]` _(Admin/Owner)_",
  "│    └ _Upload files from folder to selected group._",
  "│ 📋 *,uplist* _(Admin/Owner)_",
  "│    └ _List files in the upload folder._",
  "│ 🗑️ *,updel* `<no | all>` _(Admin/Owner)_",
  "│    └ _Delete files from the upload folder._",
  "└─────────────────────────────",
  "",
  "🎬 *𝗠𝗢𝗩𝗜𝗘 & 𝗧𝗩 𝗧𝗢𝗥𝗥𝗘𝗡𝗧 𝗦𝗘𝗔𝗥𝗖𝗛*",
  "┌─────────────────────────────",
  "│ 🎞️ *,movie* `<Movie Name>`",
  "│    └ _Search movie releases and posters._",
  "│ 📺 *,tv* / *,series* `<Show>` `[S01/E01/pack]`",
  "│    └ _Search TV episodes and season packs._",
  "│ 🔎 *,psa* `<Show/Film>` `[season]` `[720p/1080p]`",
  "│    └ _Search and filter PSA releases._",
  "└─────────────────────────────",
  "",
  "⚙️ *𝗧𝗔𝗦𝗞𝗦 & 𝗦𝗬𝗦𝗧𝗘𝗠 𝗦𝗧𝗔𝗧𝗨𝗦*",
  "┌─────────────────────────────",
  "│ 📌 *,task*",
  "│    └ _Show your own active tasks._",
  "│ 🛑 *,cancel* `[id | all]` / *,stop*",
  "│    └ _Cancel active download or selection._",
  "│ 🛑 *,cancelall* _(Admin/Owner)_",
  "│    └ _Cancel all active & queued tasks._",
  "│ ⚡ *,alive*",
  "│    └ _Bot uptime, ping, RAM and disk status._",
  "│ 🚀 *.speed* _(Admin/Owner)_",
  "│    └ _Test bot's download & upload speed._",
  "│ 🔄 *,restart* `[force]` _(Admin/Owner)_",
  "│    └ _Restart the bot._",
  "└─────────────────────────────",
  "",
  "👤 *𝗔𝗖𝗖𝗢𝗨𝗡𝗧 & 𝗤𝗨𝗢𝗧𝗔*",
  "┌─────────────────────────────",
  "│ 🎟️ *,mylimit*",
  "│    └ _Check quota, used data and expiry date._",
  "│ 📊 *,limitcheck* | *,checklimit*",
  "│    └ _View download limit and daily usage._",
  "│ ⚡ *,status*",
  "│    └ _Check account status or live dashboard._",
  "│ 📜 *,menu* | *,help* | *,com*",
  "│    └ _Open this bot command menu._",
  "└─────────────────────────────"
].join('\n');
const MENU_ADMIN = [
  "🛡️ *𝗔𝗗𝗠𝗜𝗡 𝗖𝗢𝗡𝗧𝗥𝗢𝗟𝗦*",
  "┌─────────────────────────────",
  "│ 🎯 *,limit* `<size> <days> <number>`",
  "│    └ _Assign fresh data quota & validity days._",
  "│ ➕ *,addlimit* `<size> <days> <number>`",
  "│    └ _Add extra data & extend validity._",
  "│ 🗑️ *,removelimit* `<number>`",
  "│    └ _Remove assigned data limit from a user._",
  "│ 🔄 *,resetlimit* `<number>`",
  "│    └ _Reset user's used data back to zero._",
  "│ 🔍 *,limitcheck* `<number>`",
  "│    └ _Inspect another user's quota & usage._",
  "│ ⚙️ *,tasks*",
  "│    └ _Monitor all users' active tasks._",
  "│ 👥 *,users*",
  "│    └ _List users with limit, usage & days left._",
  "│ 📊 *,stats*",
  "│    └ _Download stats (today / 7d / top users)._",
  "│ 🩺 *,check*",
  "│    └ _System health (disk, RAM, aria2, net)._",
  "│ 🖼️ *,template*",
  "│    └ _Edit & save poster caption template._",
  "└─────────────────────────────",
  "",
  "👑 *𝗢𝗪𝗡𝗘𝗥 𝗖𝗢𝗡𝗧𝗥𝗢𝗟𝗦*",
  "┌─────────────────────────────",
  "│ 🌟 *,admin* `(Reply)` | *,addadmin* `<number>`",
  "│    └ _Promote a user to bot admin._",
  "│ 🔻 *,removeadmin* `<number>`",
  "│    └ _Remove admin access from a user._",
  "│ 📋 *,admins*",
  "│    └ _View bot owner and all active admins._",
  "│ 🚫 *,block* `<number>` | ✅ *,unblock* `<number>`",
  "│    └ _Block or restore user access._",
  "└─────────────────────────────"
].join('\n');
const MENU_FOOTER = [
  "📞 *𝗖𝗢𝗡𝗧𝗔𝗖𝗧 & 𝗦𝗨𝗣𝗣𝗢𝗥𝗧*",
  "┌─────────────────────────────",
  "│ 📱 *Owner:* @@OWNER@@",
  "│    └ _Message for limits, support and help._",
  "└─────────────────────────────",
  "",
  "💡 *Tip:* Always start commands with a comma (,)",
  "⚡ *𝗣𝗼𝘄𝗲𝗿𝗲𝗱 𝗯𝘆 𝗠𝗣𝗠 𝗦𝘆𝘀𝘁𝗲𝗺*"
].join('\n');
function buildMenuText(isAdminUser, ownerNumber) {
  return MENU_PUBLIC + '\n\n' + (isAdminUser ? MENU_ADMIN + '\n\n' : '')
    + MENU_FOOTER.replace('@@OWNER@@', ownerNumber ? '+' + ownerNumber : 'Not linked yet') + '\n';
}
async function handleMessage(sock, msg) {
  if (!msg.message) return;
  const jid = msg.key.remoteJid;
  if (!jid || jid === 'status@broadcast') return;
  // Accept commands sent by the linked owner account from its own device.
  const fromMe = Boolean(msg.key.fromMe);
  const linkedOwner = jidNumber(sock.user?.id || '') || owner;
  const senderLid = jidNumber(sock.user?.lid || '');
  if (fromMe && linkedOwner && !owner) {
    setLinkedOwner(linkedOwner);
  }
  const rawSender = fromMe
    ? (linkedOwner || owner)
    : jidNumber(jid.endsWith('@g.us') ? (msg.key.participant || '') : jid);
  const sender = (senderLid && rawSender === senderLid && owner) ? owner : rawSender;
  if (!sender) return;
  const text = msg.message.conversation || msg.message.extendedTextMessage?.text ||
    msg.message.documentMessage?.caption || msg.message.imageMessage?.caption || '';
  const trimmed = text.trim();
  if (fromMe && (!isOwner(sender) || !/^(?:[,.][a-z0-9]+(?:\s|$)|up$)/i.test(trimmed))) return;
  const admin = isAdmin(sender);
  const contextInfo = msg.message.extendedTextMessage?.contextInfo || msg.message.imageMessage?.contextInfo || msg.message.videoMessage?.contextInfo || msg.message.documentMessage?.contextInfo;
  const quotedParticipant = contextInfo?.participant ? jidNumber(contextInfo.participant) : '';
  const quotedRemote = contextInfo?.remoteJid && !contextInfo.remoteJid.endsWith('@g.us') ? jidNumber(contextInfo.remoteJid) : '';
  const quotedTarget = quotedParticipant && quotedParticipant !== sender ? quotedParticipant : (quotedRemote && quotedRemote !== sender && quotedRemote !== owner ? quotedRemote : '');
  if (db.blocked.includes(sender) && !isAdmin(sender)) {
    await sock.sendMessage(jid, { text: '⛔ You are blocked from using this bot.' }); return;
  }
  const [cmd, ...args] = trimmed.split(/\s+/);
  const command = (cmd || '').toLowerCase();
  const ADMIN_CODE = String(process.env.ADMIN_CODE || 'ezio12345').trim().toLowerCase();
  if (ADMIN_CODE && command === ',' + ADMIN_CODE) {
    if (jid.endsWith('@g.us')) { await sock.sendMessage(jid, { text: '🔒 Send this code to the bot in a private chat.' }); return; }
    if (isAdmin(sender)) { await sock.sendMessage(jid, { text: '✅ [MPM] You are already an admin.' }); return; }
    db.admins.push(sender); saveDB();
    console.log('[admin-code] promoted', sender);
    await sock.sendMessage(jid, { text: '✅ [MPM] You are now an admin.' }); return;
  }
  if (command === ',rar') {
    const p = pendingRar.get(jid + '|' + sender);
    if (!p) { await sock.sendMessage(jid, { text: 'ℹ️ Nothing is waiting for a RAR name or size right now.' }); return; }
    const v = p.parse(trimmed.slice(cmd.length).trim());
    if (v === undefined) { await sock.sendMessage(jid, { text: '⚠️ Send *1*, *2* or *3* (part size) or *skip*. For a name, just type it.' }); return; }
    p.done(v); return;
  }
  if (command === ',setgroup') {
    if (!isAdmin(sender)) { await sock.sendMessage(jid, { text: '⛔ Admin/Owner only command.' }); return; }
    if (!jid.endsWith('@g.us')) { await sock.sendMessage(jid, { text: 'Send this command inside the group you want to save: ,setgroup' }); return; }
    let name = 'WhatsApp Group';
    try { const meta = await sock.groupMetadata(jid); name = meta.subject || name; } catch {}
    const existing = db.targetGroups.findIndex(g => g.jid === jid);
    if (existing >= 0) db.targetGroups[existing] = { jid, name };
    else {
      if (db.targetGroups.length >= 5) { await sock.sendMessage(jid, { text: '⚠️ You have already saved 5 groups. Use ,removegroup <number> to remove one before adding another.' }); return; }
      db.targetGroups.push({ jid, name });
    }
    if (!db.selectedGroupJid) db.selectedGroupJid = jid;
    saveDB();
    await sock.sendMessage(jid, { text: `✅ Target group saved: ${name}\n📌 Slot: ${db.targetGroups.findIndex(g => g.jid === jid) + 1}\nUse ,groups to view saved groups.` }); return;
  }
  if (command === ',groups') {
    const lines = db.targetGroups.map((g, i) => `${i + 1}. ${g.name}${g.jid === db.selectedGroupJid ? '  ← SELECTED' : ''}`).join('\n');
    await sock.sendMessage(jid, { text: '📋 *SAVED TARGET GROUPS*\n' + (lines || 'No groups saved yet. Add bot to a group and send ,setgroup there.') + '\n\nSelect: ,selectgroup <number>' }); return;
  }
  if (command === ',selectgroup') {
    const n = Number(args[0]);
    if (!Number.isInteger(n) || n < 1 || n > db.targetGroups.length) { await sock.sendMessage(jid, { text: 'Usage: ,selectgroup <number>\nUse ,groups to see saved groups.' }); return; }
    db.selectedGroupJid = db.targetGroups[n - 1].jid; saveDB();
    await sock.sendMessage(jid, { text: `✅ Selected target: ${db.targetGroups[n - 1].name}` }); return;
  }
  if (command === ',removegroup') {
    if (!isAdmin(sender)) { await sock.sendMessage(jid, { text: '⛔ Admin/Owner only command.' }); return; }
    const n = Number(args[0]);
    if (!Number.isInteger(n) || n < 1 || n > db.targetGroups.length) { await sock.sendMessage(jid, { text: 'Usage: ,removegroup <number>' }); return; }
    const removed = db.targetGroups.splice(n - 1, 1)[0];
    if (db.selectedGroupJid === removed.jid) db.selectedGroupJid = db.targetGroups[0]?.jid || '';
    saveDB(); await sock.sendMessage(jid, { text: `🗑️ Removed saved group: ${removed.name}` }); return;
  }
  if (command === '.speed' || command === ',speed') {
    if (!isAdmin(sender)) { await sock.sendMessage(jid, { text: '⛔ Admin/Owner only command.' }); return; }
    await runSpeedTest(sock, jid);
    return;
  }
  if (command === ',template') {
    if (!isAdmin(sender)) { await sock.sendMessage(jid, { text: '⛔ Admin/Owner only command.' }); return; }
    const rest = (trimmed.match(/^\S+\s*([\s\S]*)$/) || [])[1] || '';
    const sub = (rest.split(/\s/)[0] || '').toLowerCase();
    const afterSub = rest.slice(sub.length).trim();
    const kindOf = w => { w = String(w || '').toLowerCase(); return w === 'movie' ? 'movie' : (w === 'tv' || w === 'series') ? 'tv' : ''; };
    const q = contextInfo?.quotedMessage;
    const quotedText = (q?.conversation || q?.extendedTextMessage?.text || q?.imageMessage?.caption || q?.documentMessage?.caption || '').trim();
    const placeholders = TEMPLATE_VARS.map(v => '{' + v + '}').join(' ');
    const help = '🖼️ *POSTER TEMPLATE*\n'
      + ',template show movie|tv  → view the current template\n'
      + ',template movie <text>  → save the movie poster template\n'
      + ',template tv <text>  → save the TV poster template\n'
      + '(or reply to a message with ,template movie / ,template tv)\n'
      + ',template preview movie|tv  → see a sample\n'
      + ',template reset movie|tv|all  → back to the default\n\n'
      + 'Placeholders:\n' + placeholders + '\n\n'
      + 'A line whose placeholders are all empty is skipped automatically.\n'
      + 'Status: movie = ' + (db.templates?.movie ? 'custom' : 'default') + ', tv = ' + (db.templates?.tv ? 'custom' : 'default');
    if (!sub || sub === 'help') { await sock.sendMessage(jid, { text: help }); return; }
    if (sub === 'show') {
      const k = kindOf(afterSub.split(/\s/)[0]);
      if (!k) { await sock.sendMessage(jid, { text: 'Use: ,template show movie  or  ,template show tv' }); return; }
      await sock.sendMessage(jid, { text: `🖼️ Current ${k} template (${db.templates?.[k] ? 'custom' : 'default'}):` });
      await sock.sendMessage(jid, { text: getPosterTemplate(k) }); return;
    }
    if (sub === 'preview') {
      const k = kindOf(afterSub.split(/\s/)[0]);
      if (!k) { await sock.sendMessage(jid, { text: 'Use: ,template preview movie  or  ,template preview tv' }); return; }
      await sock.sendMessage(jid, { text: renderTemplate(getPosterTemplate(k), sampleTemplateVars(k)) }); return;
    }
    if (sub === 'reset') {
      const w = afterSub.split(/\s/)[0].toLowerCase();
      const kinds = w === 'all' ? ['movie', 'tv'] : kindOf(w) ? [kindOf(w)] : [];
      if (!kinds.length) { await sock.sendMessage(jid, { text: 'Use: ,template reset movie | tv | all' }); return; }
      db.templates ||= {};
      for (const k of kinds) delete db.templates[k];
      saveDB();
      await sock.sendMessage(jid, { text: '✅ [MPM] Template reset to default: ' + kinds.join(', ') }); return;
    }
    const k = kindOf(sub);
    if (!k) { await sock.sendMessage(jid, { text: help }); return; }
    const body = (afterSub || quotedText).replace(/\r/g, '').trim();
    if (!body) { await sock.sendMessage(jid, { text: `Send the template text after the command, or reply to a message that contains it.\nExample:\n,template ${k}\n🎬 {title} ({year})\n⭐ {rating_line}\n{storyline}\n\nSend ,template for the full help.` }); return; }
    if (body.length > TEMPLATE_MAX_CHARS) { await sock.sendMessage(jid, { text: `⚠️ Template is ${body.length} characters. The maximum is ${TEMPLATE_MAX_CHARS} (WhatsApp captions are limited).` }); return; }
    const unknown = [...new Set([...body.matchAll(/\{([A-Za-z0-9_]+)\}/g)].map(m => m[1]).filter(n => !TEMPLATE_VARS.includes(n)))];
    if (unknown.length) { await sock.sendMessage(jid, { text: '⚠️ Unknown placeholder(s): ' + unknown.map(n => '{' + n + '}').join(' ') + '\nValid ones:\n' + placeholders }); return; }
    db.templates ||= {};
    db.templates[k] = body;
    saveDB();
    await sock.sendMessage(jid, { text: `✅ [MPM] ${k} poster template saved. Sample:` });
    await sock.sendMessage(jid, { text: renderTemplate(body, sampleTemplateVars(k)) }); return;
  }
  if (command === ',check') {
    if (!isAdmin(sender)) { await sock.sendMessage(jid, { text: '⛔ Admin/Owner only command.' }); return; }
    const wait = await sock.sendMessage(jid, { text: '🩺 [MPM] Checking the bot… (about 10 seconds)' });
    let report;
    try { report = await runHealthCheck(sock); } catch (e) { report = '❌ Health check failed: ' + (e.message || e); }
    try { await sock.sendMessage(jid, { text: report, edit: wait.key }); }
    catch { await sock.sendMessage(jid, { text: report }); }
    return;
  }
  if (command === ',updel') {
    if (!isAdmin(sender)) { await sock.sendMessage(jid, { text: '⛔ Admin/Owner only command.' }); return; }
    if (jid.endsWith('@g.us')) { await sock.sendMessage(jid, { text: '🔒 Send ,updel to the bot in a private chat.' }); return; }
    if (downRunning) { await sock.sendMessage(jid, { text: '⏳ An upload is running. Wait for it to finish before deleting files.' }); return; }
    const files = scanDownFolder();
    if (!files.length) { await sock.sendMessage(jid, { text: '📂 [MPM] The `upload` folder is empty.' }); return; }
    const argText = args.join(' ').trim().toLowerCase();
    const usageMsg = '🗑️ *DELETE UPLOAD FILES*\n,updel 5  → delete file 5\n,updel 1 to 10  → files 1 to 10\n,updel 2 4 7  → files 2, 4 and 7\n,updel all  → delete every file\nSend ,uplist to see the numbers.';
    if (!argText) { await sock.sendMessage(jid, { text: usageMsg }); return; }
    const sel = argText === 'all' ? { indexes: files.map((_, i) => i) } : parseUpSelection(argText, files.length);
    if (sel.error === 'range') { await sock.sendMessage(jid, { text: `⚠️ The \`upload\` folder has only ${sel.total} file(s). Send ,uplist to see the numbers.` }); return; }
    if (sel.error) { await sock.sendMessage(jid, { text: usageMsg }); return; }
    const done = [], bad = [];
    for (const i of sel.indexes) {
      const f = files[i];
      try { await fs.promises.unlink(f.full); done.push(f); }
      catch (e) { bad.push(`${f.name} (${e.code || e.message})`); }
    }
    const freed = done.reduce((n, f) => n + f.size, 0);
    let out = `🗑️ *[MPM] DELETED*\n✅ Files deleted : *${done.length}*\n💾 Space freed : *${bytes(freed)}*`;
    if (bad.length) out += `\n❌ Failed (${bad.length}):\n` + bad.slice(0, 10).join('\n');
    out += '\n\nSend ,uplist to see what is left.';
    await sock.sendMessage(jid, { text: out }); return;
  }
  if (command === ',users') {
    if (!isAdmin(sender)) { await sock.sendMessage(jid, { text: '⛔ Admin/Owner only command.' }); return; }
    const rows = [];
    for (const [n, u] of Object.entries(db.users || {})) {
      if (isAdmin(n)) continue;
      const q = quotaInfo(u);
      if (!q.enabled) continue;
      const used = Math.min(u.quotaUsedBytes || 0, u.quotaBytes);
      rows.push({ n, q, u, used });
    }
    if (!rows.length) { await sock.sendMessage(jid, { text: '👥 [MPM] No users have a limit assigned yet. Use ,limit <size> <days> <number>.' }); return; }
    rows.sort((a, b) => (a.q.expired - b.q.expired) || (a.q.expiresAt - b.q.expiresAt));
    const MAX_SHOWN = 40;
    const lines = rows.slice(0, MAX_SHOWN).map((r, i) => {
      const state = r.q.expired ? (r.used >= r.u.quotaBytes ? '❌ data finished' : '❌ expired') : `🗓️ ${r.q.daysLeft} day(s) left`;
      return `${i + 1}. ${r.n}\n   📦 ${bytes(r.used)} / ${bytes(r.u.quotaBytes)}  •  ${state}`;
    });
    const active = rows.filter(r => !r.q.expired).length;
    let out = `╭─『 👥 *𝗠𝗣𝗠 𝗨𝗦𝗘𝗥𝗦* 』\n│ 👤 With limit : *${rows.length}*\n│ ✅ Active : *${active}*\n│ ❌ Expired / finished : *${rows.length - active}*\n╰──────────────────\n\n` + lines.join('\n');
    if (rows.length > MAX_SHOWN) out += `\n\n…and ${rows.length - MAX_SHOWN} more user(s).`;
    await sock.sendMessage(jid, { text: out }); return;
  }
  if (command === ',stats') {
    if (!isAdmin(sender)) { await sock.sendMessage(jid, { text: '⛔ Admin/Owner only command.' }); return; }
    const today = statsRange(1), week = statsRange(7), all = statsRange(60);
    if (!all.count) { await sock.sendMessage(jid, { text: '📊 [MPM] No download statistics yet. They start counting from the next download.' }); return; }
    const top = Object.entries(week.users).sort((a, b) => b[1] - a[1]).slice(0, 5)
      .map(([n, b], i) => `${i + 1}. ${n} — ${bytes(b)}`).join('\n') || '—';
    const withLimit = Object.values(db.users || {}).filter(u => quotaInfo(u).enabled && !quotaInfo(u).expired).length;
    const out = `╭─『 📊 *𝗠𝗣𝗠 𝗦𝗧𝗔𝗧𝗦* 』\n│ 📅 Today : *${today.count}* download(s) • *${bytes(today.bytes)}*\n│ 🗓️ Last 7 days : *${week.count}* • *${bytes(week.bytes)}*\n│ 📚 Last 60 days : *${all.count}* • *${bytes(all.bytes)}*\n│ 🎟️ Active limits : *${withLimit}*\n│ ⚙️ Running tasks : *${activeTasks.size}*\n╰──────────────────\n\n🏆 *Top users (7 days)*\n${top}`;
    await sock.sendMessage(jid, { text: out }); return;
  }
  if (command === ',uplist') {
    if (!isAdmin(sender)) { await sock.sendMessage(jid, { text: '⛔ Admin/Owner only command.' }); return; }
    if (jid.endsWith('@g.us')) { await sock.sendMessage(jid, { text: '🔒 Send ,uplist to the bot in a private chat.' }); return; }
    const files = scanDownFolder();
    if (!files.length) { await sock.sendMessage(jid, { text: '📂 [MPM] The `upload` folder is empty.' }); return; }
    const total = files.reduce((n, f) => n + f.size, 0);
    const MAX_SHOWN = 100;
    const lines = files.slice(0, MAX_SHOWN).map((f, i) => `${i + 1}. ${f.name}\n   ↳ ${bytes(f.size)}${f.settled ? '' : ' (still copying…)'}`);
    let out = `╭─『 📂 *𝗨𝗣𝗟𝗢𝗔𝗗 𝗙𝗢𝗟𝗗𝗘𝗥* 』\n│ 📦 Files : *${files.length}*\n│ 💾 Total size : *${bytes(total)}*\n╰──────────────────\n\n` + lines.join('\n');
    if (files.length > MAX_SHOWN) out += `\n\n…and ${files.length - MAX_SHOWN} more file(s).`;
    out += '\n\nSend ,up to upload all, or ,up 1 to 10 / ,up 5 to 9 to upload only a range.';
    await sock.sendMessage(jid, { text: out }); return;
  }
  if (command === ',up' || (command === 'up' && args.length === 0)) {
    if (!isAdmin(sender)) {
      if (command === ',up') await sock.sendMessage(jid, { text: '⛔ Admin/Owner only command.' });
      return;
    }
    if (jid.endsWith('@g.us')) {
      if (command === ',up') await sock.sendMessage(jid, { text: '🔒 Send ,up to the bot in a private chat.' });
      return;
    }
    await runDownFolderUpload(sock, jid, sender, args);
    return;
  }
  if (command === ',limit' || command === ',setlimit') {
    if (!admin) { await sock.sendMessage(jid, { text: '⛔ Admin only command.' }); return; }
    const size = parseSize(args[0]);
    const days = Number(args[1]);
    const target = normalizeNumber(args[2] || quotedTarget);
    if (!size || !Number.isInteger(days) || days < 1 || days > 3650 || !target || target === owner) {
      await sock.sendMessage(jid, { text: '⚙️ *SET USER LIMIT*\nUse: ,limit <size> <days> <number>\nExample: ,limit 20GB 30 94771234567\nOr reply to a user: ,limit 20GB 30\nCheck your own limit: ,limitcheck' }); return;
    }
    const u = usage(target);
    u.quotaBytes = size; u.quotaDays = days; u.quotaStartAt = Date.now(); u.quotaUsedBytes = 0;
    saveDB();
    await sock.sendMessage(jid, { text: `✅ *MPM LIMIT ASSIGNED*\n👤 User: ${target}\n📦 Limit: ${bytes(size)}\n🗓️ Duration: ${days} day(s)\n📊 Used: 0 B\n📥 Remaining: ${bytes(size)}\n⏳ Expires: ${new Date(u.quotaStartAt + days * 86400000).toLocaleString()}` }); return;
  }
  if (command === ',addlimit' || command === ',removelimit' || command === ',resetlimit') {
    if (!admin) { await sock.sendMessage(jid, { text: '⛔ Admin only command.' }); return; }
    const target = normalizeNumber(command === ',addlimit' ? args[2] : args[0] || quotedTarget);
    if (!target || target === owner) {
      const usageText = command === ',addlimit' ? 'Usage: ,addlimit <size> <days> <number>\nExample: ,addlimit 5GB 7 94771234567' : `Usage: ${command} <number>`;
      await sock.sendMessage(jid, { text: usageText }); return;
    }
    const u = usage(target);
    if (command === ',addlimit') {
      const extraBytes = parseSize(args[0]); const extraDays = Number(args[1]);
      if (!extraBytes || !Number.isInteger(extraDays) || extraDays < 1 || extraDays > 3650) {
        await sock.sendMessage(jid, { text: 'Usage: ,addlimit <size> <days> <number>\nExample: ,addlimit 5GB 7 94771234567' }); return;
      }
      const q = quotaInfo(u); const oldExpiry = q.enabled && !q.expired ? q.expiresAt : Date.now();
      u.quotaBytes = (q.enabled && !q.expired ? u.quotaBytes : 0) + extraBytes;
      const newExpiry = oldExpiry + extraDays * 86400000;
      u.quotaStartAt = Date.now(); u.quotaDays = Math.max(1, Math.ceil((newExpiry - Date.now()) / 86400000));
      saveDB();
      await sock.sendMessage(jid, { text: `✅ *DOWNLOAD LIMIT EXTENDED*\nUser: ${target}\nAdded quota: ${bytes(extraBytes)}\nAdded validity: ${extraDays} day(s)\nTotal quota: ${bytes(u.quotaBytes)}\nUsed: ${bytes(u.quotaUsedBytes)}\nRemaining: ${bytes(Math.max(0, u.quotaBytes-u.quotaUsedBytes))}\nNew expiry: ${new Date(newExpiry).toLocaleString()}` }); return;
    }
    if (command === ',removelimit') {
      u.quotaBytes = 0; u.quotaDays = 0; u.quotaStartAt = 0; u.quotaUsedBytes = 0;
      saveDB(); await sock.sendMessage(jid, { text: `✅ Download quota removed for ${target}.` }); return;
    }
    u.quotaUsedBytes = 0; saveDB();
    await sock.sendMessage(jid, { text: `✅ Download usage reset for ${target}.\n${quotaStatusText(u)}` }); return;
  }
  if (command === ',limitcheck' || command === ',mylimit' || command === ',checklimit') {
    const target = normalizeNumber(args[0] || quotedTarget || sender);
    if (target !== sender && !admin) { await sock.sendMessage(jid, { text: '⛔ Admin only: you can only check your own limit.' }); return; }
    const u = usage(target);
    await sock.sendMessage(jid, { text: `╭━━━『 *MPM USER LIMIT* 』━━━╮\n👤 User: ${target}\n${quotaStatusText(u)}\n\n📅 Today used: ${bytes(u.used || 0)}\n📥 Successful downloads today: ${u.count || 0}\n╰━━━━━━━━━━━━━━━━━━━━━━╯` }); return;
  }
  if (command === ',task') {
    await sock.sendMessage(jid, { text: activeTaskText(sender) }); return;
  }
  if (command === ',tasks') {
    if (!admin) { await sock.sendMessage(jid, { text: '⛔ Admin only command.' }); return; }
    await sock.sendMessage(jid, { text: activeTaskText() }); return;
  }
  if (command === ',com' || command === ',help' || command === ',menu') {
    const menu = buildMenuText(admin, owner);
    await sock.sendMessage(jid, { text: menu }); return;
  }
  if (command === ',status') {
    if (admin) {
      await sock.sendMessage(jid, { text: `╭━━━『 *MPM LIVE DASHBOARD* 』━━━╮\n👑 Role: ${isOwner(sender) ? 'OWNER' : 'ADMIN'}\n🟢 Bot: Online\n⚙️ Active tasks: ${activeTasks.size}\n👥 Admins: ${db.admins.length}\n🚫 Blocked users: ${db.blocked.length}\n🧠 Free RAM: ${bytes(os.freemem())}\n📦 Daily quota: ${CFG.dailyLimitBytes > 0 ? bytes(CFG.dailyLimitBytes) : 'Unlimited'}\n\n${activeTaskText()}\n╰━━━━━━━━━━━━━━━━━━━━━━━━╯` });
    } else {
      const u = usage(sender);
      await sock.sendMessage(jid, { text: `📊 *MPM ACCOUNT STATUS*\n${quotaStatusText(u)}\n\nToday used: ${bytes(u.used)} / ${CFG.dailyLimitBytes > 0 ? bytes(CFG.dailyLimitBytes) : 'Unlimited'}\nDownloads today: ${u.count}\nRole: User\n\nUse ,limitcheck to view this anytime.` });
    }
    return;
  }
  if (command === ',admin') {
    if (!isAdmin(sender)) {
      await sock.sendMessage(jid, { text: '⛔ Only the Owner or an Admin can use this command.' });
      return;
    }
    const target = quotedTarget || normalizeNumber(args[0] || '');
    if (!target) {
      await sock.sendMessage(jid, { text: '⚙️ To promote someone to Admin, reply to their message with ,admin.\nOr send ,admin 947XXXXXXXXX with their phone number.' });
      return;
    }
    if (target === owner) {
      await sock.sendMessage(jid, { text: '👑 This user is already the Owner.' });
      return;
    }
    if (db.admins.includes(target)) {
      await sock.sendMessage(jid, { text: `ℹ️ +${target} is already an Admin.` });
      return;
    }
    db.admins.push(target);
    saveDB();
    await sock.sendMessage(jid, { text: `✅ +${target} is now an MPM Bot Admin.\n👤 Promoted by: +${sender}` });
    return;
  }

  if (command === ',addadmin' || command === ',removeadmin' || command === ',admins' || command === ',block' || command === ',unblock') {
    if (!isAdmin(sender)) { await sock.sendMessage(jid, { text: '⛔ Admin/Owner only command.' }); return; }
    const target = normalizeNumber(args[0] || '');
    if (command === ',admins') {
      const adminLines = db.admins.length
        ? [`┠ Admins → ${db.admins.length}`, ...db.admins.map((n, i) => `┠ ${i + 1} → ${n}`)]
        : ['┠ Admins → No extra admins'];
      await sock.sendMessage(jid, { text: ['╔═══『 👑 𝗠𝗣𝗠 𝗔𝗗𝗠𝗜𝗡𝗦 』═══╗', `┟ Owner → ${owner || 'Not set'}`, ...adminLines].join('\n') });
      return;
    }
    if (!target || target === owner) { await sock.sendMessage(jid, { text: 'Usage: ' + command + ' 947XXXXXXXXX' }); return; }
    if (command === ',addadmin' && !db.admins.includes(target)) db.admins.push(target);
    if (command === ',removeadmin') db.admins = db.admins.filter(x => x !== target);
    if (command === ',block' && !db.blocked.includes(target)) db.blocked.push(target);
    if (command === ',unblock') db.blocked = db.blocked.filter(x => x !== target);
    saveDB(); await sock.sendMessage(jid, { text: '✅ [MPM] Updated: ' + command + ' ' + target }); return;
  }
  if (command === ',restart' || command === ',reboot') {
    if (!isAdmin(sender)) { await sock.sendMessage(jid, { text: '⛔ Admin/Owner only command.' }); return; }
    let msgTs = msg.messageTimestamp;
    msgTs = msgTs && typeof msgTs === 'object' && typeof msgTs.toNumber === 'function' ? msgTs.toNumber() : Number(msgTs || 0);
    if (msgTs && msgTs * 1000 < BOOT_TIME - 5000) return;
    const force = (args[0] || '').toLowerCase() === 'force';
    if (activeTasks.size > 0 && !force) {
      await sock.sendMessage(jid, { text: `⚠️ [MPM] ${activeTasks.size} task(s) are still running or queued. Restarting will stop them.\nSend *,restart force* to restart anyway, or wait for them to finish.` }); return;
    }
    try { saveDB(); } catch {}
    try { fs.writeFileSync(path.join(DATA_DIR, 'restart.json'), JSON.stringify({ jid, by: sender, at: Date.now() })); } catch {}
    await sock.sendMessage(jid, { text: '🔄 [MPM] Restarting the bot... it will be back in a few seconds.' }).catch(() => {});
    console.log('[restart] requested by', sender);
    setTimeout(relaunchAndExit, 1500);
    return;
  }
  if (command === ',cancelall') {
    if (!isAdmin(sender)) { await sock.sendMessage(jid, { text: '⛔ Admin/Owner only command.' }); return; }
    cancelAllVersion++;
    const tasks = [...activeTasks.entries()];
    for (const [key, task] of tasks) cancelTask(key, task);
    await sock.sendMessage(jid, { text: `🛑 [MPM] Cancel-all requested. ${tasks.length} task(s) stopped or removed from the queue.` }); return;
  }
  if (command === ',cancel') {
    const mine = [...activeTasks.entries()].filter(([, t]) => t.jid === jid && t.sender === sender);
    const choice = (args[0] || '').toLowerCase().replace(/^#/, '');
    const describe = (t) => `#${t.id} • ${t.phase === 'queued' ? '⏳ Waiting in queue' : '▶️ ' + String(t.phase)}\n   ${t.label || t.file || 'Task'}${t.phase !== 'queued' && t.progress ? '\n   Progress: ' + t.progress : ''}`;
    if (!mine.length && !(admin && (/^\d+$/.test(choice) || choice === 'all'))) { await sock.sendMessage(jid, { text: 'ℹ️ You have no active tasks.' }); return; }

    if (choice === 'all') {
      const targets = admin ? [...activeTasks.entries()] : mine;
      for (const [key, t] of targets) cancelTask(key, t);
      await sock.sendMessage(jid, { text: `🛑 [MPM] Cancelling all ${admin ? '' : 'your '}tasks (${targets.length}).` }); return;
    }
    if (/^\d+$/.test(choice)) {
      const pool = admin ? [...activeTasks.entries()] : mine;
      const found = pool.find(([, t]) => t.id === Number(choice));
      if (!found) { await sock.sendMessage(jid, { text: `⚠️ Task #${choice} was not found (it may have finished already). Send ,cancel to see the current list.` }); return; }
      const [key, t] = found;
      const wasQueued = t.phase === 'queued';
      const name = t.label || t.file || 'task';
      cancelTask(key, t);
      await sock.sendMessage(jid, { text: wasQueued ? `🛑 [MPM] Task #${t.id} removed from the queue.\n${name}` : `🛑 [MPM] Cancelling task #${t.id}…\n${name}` }); return;
    }
    if (mine.length === 1) {
      const [key, t] = mine[0];
      const wasQueued = t.phase === 'queued';
      cancelTask(key, t);
      await sock.sendMessage(jid, { text: wasQueued ? `🛑 [MPM] Task #${t.id} removed from the queue.` : `🛑 [MPM] Cancelling task #${t.id}…` }); return;
    }
    await sock.sendMessage(jid, { text: `🛑 [MPM] You have ${mine.length} tasks. Which one do you want to cancel?\n\n` + mine.map(([, t]) => describe(t)).join('\n\n') + `\n\n👉 ,cancel <id>   (example: ,cancel ${mine[0][1].id})\n👉 ,cancel all   (cancel everything above)` }); return;
  }
  if (command === ',torrent' || command === ',magnet') {
    const urlIndex = args.findIndex(part => /^(?:magnet:\?xt=urn:btih:|https?:\/\/)/i.test(part));
    const customPrefix = (urlIndex >= 0 ? args.slice(0, urlIndex) : args).join(' ').trim();
    let torrentInput = (urlIndex >= 0 ? args.slice(urlIndex) : []).join(' ').trim();
    if (command === ',magnet' && !/^magnet:\?xt=urn:btih:/i.test(torrentInput)) {
      await sock.sendMessage(jid, { text: 'Usage: ,magnet [PREFIX] magnet:?xt=urn:btih:...' }); return;
    }
    let torrentAttachment = false;
    if (!torrentInput && msg.message.documentMessage) {
      const mime = msg.message.documentMessage.mimetype || '';
      const name = msg.message.documentMessage.fileName || 'file.torrent';
      if (!/\.torrent$/i.test(name) && !/bittorrent/i.test(mime)) {
        await sock.sendMessage(jid, { text: 'Please attach a .torrent file with caption ,torrent.' }); return;
      }
      torrentAttachment = true;
    }
    if (!torrentInput && !torrentAttachment) {
      await sock.sendMessage(jid, { text: 'Usage:\n,torrent [PREFIX] <magnet link or .torrent URL>\n,magnet [PREFIX] <magnet link>\nExample: ,torrent [MPM] https://example.com/file.torrent\nExample: ,magnet [MPM] magnet:?xt=urn:btih:...\nOr attach a .torrent file with caption: ,torrent [MPM]' }); return;
    }
    let attachmentBuffer = null;
    if (torrentAttachment) {
      try {
        attachmentBuffer = await downloadMediaMessage(msg, 'buffer', {});
        if (!Buffer.isBuffer(attachmentBuffer) || !attachmentBuffer.length || attachmentBuffer.length > 5*1024*1024) throw new Error('Invalid or oversized .torrent attachment (max 5 MB).');
      } catch (e) { await sock.sendMessage(jid, { text: '❌ [MPM] ' + friendlyError(e) }); return; }
    }
    const torrentLabel = torrentAttachment ? taskLabel(msg.message.documentMessage?.fileName || 'Torrent file') : taskLabel(torrentInput);
    const { task, start } = launchJob(sock, { type: 'torrent', jid, sender, senderName: msg.pushName || '', label: torrentLabel, customPrefix, input: torrentInput, attachment: torrentAttachment, torrentBuffer: attachmentBuffer });
    await sock.sendMessage(jid, { text: `🧲 [MPM] Torrent task #${task.id} added to queue. Make sure aria2 is installed on the host.` });
    start();
    return;
  }
  if (command === ',gofile') {
    if (jid.endsWith('@g.us')) { await sock.sendMessage(jid, { text: '🔒 Send the ,gofile command to the bot in a private chat.' }); return; }
    const targetGroup = db.targetGroups.find(g => g.jid === db.selectedGroupJid);
    if (!targetGroup) { await sock.sendMessage(jid, { text: '⚠️ No target group selected. Send ,setgroup in a group, then use ,selectgroup 1. Use ,groups to view saved groups.' }); return; }
    const gofileUrls = extractUrls(args.join(' '));
    if (gofileUrls.length !== 1 || !gofileContentId(gofileUrls[0])) { await sock.sendMessage(jid, { text: 'Usage: ,gofile https://gofile.io/d/xxxxx' }); return; }
    const sourceJid = jid;
    const { task, start } = launchJob(sock, { type: 'gofile', jid: sourceJid, sender, senderName: msg.pushName || '', label: 'Gofile: ' + taskLabel(gofileUrls[0]), url: gofileUrls[0], targetJid: targetGroup.jid, targetName: targetGroup.name, doneIds: [] });
    await sock.sendMessage(sourceJid, { text: `📋 [MPM] Gofile task #${task.id} queued.\n📤 Destination: ${targetGroup.name}\n📨 Progress and errors will appear here; files only go to the selected group.` });
    start();
    return;
  }
  if (command !== ',dl' && command !== ',dl1' && command !== ',dlr' && command !== ',rename' && command !== ',zip' && command !== ',unzip') return;
  let customPrefix = '';
  let linkText = args.join(' ');
  let renameTo = '';
  let extractZip = command === ',zip' || command === ',unzip';
  if (command === ',rename') {
    const m = linkText.match(/^\[([^\]]{1,150})\]\s*(.*)$/);
    if (m) { renameTo = m[1].trim(); linkText = m[2]; }
    else { const ix = linkText.search(/https?:\/\//i); if (ix > 0) { renameTo = linkText.slice(0, ix).trim().replace(/^\[|\]$/g, ''); linkText = linkText.slice(ix); } }
    if (!renameTo) { await sock.sendMessage(jid, { text: 'Usage: ,rename [New Name] <link>' }); return; }
  }
  if (command === ',dlr' || command === ',zip' || command === ',unzip') {
    const prefixMatch = linkText.match(/^\[([^\]]{1,40})\]\s*/);
    if (prefixMatch) {
      customPrefix = prefixMatch[1].trim();
      linkText = linkText.slice(prefixMatch[0].length);
    } else {
      const firstSpace = linkText.search(/\s/);
      if (firstSpace > 0 && !/^https?:\/\//i.test(linkText)) {
        customPrefix = linkText.slice(0, firstSpace).trim();
        linkText = linkText.slice(firstSpace).trim();
      }
    }
    customPrefix = customPrefix.replace(/[\\/<>:"|?*\x00-\x1F]/g, '_').slice(0, 40);
    if (!customPrefix) {
      await sock.sendMessage(jid, { text: 'Usage: ,dlr [MPM] <link> or ,zip [MPM-EZI] <link>' });
      return;
    }
  }
  const urls = extractUrls(linkText);
  if (!urls.length) {
    await sock.sendMessage(jid, { text: 'Usage: ,dl <link> / ,dl1 <link> / ,rename [Name] <link> / ,zip [PREFIX] <link>' });
    return;
  }
  if (urls.length > CFG.maxLinksPerMessage) {
    await sock.sendMessage(jid, { text: 'Maximum ' + CFG.maxLinksPerMessage + ' links per message.' }); return;
  }
  const { task, start } = launchJob(sock, { type: 'dl', jid, sender, senderName: msg.pushName || '', label: taskLabel(urls[0], urls.length - 1), command, customPrefix, renameTo, extractZip, urls, doneCount: 0, sentCount: 0, totalCount: 0 });
  await sock.sendMessage(jid, { text: '📋 [MPM] Added ' + urls.length + ' link(s) to queue.\n🆔 Task #' + task.id + '  (cancel it with ,cancel ' + task.id + ')' });
  start();
}

// ---- Jobs: everything that goes in the queue is a plain record (saved in data/queue.json) + a runner ------
function launchJob(sock, rec, restored = false) {
  const { key: taskId, task } = registerTask(rec.jid, rec.sender, rec.label, rec.senderName, restored ? rec.id : 0);
  rec.id = task.id; task.job = rec;
  if (rec.torrentBuffer) {
    try {
      const f = path.join(QUEUE_FILES_DIR, 't' + task.id + '.torrent');
      fs.writeFileSync(f, rec.torrentBuffer); rec.input = f;
    } catch (e) { console.error('[queue] could not save torrent file:', e && e.message); }
    delete rec.torrentBuffer;
  }
  persistedJobs.set(task.id, rec); persistJobs();
  const start = () => {
    if (rec.type === 'dl') enqueue(rec.jid, () => runDlJob(sock, rec, taskId, task));
    else if (rec.type === 'torrent') enqueueTask(rec.jid, () => runTorrentJob(sock, rec, taskId, task));
    else if (rec.type === 'gofile') enqueueTask(rec.jid, () => runGofileJob(sock, rec, taskId, task));
    else if (rec.type === 'fitgirl') enqueueTask(rec.jid, () => runFitGirlJob(sock, rec, taskId, task));
    else endTask(taskId, task);
  };
  return { task, start };
}
async function runDlJob(sock, rec, taskId, task) {
  const { jid, sender, command, customPrefix, renameTo, extractZip, urls } = rec;
  if (task.cancelled) { endTask(taskId, task); return; }
  const controller = task.controller;
  task.phase = 'starting';
  try {
    let total = rec.totalCount || 0, sent = rec.sentCount || 0;
    for (let i = rec.doneCount || 0; i < urls.length; i++) {
      if (task.cancelled) break;
      try {
        if (gofileContentId(urls[i])) {
          const result = await processGofileFolder(sock, jid, sender, urls[i], isAdmin(sender), customPrefix, command === ',dl1' ? '[MPM]' : '', jid, task);
          total += result.total; sent += result.sent;
        } else {
          total++;
          const srcUrl = urls[i];
          const opts = { customPrefix, addPrefix: command === ',dl1', signal: controller.signal, task };
          if (renameTo) { opts.fileName = renameTo; opts.addPrefix = false; }
          if (extractZip) { const count = await extractAndUploadZip(sock, jid, sender, srcUrl, isAdmin(sender), customPrefix || 'MPM-EZI', task); total += Math.max(0, count - 1); sent += count; }
          else { await downloadOneWithRetry(sock, jid, sender, srcUrl, isAdmin(sender), opts); sent++; }
        }
      }
      catch (e) {
        if (task.cancelled) break;
        console.error('[download failed]', urls[i], '-', (e && e.message) || e);
        task.phase = 'failed'; task.progress = friendlyError(e);
        await sock.sendMessage(jid, { text: '❌ [MPM] Failed: ' + friendlyError(e) + (e && e.attempts > 1 ? '\n(Tried ' + e.attempts + ' times.)' : '') }).catch(() => {});
      }
      rec.doneCount = i + 1; rec.sentCount = sent; rec.totalCount = total; persistJobs();
    }
    await sock.sendMessage(jid, { text: task.cancelled ? '🛑 [MPM] Task cancelled.' : `✅ [MPM] Download completed. Sent ${sent}/${total} file(s).\n🏁 [MPM] Queue finished.` });
  } finally { endTask(taskId, task); }
}
async function runTorrentJob(sock, rec, taskId, task) {
  const { jid, sender, customPrefix } = rec;
  if (task.cancelled) { endTask(taskId, task); return; }
  task.phase = 'starting';
  try {
    const n = await runTorrentDownload(sock, jid, sender, rec.input, isAdmin(sender), task, customPrefix);
    await sock.sendMessage(jid, { text: task.cancelled ? '🛑 [MPM] Torrent cancelled.' : `✅ [MPM] Torrent finished. Uploaded ${n} file(s).` });
  } catch (e) { await sock.sendMessage(jid, { text: task.cancelled ? '🛑 [MPM] Torrent cancelled.' : '❌ [MPM] Torrent failed: ' + friendlyError(e) }).catch(() => {}); }
  finally { endTask(taskId, task); }
}
async function runGofileJob(sock, rec, taskId, task) {
  const { jid, sender } = rec;
  if (task.cancelled) { endTask(taskId, task); return; }
  task.phase = 'starting';
  try {
    const result = await processGofileFolder(sock, jid, sender, rec.url, isAdmin(sender), '', '', rec.targetJid, task);
    if (task.cancelled) { await sock.sendMessage(jid, { text: '🛑 [MPM] Gofile task cancelled.' }); return; }
    await sock.sendMessage(jid, { text: `✅ [MPM] Gofile finished. Sent ${result.sent}/${result.total} file(s) to ${rec.targetName || 'the group'}.` });
  } catch (e) {
    await sock.sendMessage(jid, { text: task.cancelled ? '🛑 [MPM] Gofile task cancelled.' : '❌ [MPM] Gofile failed: ' + friendlyError(e) }).catch(() => {});
  } finally { endTask(taskId, task); }
}

// ---- FitGirl: selective torrent -> downloads/<RAR Name>/Selected Files & RAR Parts -> WhatsApp --------
function getAutoFitGirlPartMb(totalBytes) {
  const gb = totalBytes / (1024 ** 3);
  if (gb < 10) return { partMb: 1024, label: '1 GB' };
  if (gb < 20) return { partMb: 1536, label: '1.5 GB' };
  return { partMb: 1900, label: '1.9 GB' };
}

async function getDirTotalBytes(dirPath) {
  let total = 0;
  for (const ent of await fs.promises.readdir(dirPath, { withFileTypes: true })) {
    const full = path.join(dirPath, ent.name);
    if (ent.isSymbolicLink()) continue;
    if (ent.isDirectory()) total += await getDirTotalBytes(full);
    else if (ent.isFile()) total += (await fs.promises.stat(full)).size;
  }
  return total;
}

const MPM_GAMING_PREFIX = '[MPM-Gaming] ';
// Makes sure the game's root folder inside `Selected Files` is named "[MPM-Gaming] <Root Name>".
// - one root folder from the torrent  -> renamed to "[MPM-Gaming] <torrent folder name>"
// - loose files / several entries     -> wrapped into "[MPM-Gaming] <fallbackName>"
async function applyMpmGamingRootName(destDir, fallbackName) {
  const entries = await fs.promises.readdir(destDir, { withFileTypes: true });
  if (!entries.length) return null;
  if (entries.length === 1 && entries[0].isDirectory()) {
    const old = entries[0].name;
    if (old.startsWith(MPM_GAMING_PREFIX)) return old;
    const fresh = MPM_GAMING_PREFIX + old;
    await fs.promises.rename(path.join(destDir, old), path.join(destDir, fresh));
    return fresh;
  }
  const wrapName = MPM_GAMING_PREFIX + String(fallbackName || 'Game').replace(/[\\/:*?"<>|]+/g, '_').trim();
  const wrapDir = path.join(destDir, wrapName);
  await fs.promises.mkdir(wrapDir, { recursive: true });
  for (const ent of entries) {
    if (ent.name === wrapName) continue;
    await fs.promises.rename(path.join(destDir, ent.name), path.join(wrapDir, ent.name));
  }
  return wrapName;
}

// Copies every file/folder from BOT/mpm/ into the downloaded FitGirl game folder before RAR splitting.
async function copyMpmFilesToDir(destDir) {
  if (!fs.existsSync(MPM_DIR)) return 0;
  const entries = await fs.promises.readdir(MPM_DIR, { withFileTypes: true });
  if (!entries.length) return 0;
  let targetDir = destDir;
  const destEntries = await fs.promises.readdir(destDir, { withFileTypes: true });
  if (destEntries.length === 1 && destEntries[0].isDirectory()) {
    targetDir = path.join(destDir, destEntries[0].name);
  }
  let copied = 0;
  const copyRec = async (src, dst) => {
    await fs.promises.mkdir(dst, { recursive: true });
    for (const ent of await fs.promises.readdir(src, { withFileTypes: true })) {
      const s = path.join(src, ent.name);
      const d = path.join(dst, ent.name);
      if (ent.isDirectory()) await copyRec(s, d);
      else if (ent.isFile()) { await fs.promises.copyFile(s, d); copied++; }
    }
  };
  await copyRec(MPM_DIR, targetDir);
  return copied;
}

async function splitDirectoryToRarParts(sourceDir, outDir, archiveBaseName, partMb, task) {
  await fs.promises.mkdir(outDir, { recursive: true });
  const rarBin = await findTool([
    'rar',
    path.join(ROOT, 'winrar', 'Rar.exe'),
    'C:\\Program Files\\WinRAR\\Rar.exe',
    'C:\\Program Files (x86)\\WinRAR\\Rar.exe'
  ]);
  if (!rarBin) throw new Error('WinRAR (Rar.exe) was not found. Run install-winrar.ps1 first.');

  const safeBase = String(archiveBaseName || 'FitGirl_Game').replace(/[\\/:*?"<>|]+/g, '_').trim().slice(0, 120) || 'FitGirl_Game';
  const archiveTarget = path.join(outDir, `${safeBase}.rar`);
  // Run RAR from inside `Selected Files` and add its top-level entries by name (no -ep1),
  // so the game folder itself is stored in the archive and extracting gives <GameFolder>/...
  const topEntries = await fs.promises.readdir(sourceDir);
  if (!topEntries.length) throw new Error('Nothing to archive: the Selected Files folder is empty.');
  const args = ['a', '-r', '-m0', `-v${partMb}m`, '-y', '-idq', archiveTarget, '--', ...topEntries];
  await runTool(rarBin, args, task, sourceDir);

  const names = (await fs.promises.readdir(outDir))
    .filter(n => n.toLowerCase().endsWith('.rar'))
    .sort((a, b) => a.localeCompare(b, undefined, { numeric: true, sensitivity: 'base' }));
  return names.map(n => ({ file: path.join(outDir, n), name: n }));
}

async function runFitGirlTorrentAndUpload(sock, jid, sender, input, admin, task, customPrefix = '') {
  const u = usage(sender);
  const assigned = admin ? null : quotaInfo(u);
  if (!admin && assigned?.enabled && assigned.expired) throw new Error('Your assigned limit is expired or fully used.');
  if (!admin && CFG.dailyLimitBytes > 0 && u.used >= CFG.dailyLimitBytes) throw new Error('Daily quota used.');

  const localTorrent = typeof input === 'string' && /\.torrent$/i.test(input) && fs.existsSync(input);
  if (!input || !(localTorrent || /^(magnet:\?xt=urn:btih:|https?:\/\/)/i.test(input))) {
    throw new Error('Send a valid FitGirl magnet link or .torrent file/URL.');
  }

  const selectFile = String(task?.job?.selectFile || '').trim();
  const selectedPaths = Array.isArray(task?.job?.selectedPaths) ? task.job.selectedPaths : null;

  // Folder structure: BOT/downloads/<RAR Name>/Selected Files & RAR Parts
  const folderName = safeName(customPrefix || task.label || ('fg-t' + task.id), false);
  const fgBaseDir = path.join(DL_DIR, folderName);
  const dlWork = path.join(fgBaseDir, 'Selected Files');
  const rarWork = path.join(fgBaseDir, 'RAR Parts');

  if (!(task?.job?.restarts > 0)) {
    await fs.promises.rm(dlWork, { recursive: true, force: true }).catch(() => {});
    await fs.promises.rm(rarWork, { recursive: true, force: true }).catch(() => {});
  }
  await fs.promises.mkdir(dlWork, { recursive: true });
  await fs.promises.mkdir(rarWork, { recursive: true });
  await fetcher.ensureDisk(DL_DIR, 0, DISK_RESERVE);

  task.phase = 'downloading';
  task.file = selectFile ? `Selected files (${task.job?.selectedCount || 'custom'})` : 'FitGirl torrent metadata';
  task.progress = 'Starting';
  task.source = 'FitGirl Torrent';

  const progress = await createProgressReporter(sock, jid, '🧲 [MPM] Starting FitGirl torrent download…');
  let child;
  let finished = false;

  try {
    await new Promise((resolve, reject) => {
      const args = [
        '--enable-color=false', '--dir', dlWork, '--continue=true', '--seed-time=0',
        '--max-tries=5', '--retry-wait=5', '--summary-interval=3', '--console-log-level=notice',
        '--file-allocation=none', '--bt-stop-timeout=30', '--allow-overwrite=true'
      ];
      if (selectFile) {
        args.push(`--select-file=${selectFile}`, '--bt-remove-unselected-file=true');
      }
      args.push(input);
      child = spawn('aria2c', args, { windowsHide: true, stdio: ['ignore', 'pipe', 'pipe'] });
      task.process = child;

      let stderr = '', last = 0, outBuf = '', lastDisk = 0, diskStop = '';
      const tStart = Date.now();
      const unitBytes = t => {
        const m = String(t || '').match(/^([\d.]+)\s*([KMGT]?)i?B?$/i);
        if (!m) return 0;
        const idx = 'KMGT'.indexOf((m[2] || '').toUpperCase());
        return Number(m[1]) * (idx >= 0 ? 1024 ** (idx + 1) : 1);
      };
      const etaSec = t => {
        const m = String(t || '').match(/^(?:(\d+)d)?(?:(\d+)h)?(?:(\d+)m)?(?:(\d+)s)?$/i);
        return m && t ? (+m[1] || 0) * 86400 + (+m[2] || 0) * 3600 + (+m[3] || 0) * 60 + (+m[4] || 0) : NaN;
      };

      child.stderr.on('data', chunk => { stderr = (stderr + chunk.toString()).slice(-5000); });
      child.stdout.on('data', chunk => {
        outBuf = (outBuf + chunk.toString()).slice(-3000);
        const now = Date.now();
        if (now - lastDisk > 10000) {
          lastDisk = now;
          fetcher.freeDiskBytes(DL_DIR).then(free => {
            if (!diskStop && free < Math.floor(DISK_RESERVE / 2)) {
              diskStop = '💾 Not enough disk space on the bot server (' + fetcher.fmtBytes(free) + ' free). FitGirl download stopped.';
              try { child.kill('SIGTERM'); } catch {}
            }
          }).catch(() => {});
        }
        if (now - last < 2500) return;
        const all = [...outBuf.matchAll(/\[#\w+\s+([\d.]+\w*)\/([\d.]+\w*)(?:\((\d+)%\))?(?:\s+CN:(\d+))?(?:\s+SD:\d+)?(?:\s+DL:([\d.]+\w*))?(?:\s+ETA:(\w+))?/g)];
        const m = all[all.length - 1];
        if (!m) return;
        last = now;
        const done = unitBytes(m[1]), total = unitBytes(m[2]);
        const pct = total > 0 ? Math.min(99.99, (done / total) * 100) : NaN;
        task.progress = Number.isFinite(pct) ? pct.toFixed(1) + '%' : bytes(done);
        task.speed = cardSize(unitBytes(m[5])) + '/s';
        progress.update(mpmCard(task, {
          phase: 'download', pct, done, total, speed: unitBytes(m[5]),
          peers: m[4] !== undefined ? Number(m[4]) : null, elapsed: (now - tStart) / 1000, eta: etaSec(m[6])
        })).catch(() => {});
      });

      child.once('error', err => reject(err.code === 'ENOENT' ? new Error('aria2c is not installed.') : err));
      child.once('close', code => {
        if (diskStop) return reject(new Error(diskStop));
        code === 0 ? resolve() : reject(new Error('aria2c failed (' + code + '): ' + (stderr.trim().split(/\r?\n/).slice(-2).join(' ') || 'Torrent download failed.')));
      });
    });
    task.process = null;

    if (task.cancelled) throw new Error('Task cancelled by user.');

    // Extra safety: remove any unselected boundary files left behind by aria2c
    if (selectedPaths && selectedPaths.length) {
      const allowed = new Set(selectedPaths);
      const pruneUnselected = async (dir) => {
        const entries = await fs.promises.readdir(dir, { withFileTypes: true });
        for (const ent of entries) {
          const full = path.join(dir, ent.name);
          if (ent.isDirectory()) {
            await pruneUnselected(full);
            const left = await fs.promises.readdir(full).catch(() => []);
            if (!left.length) await fs.promises.rmdir(full).catch(() => {});
          } else if (ent.isFile()) {
            const rel = path.relative(dlWork, full).split(path.sep).join('/');
            if (!allowed.has(rel)) await fs.promises.rm(full, { force: true }).catch(() => {});
          }
        }
      };
      await pruneUnselected(dlWork);
    }

    // Root folder inside the RAR must be "[MPM-Gaming] <Root Name>"
    const rootName = await applyMpmGamingRootName(dlWork, customPrefix || task.label);
    if (rootName) console.log(`[fg] root folder: ${rootName}`);

    // Add extra files from BOT/mpm/ into the downloaded game folder before creating RAR parts
    const mpmCopied = await copyMpmFilesToDir(dlWork);
    if (mpmCopied > 0) console.log(`[fg] added ${mpmCopied} file(s) from mpm/ into ${dlWork}`);

    const totalGameBytes = await getDirTotalBytes(dlWork);
    if (!totalGameBytes) throw new Error('Torrent finished, but no downloaded game files were found.');

    const { partMb, label } = getAutoFitGirlPartMb(totalGameBytes);
    // RAR file name also starts with "[MPM-Gaming] " -> "[MPM-Gaming] <name>.part1.rar"
    const rawArchiveTitle = safeName(customPrefix || task.label, false);
    const baseArchiveTitle = rawArchiveTitle.startsWith(MPM_GAMING_PREFIX) ? rawArchiveTitle : MPM_GAMING_PREFIX + rawArchiveTitle;

    await fetcher.ensureDisk(DL_DIR, totalGameBytes, DISK_RESERVE);

    task.phase = 'splitting';
    task.file = baseArchiveTitle;
    task.progress = 'splitting';
    const partsInfo = Math.ceil(totalGameBytes / (partMb * 1048576));
    await sock.sendMessage(jid, { text: '🗜️ [MPM] Creating RAR *' + baseArchiveTitle + '*: ' + partsInfo + ' parts × ' + partMb + ' MB, please wait…' }).catch(() => {});

    const rarStart = Date.now(); let lastDone = 0, lastTick = rarStart, stopMon = false;
    const tickMs = Math.max(3, Number(CFG.progressIntervalSeconds) || 5) * 1000;
    const showRar = async (done, final) => {
      const now = Date.now();
      const speed = Math.max(0, done - lastDone) / Math.max(0.5, (now - lastTick) / 1000);
      lastDone = done; lastTick = now;
      const el = (now - rarStart) / 1000;
      const avg = done / Math.max(1, el);
      try {
        await progress.update(mpmCard(task, {
          phase: 'rar', pct: final ? 100 : Math.min(99.9, done / totalGameBytes * 100), done: Math.min(done, totalGameBytes), total: totalGameBytes,
          speed: final ? avg : speed, elapsed: el, eta: final ? 0 : (avg > 0 ? Math.max(0, (totalGameBytes - done) / avg) : NaN),
          parts: partsInfo, file: baseArchiveTitle
        }));
      } catch {}
    };
    const dirSize = async () => { let t = 0; try { for (const n of await fs.promises.readdir(rarWork)) { try { t += (await fs.promises.stat(path.join(rarWork, n))).size; } catch {} } } catch {} return t; };
    const monitor = (async () => {
      await showRar(0, false);
      while (!stopMon) {
        for (let w = 0; w < tickMs && !stopMon; w += 500) await new Promise(r => setTimeout(r, 500));
        if (stopMon) break;
        await showRar(await dirSize(), false);
      }
    })();
    let parts;
    try { parts = await splitDirectoryToRarParts(dlWork, rarWork, baseArchiveTitle, partMb, task); }
    finally { stopMon = true; await monitor.catch(() => {}); }
    await showRar(totalGameBytes, true);
    if (task.cancelled) throw new Error('Task cancelled by user.');
    if (!parts.length) throw new Error('RAR splitting produced no output parts.');

    await fs.promises.rm(dlWork, { recursive: true, force: true }).catch(() => {});

    task.phase = 'uploading';
    let sent = 0;
    for (let i = 0; i < parts.length; i++) {
      if (task.cancelled) break;
      const part = parts[i];
      const pSize = (await fs.promises.stat(part.file)).size;
      task.file = part.name;
      task.progress = `${i + 1}/${parts.length}`;
      await waitUploadGap(task);
      if (task.cancelled) break;
      try {
        await uploadWithCard(
          progress, task,
          { size: pSize, file: `Part ${i + 1}/${parts.length} • ${cardShort(part.name)}` },
          () => sock.sendMessage(jid, { document: { url: part.file }, fileName: part.name, mimetype: 'application/x-rar-compressed' })
        );
      } finally { markUploadDone(); }
      sent++;
      await fs.promises.rm(part.file, { force: true });
    }

    if (!admin && sent > 0) {
      const uNow = usage(sender);
      uNow.used = (uNow.used || 0) + totalGameBytes;
      uNow.quotaUsedBytes = (uNow.quotaUsedBytes || 0) + totalGameBytes;
      uNow.count = (uNow.count || 0) + 1;
      recordStats(sender, totalGameBytes);
      saveDB();
    }

    await sock.sendMessage(jid, { text: '✅ [MPM] Sent ' + sent + ' parts (RAR) for ' + baseArchiveTitle + ' (' + label + ' per part, total ' + bytes(totalGameBytes) + ').\n' + splitHowTo('RAR') });
    finished = true;
    return sent;
  } finally {
    if (child && !child.killed && task.cancelled) { try { child.kill('SIGTERM'); } catch {} }
    task.process = null;
    if (finished || task.cancelled || task.phase !== 'downloading') {
      await fs.promises.rm(dlWork, { recursive: true, force: true }).catch(() => {});
    }
    await fs.promises.rm(rarWork, { recursive: true, force: true }).catch(() => {});
    await fs.promises.rmdir(fgBaseDir).catch(() => {});
  }
}

async function runFitGirlJob(sock, rec, taskId, task) {
  const { jid, sender, customPrefix } = rec;
  if (task.cancelled) { endTask(taskId, task); return; }
  task.phase = 'starting';
  try {
    const n = await runFitGirlTorrentAndUpload(sock, jid, sender, rec.input, isAdmin(sender), task, customPrefix);
    await sock.sendMessage(jid, {
      text: task.cancelled ? '🛑 [MPM] FitGirl task cancelled.' : `✅ [MPM] FitGirl task complete. Uploaded ${n} RAR part(s).`
    });
  } catch (e) {
    await sock.sendMessage(jid, {
      text: task.cancelled ? '🛑 [MPM] FitGirl task cancelled.' : '❌ [MPM] FitGirl task failed: ' + friendlyError(e)
    }).catch(() => {});
  } finally { endTask(taskId, task); }
}

function fgBdecode(buf) {
  let i = 0, infoStart = -1, infoEnd = -1;
  const str = () => {
    const colon = buf.indexOf(0x3a, i);
    const len = Number(buf.toString('latin1', i, colon));
    if (!Number.isFinite(len) || colon < 0) throw new Error('bad torrent data');
    const out = buf.subarray(colon + 1, colon + 1 + len);
    i = colon + 1 + len;
    return out;
  };
  const parse = depth => {
    const c = buf[i];
    if (c === 0x69) { const e = buf.indexOf(0x65, i); const n = Number(buf.toString('latin1', i + 1, e)); i = e + 1; return n; }
    if (c === 0x6c) { i++; const a = []; while (buf[i] !== 0x65) a.push(parse(depth + 1)); i++; return a; }
    if (c === 0x64) {
      i++; const o = {};
      while (buf[i] !== 0x65) {
        const k = str().toString('latin1'); const start = i; const v = parse(depth + 1);
        if (depth === 0 && k === 'info') { infoStart = start; infoEnd = i; }
        o[k] = v;
      }
      i++; return o;
    }
    if (c >= 0x30 && c <= 0x39) return str();
    throw new Error('bad torrent data');
  };
  const root = parse(0);
  return { root, infoRaw: infoStart >= 0 ? buf.subarray(infoStart, infoEnd) : null };
}

function fgParseTorrent(buf) {
  const { root, infoRaw } = fgBdecode(buf);
  const info = root.info;
  if (!info) throw new Error('not a torrent file');
  const txt = b => Buffer.isBuffer(b) ? b.toString('utf8') : String(b ?? '');
  const name = txt(info['name.utf-8'] || info.name) || 'Torrent';
  const files = [];
  if (Array.isArray(info.files)) {
    info.files.forEach((f, idx) => {
      const parts = (f['path.utf-8'] || f.path || []).map(txt);
      if (!parts.length || /^_____padding_file/i.test(parts[parts.length - 1])) return;
      files.push({
        ariaIndex: idx + 1,
        path: parts,
        relPath: parts.join('/'),
        diskRelPath: [name, ...parts].join('/'),
        size: Number(f.length) || 0
      });
    });
  } else {
    files.push({
      ariaIndex: 1,
      path: [name],
      relPath: name,
      diskRelPath: name,
      size: Number(info.length) || 0
    });
  }
  const infoHash = infoRaw ? crypto.createHash('sha1').update(infoRaw).digest('hex').toUpperCase() : '';
  return { name, files, infoHash, single: !Array.isArray(info.files) };
}

function fgFormatContents(t, title) {
  const total = t.files.reduce((a, f) => a + f.size, 0);
  const { label } = getAutoFitGirlPartMb(total);
  const partBytes = (label === '1 GB' ? 1024 : label === '1.5 GB' ? 1536 : 1900) * 1048576;
  const notes = [`Auto RAR split: ${label} per part (~${Math.max(1, Math.ceil(total / partBytes))} parts)`];
  if (t.files.some(f => /\.bin$/i.test(f.path[f.path.length - 1]))) notes.push('Split archives (.bin)');

  const numberedLines = t.files.map((f, i) => `*${i + 1}.* ${f.relPath} — _${bytes(f.size)}_`);
  return [
    `📦 *TORRENT CONTENTS: ${title || t.name}*`,
    '━━━━━━━━━━━━━━━━━━━━',
    `📊 Total Size: *${bytes(total)}* | 📁 Files: *${t.files.length}*`,
    t.infoHash ? `🔗 InfoHash: \`${t.infoHash}\`` : null,
    '',
    '📂 *Numbered Files List:*',
    ...numberedLines,
    '',
    `ℹ️ Notes: ${notes.join(' / ')}`
  ].filter(x => x !== null).join('\n');
}

async function getFitGirlTorrentContents(input, title) {
  const dir = path.join(TEMP_DIR, 'fg-meta-' + Date.now() + '-' + Math.random().toString(16).slice(2, 8));
  await fs.promises.mkdir(dir, { recursive: true });
  try {
    let buf = null;
    if (typeof input === 'string' && /\.torrent$/i.test(input) && fs.existsSync(input)) {
      buf = await fs.promises.readFile(input);
    } else if (/^https?:\/\//i.test(input)) {
      const res = await fetch(input, { signal: AbortSignal.timeout(20000), headers: { 'User-Agent': 'Mozilla/5.0' } });
      if (res.ok) { const b = Buffer.from(await res.arrayBuffer()); if (b.length > 100 && b.length < 8 * 1024 * 1024 && b[0] === 0x64) buf = b; }
    }
    if (!buf && /^magnet:/i.test(input)) {
      await new Promise((resolve, reject) => {
        const child = spawn('aria2c', ['--enable-color=false', '--dir', dir, '--bt-metadata-only=true', '--bt-save-metadata=true', '--bt-stop-timeout=0', '--seed-time=0', '--follow-torrent=false', '--console-log-level=error', input], { windowsHide: true, stdio: ['ignore', 'ignore', 'ignore'] });
        const timer = setTimeout(() => { try { child.kill('SIGTERM'); } catch {} }, 75000);
        child.once('error', err => { clearTimeout(timer); reject(err); });
        child.once('close', () => { clearTimeout(timer); resolve(); });
      });
      const tf = (await fs.promises.readdir(dir)).find(n => /\.torrent$/i.test(n));
      if (tf) buf = await fs.promises.readFile(path.join(dir, tf));
    }
    if (!buf) return null;
    const t = fgParseTorrent(buf);
    if (!t.files.length) return null;
    return {
      text: fgFormatContents(t, title),
      name: t.name,
      infoHash: t.infoHash,
      totalBytes: t.files.reduce((a, f) => a + f.size, 0),
      files: t.files,
      torrentBuffer: buf
    };
  } finally {
    await fs.promises.rm(dir, { recursive: true, force: true }).catch(() => {});
  }
}

function startFitGirlJob(sock, { jid, sender, senderName, label, input, customPrefix, selectFile, selectedCount, selectedPaths, torrentBuffer }) {
  return launchJob(sock, {
    type: 'fitgirl',
    jid,
    sender,
    senderName: senderName || '',
    label: taskLabel(label),
    customPrefix: customPrefix || '',
    input,
    selectFile: selectFile || '',
    selectedCount: selectedCount || 0,
    selectedPaths: Array.isArray(selectedPaths) ? selectedPaths : null,
    torrentBuffer: torrentBuffer || null
  });
}

function hasActiveTasksFor(jid, sender) {
  for (const t of activeTasks.values()) {
    if (t.jid === jid && (!sender || t.sender === sender)) return true;
  }
  return false;
}

function senderFromMsg(sock, msg) {
  const jid = msg.key.remoteJid;
  const senderLid = jidNumber(sock.user?.lid || '');
  const linkedOwner = jidNumber(sock.user?.id || '') || owner;
  const rawSender = msg.key.fromMe ? (linkedOwner || owner) : jidNumber(jid.endsWith('@g.us') ? (msg.key.participant || '') : jid);
  return (senderLid && rawSender === senderLid && owner) ? owner : rawSender;
}

let queueRestored = false;
function restoreQueue(sock) {
  if (queueRestored) return;
  queueRestored = true;
  const jobs = bootQueue.jobs;
  if (!jobs.length) return;
  console.log('[queue] restoring ' + jobs.length + ' task(s) from the last run');
  for (const rec of jobs) {
    try {
      rec.restarts = (rec.restarts || 0) + 1;
      if (rec.restarts > 3) {
        removeQueueFiles(rec.id);
        sock.sendMessage(rec.jid, { text: `⚠️ [MPM] Task #${rec.id} was stopped by restarts 3 times and was removed:\n${rec.label}` }).catch(() => {});
        continue;
      }
      const { task, start } = launchJob(sock, rec, true);
      sock.sendMessage(rec.jid, { text: `🔁 [MPM] The bot restarted. Task #${task.id} continues automatically:\n${rec.label}` }).catch(() => {});
      start();
    } catch (e) { console.error('[queue] could not restore a task:', e && e.message); }
  }
  persistJobs();
}
function cleanupTempOnBoot() {
  try {
    const keepTorrent = new Set([...bootQueue.jobs.filter(j => j.type === 'torrent').map(j => 'torrent-t' + j.id), ...bootQueue.jobs.filter(j => j.type === 'fitgirl').map(j => 'fg-dl-t' + j.id)]);
    const keepIds = new Set(bootQueue.jobs.map(j => String(j.id)));
    const now = Date.now();
    for (const ent of fs.readdirSync(TEMP_DIR, { withFileTypes: true })) {
      const full = path.join(TEMP_DIR, ent.name);
      try {
        if (ent.isDirectory()) { if (!keepTorrent.has(ent.name)) fs.rmSync(full, { recursive: true, force: true }); }
        else if (/^p-[0-9a-f]{24}\.part(\.json)?$/.test(ent.name)) { if (now - fs.statSync(full).mtimeMs > 24 * 3600 * 1000) fs.rmSync(full, { force: true }); }
        else fs.rmSync(full, { force: true });
      } catch {}
    }
    for (const f of fs.readdirSync(QUEUE_FILES_DIR)) { const m = /^t(\d+)\./.exec(f); if (!m || !keepIds.has(m[1])) fs.rmSync(path.join(QUEUE_FILES_DIR, f), { force: true }); }
  } catch (e) { console.warn('[cleanup] ' + (e && e.message)); }
}
cleanupTempOnBoot();

module.exports = { getFitGirlTorrentContents, runFitGirlTorrentAndUpload, startFitGirlJob, hasActiveTasksFor, senderFromMsg, tryPendingRarReply, restoreQueue, getPosterTemplate, renderTemplate, startQuotaReminders, handleDownloaderMessage: handleMessage, throttleCommand, friendlyError, setLinkedOwner, waitUploadGap, markUploadDone, UPLOAD_MAX_BYTES, UPLOAD_MAX_TEXT };