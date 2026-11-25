'use strict';
// Download engine used by downloader.cjs
//  * multi-connection (multi-part) downloading with HTTP Range requests
//  * resume: a broken connection continues from the bytes already saved (also after a bot restart)
//  * real free-disk-space check
//  * link resolvers: Google Drive, Mediafire, Dropbox, Pixeldrain, OneDrive, GitHub blob -> direct links
//  * refuses "web page instead of file" responses with a clear message
const fs = require('fs');
const path = require('path');
const http = require('http');
const https = require('https');
const crypto = require('crypto');
const { URL } = require('url');

const BROWSER_UA = 'Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/126.0.0.0 Safari/537.36';

// downloader.cjs injects its own URL validator (blocks private/local addresses) and helpers.
let deps = {
  validatePublicUrl: async (raw) => new URL(raw),
  filenameFromResponse: (headers, url) => decodeURIComponent(url.pathname.split('/').pop() || 'download'),
  mimeTypeFor: () => 'application/octet-stream'
};
function init(d) { deps = { ...deps, ...d }; }

const sleep = (ms) => new Promise(r => setTimeout(r, ms));
const cancelErr = () => new Error('Task cancelled by user.');
function fatal(msg) { const e = new Error(msg); e.fatal = true; return e; }
function httpError(code) { const e = new Error('Server returned HTTP ' + code); e.statusCode = code; return e; }
function isCancel(e) { return /cancel/i.test(String((e && e.message) || '')); }
function isTransient(e) {
  if (!e || e.fatal || isCancel(e)) return false;
  const m = String(e.message || e) + ' ' + String(e.code || '');
  return /timed? ?out|ETIMEDOUT|ECONNRESET|ECONNREFUSED|EPIPE|socket hang up|aborted|closed before|ENETUNREACH|ENETDOWN|EHOSTUNREACH|EAI_AGAIN|premature close|HTTP (429|500|502|503|504)/i.test(m);
}

// ---- one HTTP request (follows redirects, validates every hop) -------------------------------------
function openRequest(url, { headers = {}, signal = null, redirects = 0 } = {}) {
  return new Promise(async (resolve, reject) => {
    try {
      const u = await deps.validatePublicUrl(url);
      if (signal && signal.aborted) return reject(cancelErr());
      const client = u.protocol === 'https:' ? https : http;
      const req = client.get(u, { timeout: 30000, headers: { 'User-Agent': BROWSER_UA, 'Accept': '*/*', ...headers } }, res => {
        if ([301, 302, 303, 307, 308].includes(res.statusCode)) {
          res.resume();
          if (redirects >= 8 || !res.headers.location) return reject(new Error('Too many redirects.'));
          const next = new URL(res.headers.location, u);
          const h = { ...headers };
          if (next.hostname !== u.hostname) for (const k of Object.keys(h)) if (/^(cookie|authorization)$/i.test(k)) delete h[k];
          return resolve(openRequest(next.toString(), { headers: h, signal, redirects: redirects + 1 }));
        }
        resolve({ res, url: u, status: res.statusCode, headers: res.headers });
      });
      req.on('timeout', () => req.destroy(new Error('Connection timed out.')));
      req.on('error', reject);
      if (signal) { const ab = () => req.destroy(cancelErr()); if (signal.aborted) ab(); else signal.addEventListener('abort', ab, { once: true }); }
    } catch (e) { reject(e); }
  });
}

// Small text/HTML fetch (used by the link resolvers). Never downloads a big binary body.
async function getText(url, { headers = {}, signal = null, maxBytes = 800000 } = {}) {
  const r = await openRequest(url, { headers, signal });
  const type = String(r.headers['content-type'] || '').toLowerCase();
  if (!/text|json|xml|html/.test(type)) { r.res.destroy(); return { status: r.status, type, body: '', url: r.url.toString(), headers: r.headers }; }
  let body = '';
  try {
    r.res.setEncoding('utf8');
    for await (const chunk of r.res) { body += chunk; if (body.length > maxBytes) break; }
  } finally { r.res.destroy(); }
  return { status: r.status, type, body, url: r.url.toString(), headers: r.headers };
}

// ---- link resolvers --------------------------------------------------------------------------------
function decodeHtml(s) { return String(s || '').replace(/&amp;/g, '&').replace(/&#x2F;/gi, '/').replace(/&#39;/g, "'").replace(/&quot;/g, '"'); }
function parseAttrs(tag) {
  const out = {};
  for (const m of String(tag).matchAll(/([a-zA-Z_:][-a-zA-Z0-9_:.]*)\s*=\s*(?:"([^"]*)"|'([^']*)')/g)) out[m[1].toLowerCase()] = decodeHtml(m[2] !== undefined ? m[2] : m[3]);
  return out;
}
function parseMediafire(html) {
  const tag = /<a\b[^>]*\bid=["']downloadButton["'][^>]*>/i.exec(html);
  if (tag) {
    const a = parseAttrs(tag[0]);
    if (a['data-scrambled-url']) { try { const d = Buffer.from(a['data-scrambled-url'], 'base64').toString('utf8'); if (/^https?:\/\//i.test(d)) return d; } catch {} }
    if (a.href && /^https?:\/\//i.test(a.href)) return a.href;
  }
  const m = /href=["'](https?:\/\/download[0-9]*\.mediafire\.com\/[^"']+)["']/i.exec(html);
  return m ? decodeHtml(m[1]) : null;
}
function parseDriveInterstitial(html, base) {
  if (/Quota exceeded|too many users have (viewed or )?downloaded|Too many users/i.test(html)) throw fatal('Google Drive download quota exceeded for this file. Try again in about 24 hours, or make a copy to your own Drive.');
  const form = /<form\b[^>]*id=["']download-form["'][^>]*>/i.exec(html) || /<form\b[^>]*action=["'][^"']*(?:download|uc)[^"']*["'][^>]*>/i.exec(html);
  if (!form) return null;
  const fa = parseAttrs(form[0]);
  if (!fa.action) return null;
  const target = new URL(fa.action, base);
  for (const inp of html.matchAll(/<input\b[^>]*>/gi)) {
    const a = parseAttrs(inp[0]);
    if (a.type === 'hidden' && a.name) target.searchParams.set(a.name, a.value || '');
  }
  return target.toString();
}
function driveId(u) {
  const m = u.pathname.match(/\/(?:file|document|presentation|spreadsheets)\/(?:u\/\d+\/)?d\/([A-Za-z0-9_-]+)/) || u.pathname.match(/^\/(?:uc|open|download)$/) && null;
  return (m && m[1]) || u.searchParams.get('id') || null;
}

// Returns { url, headers?, fileName? }. Unknown sites are returned unchanged.
async function resolveLink(raw, { signal = null } = {}) {
  let u;
  try { u = new URL(raw); } catch { return { url: raw }; }
  const host = u.hostname.replace(/^www\./i, '').toLowerCase();

  if (host === 'dropbox.com') {
    u.searchParams.delete('raw'); u.searchParams.set('dl', '1');
    return { url: u.toString() };
  }
  if (host === 'github.com') {
    const m = u.pathname.match(/^\/([^/]+)\/([^/]+)\/(?:blob|raw)\/(.+)$/);
    if (m) return { url: `https://raw.githubusercontent.com/${m[1]}/${m[2]}/${m[3]}` };
    return { url: raw };
  }
  if (host === 'pixeldrain.com') {
    const m = u.pathname.match(/^\/u\/([A-Za-z0-9]+)/);
    if (m) return { url: `https://pixeldrain.com/api/file/${m[1]}?download` };
    if (/^\/l\//.test(u.pathname)) throw fatal('Pixeldrain lists (folders) are not supported. Send the link of a single file (pixeldrain.com/u/...).');
    return { url: raw };
  }
  if (host === '1drv.ms' || host === 'onedrive.live.com' || host === 'photos.onedrive.com') {
    const b64 = Buffer.from(raw, 'utf8').toString('base64').replace(/=+$/, '').replace(/\+/g, '-').replace(/\//g, '_');
    return { url: `https://api.onedrive.com/v1.0/shares/u!${b64}/root/content` };
  }
  if (host === 'mega.nz' || host === 'mega.co.nz') {
    throw fatal('Mega links are not supported (they are end-to-end encrypted and need the Mega client).');
  }
  if (host === 'drive.google.com' || host === 'docs.google.com' || host === 'drive.usercontent.google.com') {
    if (/\/drive\/(u\/\d+\/)?folders\//.test(u.pathname)) throw fatal('Google Drive folders are not supported. Send the link of a single file.');
    const id = driveId(u);
    if (!id) return { url: raw };
    let url = `https://drive.usercontent.google.com/download?id=${encodeURIComponent(id)}&export=download&confirm=t`;
    // If Google still answers with its "virus scan" page, follow the form on that page.
    const page = await getText(url, { signal });
    if (/html/.test(page.type)) {
      const next = parseDriveInterstitial(page.body, page.url);
      if (next) url = next;
      else if (/accounts\.google\.com|ServiceLogin|You need access|Request access/i.test(page.body + page.url)) throw fatal('This Google Drive file is private. Share it as "Anyone with the link" and try again.');
      else throw fatal('Google Drive did not give a downloadable file for this link.');
    }
    return { url };
  }
  if (/(^|\.)mediafire\.com$/.test(host) && /^\/(file|file_premium|view|download)\//.test(u.pathname)) {
    const page = await getText(raw, { signal });
    const direct = parseMediafire(page.body);
    if (!direct) throw fatal('Could not find the download button on this Mediafire page (file removed, private, or Mediafire changed its page).');
    return { url: direct };
  }
  return { url: raw };
}

// ---- disk space ------------------------------------------------------------------------------------
async function freeDiskBytes(dir) {
  try {
    if (typeof fs.promises.statfs !== 'function') return Infinity;
    const s = await fs.promises.statfs(dir);
    return Number(s.bavail) * Number(s.bsize);
  } catch { return Infinity; }
}
function fmtBytes(n) {
  if (!Number.isFinite(n)) return '?';
  const u = ['B', 'KB', 'MB', 'GB', 'TB']; let i = 0, v = n;
  while (v >= 1024 && i < u.length - 1) { v /= 1024; i++; }
  return (i ? v.toFixed(2) : v) + ' ' + u[i];
}
async function ensureDisk(dir, needBytes, reserveBytes) {
  const free = await freeDiskBytes(dir);
  if (free < needBytes + reserveBytes) {
    throw fatal(`💾 Not enough disk space on the bot server: needs ${fmtBytes(needBytes)} (+${fmtBytes(reserveBytes)} kept free), only ${fmtBytes(free)} free.`);
  }
}

// ---- download --------------------------------------------------------------------------------------
const activeParts = new Set();   // partial files in use right now (two tasks never share one)
function partPathFor(dir, key) { return path.join(dir, 'p-' + crypto.createHash('sha1').update(String(key)).digest('hex').slice(0, 24) + '.part'); }

async function probe(url, headers, signal) {
  let r;
  try { r = await openRequest(url, { headers: { ...headers, Range: 'bytes=0-0' }, signal }); }
  catch (e) { throw e; }
  if (r.status === 206) {
    const m = /bytes\s+(\d+)-(\d+)\/(\d+)/i.exec(String(r.headers['content-range'] || ''));
    r.res.destroy();
    if (m && Number(m[3]) > 0) return { ranges: true, total: Number(m[3]), finalUrl: r.url, headers: r.headers };
    r = await openRequest(url, { headers, signal });
  } else if (r.status >= 200 && r.status < 300 && r.status !== 206) {
    return { ranges: false, res: r.res, length: Number(r.headers['content-length']) || 0, finalUrl: r.url, headers: r.headers };
  } else {
    r.res.resume();
    if (![416, 400, 403, 405, 501].includes(r.status)) throw httpError(r.status);
    r = await openRequest(url, { headers, signal });   // server dislikes Range: plain request
  }
  if (r.status < 200 || r.status >= 300) { r.res.resume(); throw httpError(r.status); }
  return { ranges: false, res: r.res, length: Number(r.headers['content-length']) || 0, finalUrl: r.url, headers: r.headers };
}

/**
 * download({ url, headers, signal, outPath, onMeta, onChunk, connections, minMultipart, reserveBytes })
 *  onMeta({ name, mimetype, length, ranges })  -> may throw to refuse the file (size limits ...)
 *  onChunk(totalBytesSoFar)                    -> may throw to stop (quota exceeded ...)
 * Resolves { size, name, mimetype, parts, resumedBytes }.
 * If outPath has a matching partial file + outPath.json, the download continues from it.
 */
async function download(o) {
  const { url, headers = {}, signal = null, outPath, onMeta = () => {}, onChunk = () => {}, reserveBytes = 0 } = o;
  const connections = Math.max(1, Math.min(16, Number(o.connections) || 4));
  const minMultipart = Number(o.minMultipart) > 0 ? Number(o.minMultipart) : 8 * 1024 * 1024;
  const maxTries = Number(o.maxTries) || 5;
  const metaPath = outPath + '.json';
  if (signal && signal.aborted) throw cancelErr();

  const p = await probe(url, headers, signal);
  const h = p.headers;
  const name = deps.filenameFromResponse(h, p.finalUrl);
  const ctype = String(h['content-type'] || '').toLowerCase();
  const disp = String(h['content-disposition'] || '');
  if (/text\/html/.test(ctype) && !/attachment|filename/i.test(disp) && !/\.html?$/i.test(name)) {
    if (p.res) p.res.destroy();
    throw fatal('🔗 This link opens a web page, not a file. Send a direct file link (or a supported site: Google Drive, Mediafire, Dropbox, Pixeldrain, OneDrive, GitHub, Gofile).');
  }
  const total = p.ranges ? p.total : p.length;
  const mimetype = deps.mimeTypeFor(name, h['content-type']);

  // --- same-host cookie safety for the range requests that follow
  const partHeaders = { ...headers };
  try { if (new URL(url).hostname !== p.finalUrl.hostname) for (const k of Object.keys(partHeaders)) if (/^(cookie|authorization)$/i.test(k)) delete partHeaders[k]; } catch {}

  try { await onMeta({ name, mimetype, length: total, ranges: p.ranges }); }
  catch (e) { if (p.res) p.res.destroy(); throw e; }

  const dir = path.dirname(outPath);
  const abort = new AbortController();
  if (signal) { if (signal.aborted) abort.abort(); else signal.addEventListener('abort', () => abort.abort(), { once: true }); }
  const fail = () => (signal && signal.aborted ? cancelErr() : null);

  // ===== no Range support (or unknown size): one plain stream, retried from the start by the caller =====
  if (!p.ranges) {
    try { await ensureDisk(dir, total || 0, reserveBytes); } catch (e) { p.res.destroy(); throw e; }
    try { fs.rmSync(metaPath, { force: true }); } catch {}
    const out = fs.createWriteStream(outPath);
    let received = 0, lastDiskCheck = Date.now();
    const onAbort = () => p.res.destroy(cancelErr());
    if (signal) { if (signal.aborted) onAbort(); else signal.addEventListener('abort', onAbort, { once: true }); }
    try {
      for await (const chunk of p.res) {
        if (!out.write(chunk)) await new Promise(r => out.once('drain', r));
        received += chunk.length;
        onChunk(received);
        if (!total && Date.now() - lastDiskCheck > 5000) { lastDiskCheck = Date.now(); await ensureDisk(dir, 0, Math.floor(reserveBytes / 2)); }
      }
      if (!p.res.complete) throw new Error('Connection closed before the download finished.');
      if (total && received !== total) throw new Error('Connection closed before the download finished.');
    } catch (e) { out.destroy(); throw fail() || e; }
    await new Promise((res, rej) => { out.once('error', rej); out.end(res); });
    return { size: received, name, mimetype, parts: 1, resumedBytes: 0 };
  }

  // ===== Range supported: parts, each one resumable =====
  const n = total >= minMultipart ? Math.min(connections, Math.max(1, Math.ceil(total / (4 * 1024 * 1024)))) : 1;
  const per = Math.ceil(total / n);
  let state = null;
  try {
    const saved = JSON.parse(fs.readFileSync(metaPath, 'utf8'));
    const st = fs.statSync(outPath);
    const sameEtag = !saved.etag || !h.etag || saved.etag === h.etag;
    const sameLm = !saved.lastModified || !h['last-modified'] || saved.lastModified === h['last-modified'];
    if (saved.total === total && st.size === total && sameEtag && sameLm && Array.isArray(saved.parts) && saved.parts.length >= 1 &&
        saved.parts.every(x => Number.isFinite(x.start) && Number.isFinite(x.end) && Number.isFinite(x.done) && x.done >= 0 && x.done <= x.end - x.start + 1)) state = saved;
  } catch { /* no usable partial */ }
  const resumedBytes = state ? state.parts.reduce((a, x) => a + x.done, 0) : 0;
  if (!state) {
    state = { url, total, etag: h.etag || '', lastModified: h['last-modified'] || '', parts: [] };
    for (let i = 0; i < n; i++) {
      const start = i * per, end = Math.min(total - 1, start + per - 1);
      if (start <= end) state.parts.push({ start, end, done: 0 });
    }
    await ensureDisk(dir, total, reserveBytes);
    fs.closeSync(fs.openSync(outPath, 'w'));
    fs.truncateSync(outPath, total);
  } else {
    await ensureDisk(dir, total - resumedBytes, reserveBytes);
  }
  const saveMeta = () => { try { fs.writeFileSync(metaPath, JSON.stringify(state)); } catch {} };
  saveMeta();
  const metaTimer = setInterval(saveMeta, 3000); metaTimer.unref?.();

  const fh = await fs.promises.open(outPath, 'r+');
  let received = resumedBytes;
  let lastDiskCheck = Date.now();
  const finalUrl = p.finalUrl.toString();

  async function runPart(part) {
    let fails = 0;
    while (part.done < part.end - part.start + 1) {
      if (abort.signal.aborted) throw fail() || cancelErr();
      const before = part.done;
      const from = part.start + part.done;
      try {
        const r = await openRequest(finalUrl, { headers: { ...partHeaders, Range: `bytes=${from}-${part.end}` }, signal: abort.signal });
        if (r.status !== 206) {
          r.res.destroy();
          if (r.status === 200) throw fatal('The server stopped supporting partial downloads. Please try again.');
          throw httpError(r.status);
        }
        const cr = /bytes\s+(\d+)-/i.exec(String(r.headers['content-range'] || ''));
        if (!cr || Number(cr[1]) !== from) { r.res.destroy(); throw fatal('The server answered a wrong byte range.'); }
        try {
          for await (const chunk of r.res) {
            const room = part.end - part.start + 1 - part.done;
            const buf = chunk.length > room ? chunk.subarray(0, room) : chunk;
            await fh.write(buf, 0, buf.length, part.start + part.done);
            part.done += buf.length; received += buf.length;
            try { onChunk(received); } catch (e) { e.fatal = true; throw e; }
            if (Date.now() - lastDiskCheck > 10000) { lastDiskCheck = Date.now(); await ensureDisk(dir, 0, Math.floor(reserveBytes / 2)); }
            if (buf.length < chunk.length) break;
          }
        } finally { r.res.destroy(); }
      } catch (e) {
        if (abort.signal.aborted) throw fail() || e;
        if (!isTransient(e)) throw e;
        if (++fails > maxTries) throw e;
        await sleep(Math.min(1500 * fails, 8000));
        continue;
      }
      if (part.done === before) {          // server closed the connection without sending anything
        if (++fails > maxTries) throw new Error('Connection closed before the download finished.');
        await sleep(Math.min(1500 * fails, 8000));
      } else fails = 0;
    }
  }

  try {
    const results = await Promise.allSettled(state.parts.map(async part => {
      try { await runPart(part); } catch (e) { abort.abort(); throw e; }
    }));
    const bad = results.filter(r => r.status === 'rejected').map(r => r.reason);
    if (bad.length) throw fail() || bad.find(e => !isCancel(e)) || bad[0];
    if (state.parts.some(x => x.done !== x.end - x.start + 1)) throw new Error('Connection closed before the download finished.');
  } catch (e) {
    saveMeta();                              // keep progress so the next try continues from here
    throw e;
  } finally {
    clearInterval(metaTimer);
    await fh.close().catch(() => {});
  }
  try { fs.rmSync(metaPath, { force: true }); } catch {}
  return { size: total, name, mimetype, parts: state.parts.length, resumedBytes };
}

function discardPartial(outPath) {
  try { fs.rmSync(outPath, { force: true }); } catch {}
  try { fs.rmSync(outPath + '.json', { force: true }); } catch {}
}

module.exports = { init, download, resolveLink, getText, openRequest, freeDiskBytes, ensureDisk, fmtBytes, partPathFor, activeParts, discardPartial, isTransient, parseMediafire, parseDriveInterstitial, BROWSER_UA };
