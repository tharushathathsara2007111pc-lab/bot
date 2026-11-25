import makeWASocket, {
  useMultiFileAuthState,
  DisconnectReason,
  fetchLatestBaileysVersion
} from "@whiskeysockets/baileys";
import axios from "axios";
import * as cheerio from "cheerio";
import { spawn } from "child_process";
import fs from "fs";
import path from "path";
import pino from "pino";
import qrcode from "qrcode-terminal";
import { createRequire } from "module";
const require = createRequire(import.meta.url);
const { tryPendingRarReply, restoreQueue, handleDownloaderMessage, getPosterTemplate, renderTemplate, startQuotaReminders, setLinkedOwner, waitUploadGap, markUploadDone, throttleCommand, startFitGirlJob, hasActiveTasksFor, senderFromMsg, getFitGirlTorrentContents } = require("./downloader.cjs");

// ---- Persistent log (bot.log): everything printed in the console is also saved, so crashes can be diagnosed ----
try {
  const LOG_FILE = path.resolve("bot.log");
  try {
    if (fs.existsSync(LOG_FILE) && fs.statSync(LOG_FILE).size > 5 * 1024 * 1024) {
      fs.renameSync(LOG_FILE, LOG_FILE + ".old");
    }
  } catch {}
  const logStream = fs.createWriteStream(LOG_FILE, { flags: "a" });
  logStream.on("error", () => {});
  const stripAnsi = (c) => String(c).replace(/\x1b\[[0-9;]*m/g, "");
  for (const name of ["stdout", "stderr"]) {
    const orig = process[name].write.bind(process[name]);
    process[name].write = (chunk, ...rest) => {
      try { logStream.write(stripAnsi(chunk)); } catch {}
      return orig(chunk, ...rest);
    };
  }
  logStream.write(`\n---- Bot process started ${new Date().toISOString()} ----\n`);
} catch {}

const TEMP_DIR = "./temp_torrents";
const LEECH_DIR = "./leeched_downloads";
const AUTH_DIR = "./auth_info";
const WATCHSOMUCH_BASE = "https://watchsomuch.to";
const BOT_STARTED_AT = Date.now();
const PAGE_SIZE = 10;
const MAX_UPLOAD_BYTES = Math.floor(1.99 * 1024 * 1024 * 1024); // 1.99 GB limit per individual file (WhatsApp refuses 2 GB+)

const PUBLIC_TRACKERS = [
  "udp://tracker.opentrackr.org:1337/announce",
  "udp://open.stealth.si:80/announce",
  "udp://tracker.torrent.eu.org:451/announce",
  "udp://tracker.moeking.me:6969/announce",
  "udp://explodie.org:6969/announce",
  "udp://tracker1.bt.moeu.cn:80/announce",
  "udp://tracker.dler.org:6969/announce",
  "udp://open.demonii.com:1337/announce",
  "http://tracker.openbittorrent.com:80/announce",
  "udp://tracker.openbittorrent.com:6969/announce"
];

if (!fs.existsSync(TEMP_DIR)) fs.mkdirSync(TEMP_DIR, { recursive: true });
if (!fs.existsSync(LEECH_DIR)) fs.mkdirSync(LEECH_DIR, { recursive: true });
if (!fs.existsSync(AUTH_DIR)) fs.mkdirSync(AUTH_DIR, { recursive: true });

const http = axios.create({
  timeout: 22000,
  headers: {
    "User-Agent":
      "Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/128.0.0.0 Safari/537.36",
    Referer: "https://en.yts.lu/"
  }
});

const YTS_API_MIRRORS = [
  "https://en.yts.lu/api/v2/list_movies.json",
  "https://yts.lu/api/v2/list_movies.json",
  "https://yts.lt/api/v2/list_movies.json",
  "https://yts.ag/api/v2/list_movies.json",
  "https://yts.am/api/v2/list_movies.json"
];

const YTS_WEB_MIRRORS = [
  "https://en.yts.lu",
  "https://yts.lu",
  "https://yts.lt",
  "https://yts.ag",
  "https://yts.am"
];

const EZTV_API_MIRRORS = [
  "https://eztv.re/api/get-torrents",
  "https://eztv.ag/api/get-torrents"
];

const APIBAY_MIRRORS = [
  "https://apibay.org/q.php",
  "https://tpb.party/q.php"
];

const EXTRA_TORRENT_SOURCES = [
  (q) => ({
    url: `https://solidtorrents.to/api/v1/search?q=${encodeURIComponent(q)}&category=all&sort=seeders`,
    source: "SolidTorrents"
  }),
  (q) => ({
    url: `https://bitsearch.to/search?q=${encodeURIComponent(q)}`,
    source: "BitSearch"
  }),
  (q) => ({
    url: `https://knaben.org/search/${encodeURIComponent(q)}/0/1/seeders`,
    source: "Knaben"
  }),
  (q) => ({
    url: `https://ext.to/search/?q=${encodeURIComponent(q)}`,
    source: "EXT"
  }),
  (q) => ({
    url: `https://1337x.to/search/${encodeURIComponent(q)}/1/`,
    source: "1337x"
  }),
  (q) => ({
    url: `https://limetorrents.info/search/all/${encodeURIComponent(q)}/`,
    source: "LimeTorrents"
  }),
  (q) => ({
    url: `https://torrentdownloads.me/search/?search=${encodeURIComponent(q)}`,
    source: "TorrentDownloads"
  }),
  (q) => ({
    url: `https://torlock.com/all/torrents/${encodeURIComponent(q)}.html`,
    source: "TorLock"
  })
];

const TORRENT_CACHE_MIRRORS = [
  (hash) => `https://itorrents.org/torrent/${hash}.torrent`,
  (hash) => `https://torrage.info/torrent.php?h=${hash}`,
  (hash) => `https://btcache.me/torrent/${hash}`,
  (hash) => `https://watercache.nanodl.com/get/${hash}`
];

const pendingSelectionByChat = new Map();
const pendingActionByChat = new Map();
const activeTasksByChat = new Map();

let webTorrentModulePromise = null;
let webTorrentClient = null;
let admZipModulePromise = null;

async function getWebTorrentClient() {
  if (webTorrentClient) return webTorrentClient;
  if (!webTorrentModulePromise) {
    webTorrentModulePromise = import("webtorrent").catch(() => null);
  }
  const mod = await webTorrentModulePromise;
  const WebTorrentCtor = mod?.default || mod;
  if (!WebTorrentCtor) return null;
  webTorrentClient = new WebTorrentCtor();
  webTorrentClient.on("error", (err) => {
    console.error("[WebTorrent Error]:", err?.message || err);
  });
  return webTorrentClient;
}

async function getAdmZipConstructor() {
  if (!admZipModulePromise) {
    admZipModulePromise = import("adm-zip").catch(() => null);
  }
  const mod = await admZipModulePromise;
  return mod?.default || mod || null;
}

function sanitizeFileName(name) {
  return String(name || "release")
    .replace(/[<>:"/\\|?*\x00-\x1F]+/g, "_")
    .replace(/\s+/g, " ")
    .trim()
    .slice(0, 130);
}

function isValidTorrentBuffer(buf) {
  if (!Buffer.isBuffer(buf) || buf.length < 100) return false;
  const start = buf.slice(0, 64).toString("utf8").trim().toLowerCase();
  if (start.startsWith("<!doctype") || start.startsWith("<html")) return false;
  return true;
}

function extractInfoHash(magnetOrHash) {
  if (!magnetOrHash) return null;
  const clean = String(magnetOrHash).trim();
  if (/^[a-fA-F0-9]{40}$/.test(clean)) return clean.toUpperCase();
  const match = clean.match(/btih:([a-fA-F0-9]{40})/i);
  return match ? match[1].toUpperCase() : null;
}

function buildMagnetUri(resolved) {
  if (resolved.magnet && String(resolved.magnet).startsWith("magnet:")) {
    return String(resolved.magnet).trim();
  }
  const hash = extractInfoHash(resolved.infoHash || resolved.magnet || "");
  if (!hash) return null;
  const dn = encodeURIComponent(resolved.label || "Torrent");
  const tr = PUBLIC_TRACKERS.map((t) => `&tr=${encodeURIComponent(t)}`).join("");
  return `magnet:?xt=urn:btih:${hash}&dn=${dn}${tr}`;
}

function detectQualityTag(text) {
  const str = String(text || "");
  if (/\b(2160p|4k|uhd)\b/i.test(str)) return "2160p";
  if (/\b1080p\b/i.test(str)) return "1080p";
  if (/\b720p\b/i.test(str)) return "720p";
  if (/\b480p\b/i.test(str)) return "480p";
  return null;
}

function formatBytes(bytes) {
  const num = Number(bytes);
  if (!Number.isFinite(num) || num <= 0) return "";
  if (num >= 1024 * 1024 * 1024) {
    return `${(num / (1024 * 1024 * 1024)).toFixed(2)} GB`;
  }
  return `${(num / (1024 * 1024)).toFixed(1)} MB`;
}

function formatUptime(ms) {
  const totalSec = Math.max(0, Math.floor(ms / 1000));
  const days = Math.floor(totalSec / 86400);
  const hours = Math.floor((totalSec % 86400) / 3600);
  const minutes = Math.floor((totalSec % 3600) / 60);
  const seconds = totalSec % 60;

  const parts = [];
  if (days > 0) parts.push(`${days}d`);
  if (hours > 0) parts.push(`${hours}h`);
  if (minutes > 0) parts.push(`${minutes}m`);
  parts.push(`${seconds}s`);
  return parts.join(" ");
}

function getDiskSpaceInfo(targetPath = ".") {
  try {
    if (typeof fs.statfsSync === "function") {
      const stats = fs.statfsSync(targetPath);
      const blockSize = Number(stats.bsize || stats.frsize || 0);
      const totalBytes = blockSize * Number(stats.blocks || 0);
      const freeBytes = blockSize * Number(stats.bavail ?? stats.bfree ?? 0);
      const usedBytes = Math.max(0, totalBytes - freeBytes);
      const usedPercent = totalBytes > 0 ? ((usedBytes / totalBytes) * 100).toFixed(1) : "0.0";

      const driveRoot = path.parse(path.resolve(targetPath)).root || targetPath;
      return {
        drive: driveRoot,
        freeText: formatBytes(freeBytes) || "0 MB",
        usedText: formatBytes(usedBytes) || "0 MB",
        totalText: formatBytes(totalBytes) || "0 MB",
        usedPercent
      };
    }
  } catch {
    // Ignore statfs error
  }
  return null;
}

function parseSeasonEpisodeFilter(rawText) {
  const original = String(rawText || '').replace(/\bS[OО](\d{1,2})\b/gi, 'S0$1');
  const qualityMatch = original.match(/\b(2160p|1080p|720p|480p)\b/i);
  const quality = qualityMatch ? qualityMatch[1].toLowerCase() : null;
  let str = original
    .replace(/\b(2160p|1080p|720p|480p)\b/gi, ' ')
    .replace(/\b(season\s*pack|complete\s*pack|complete|pack|all\s*episodes|full\s*season)\b/gi, ' ')
    .replace(/\s+/g, ' ').trim();
  const packRequested = /\b(season\s*pack|complete\s*pack|complete|pack|all\s*episodes|full\s*season)\b/i.test(original);
  const seMatch = str.match(/\bS(\d{1,2})E(\d{1,3})\b/i);
  if (seMatch) {
    const season = Number(seMatch[1]), episode = Number(seMatch[2]);
    const seasonCode = `S${String(season).padStart(2, '0')}`;
    return { mode: 'episode', season, episode, code: `${seasonCode}E${String(episode).padStart(2, '0')}`,
      seasonCode, cleanedQuery: str.replace(seMatch[0], ' ').replace(/\s+/g, ' ').trim(), quality, packRequested };
  }
  const sMatch = str.match(/\bS(\d{1,2})\b|\bSeason\s*(\d{1,2})\b|(\d{1,2})\s*$/i);
  if (sMatch) {
    const season = Number(sMatch[1] || sMatch[2] || sMatch[3]);
    const seasonCode = `S${String(season).padStart(2, '0')}`;
    return { mode: 'season', season, episode: null, code: seasonCode, seasonCode,
      cleanedQuery: str.replace(sMatch[0], ' ').replace(/\s+/g, ' ').trim(), quality, packRequested };
  }
  if (packRequested) return { mode: 'pack', season: null, episode: null, code: 'PACK', seasonCode: null,
    cleanedQuery: str, quality, packRequested };
  return { mode: null, season: null, episode: null, code: null, seasonCode: null, cleanedQuery: str, quality, packRequested: false };
}

function isSeasonPackLabel(label) {
  const str = String(label || "");
  if (/\bS\d{1,2}E\d{1,3}\b/i.test(str)) return false;
  return /\b(season\s*\d{1,2}|s\d{1,2}|complete|pack|season pack|disc\s*\d+)\b/i.test(str);
}

function matchesSeasonEpisodeItem(label, filter) {
  if (!filter || !filter.mode) return true;
  const str = String(label || "");

  if (filter.mode === "episode") {
    const epRegex = new RegExp(String.raw`\bS0?${filter.season}E0?${filter.episode}\b`, "i");
    return epRegex.test(str);
  }

  if (filter.mode === "season") {
    const sTagRegex = new RegExp(String.raw`\bS0?${filter.season}(?:E\d{1,3}|\b|[._\-\s])`, "i");
    const seasonWordRegex = new RegExp(String.raw`\bseason\s*0?${filter.season}\b`, "i");
    return sTagRegex.test(str) || seasonWordRegex.test(str);
  }

  if (filter.mode === "pack") {
    return isSeasonPackLabel(str);
  }

  return true;
}

function orderAndFilterReleases(releases, { seFilter = null, preferPacks = false } = {}) {
  let list = Array.isArray(releases) ? [...releases] : [];

  if (seFilter && seFilter.mode) {
    const matched = list.filter((r) => matchesSeasonEpisodeItem(r.label, seFilter));
    if (matched.length > 0) {
      list = matched;
    }
  }

  if (preferPacks) {
    const packs = list.filter((r) => isSeasonPackLabel(r.label));
    const others = list.filter((r) => !isSeasonPackLabel(r.label));
    list = [...packs, ...others];
  }

  return list;
}

function getPagedItems(allItems, page = 0) {
  const totalItems = allItems.length;
  const totalPages = Math.max(1, Math.ceil(totalItems / PAGE_SIZE));
  const safePage = Math.max(0, Math.min(page, totalPages - 1));
  const start = safePage * PAGE_SIZE;
  const slice = allItems.slice(start, start + PAGE_SIZE);
  const hasMore = start + PAGE_SIZE < totalItems;

  return {
    page: safePage,
    totalPages,
    start,
    items: slice,
    hasMore
  };
}

function formatReleasePageText(session, pageIdx = 0) {
  const paged = getPagedItems(session.releases, pageIdx);
  const lines = paged.items.map((r, i) => {
    const displayNum = i + 1;
    const sizePart = r.size ? ` _(${r.size})_` : "";
    const packBadge = isSeasonPackLabel(r.label) ? " 📦*[PACK]*" : "";
    return `*${displayNum}.* ${r.label}${packBadge}${sizePart}`;
  });
  // "Next" is a separate option (11) so all 10 releases on the page stay selectable
  if (paged.hasMore) lines.push(`*11.* ➡️ *Next page*`);

  const pageInfo =
    paged.totalPages > 1 ? ` _(Page ${paged.page + 1}/${paged.totalPages})_` : "";
  const footerHint = paged.hasMore
    ? "✍️ Reply with a number (e.g. *1*). Reply *11* for *Next page*."
    : "✍️ Reply with the *number* of the release you want (e.g. *1*).";

  return {
    text:
      `${session.headerTitle}${pageInfo}\n` +
      `${session.subTitle}\n\n` +
      `${lines.join("\n")}\n\n` +
      `${footerHint}`,
    paged
  };
}

function isReplyToBotMessage(msg, botJid, botLid) {
  const ctx =
    msg.message?.extendedTextMessage?.contextInfo ||
    msg.message?.imageMessage?.contextInfo ||
    msg.message?.documentMessage?.contextInfo ||
    null;

  if (!ctx?.stanzaId) return false;
  const participant = ctx.participant || "";
  if (!participant) return true;
  const candidates = [botJid, botLid].filter(Boolean).map((id) => id.split(":")[0].split("@")[0]);
  const senderId = participant.split(":")[0].split("@")[0];
  return candidates.includes(senderId);
}

async function fetchTorrentFileBuffer(torrentUrl, infoHash) {
  if (torrentUrl) {
    try {
      const res = await http.get(torrentUrl, { responseType: "arraybuffer", timeout: 15000 });
      const buf = Buffer.from(res.data);
      if (isValidTorrentBuffer(buf)) return buf;
    } catch {}
  }

  const hash = extractInfoHash(infoHash);
  if (hash) {
    for (const makeUrl of TORRENT_CACHE_MIRRORS) {
      try {
        const res = await http.get(makeUrl(hash), {
          responseType: "arraybuffer",
          timeout: 15000
        });
        const buf = Buffer.from(res.data);
        if (isValidTorrentBuffer(buf)) return buf;
      } catch {}
    }
  }

  return null;
}

async function resolveWatchSoMuchRelease(item) {
  if (item.infoHash) return item;
  if (!item.pageUrl) return item;

  try {
    const { data: html } = await http.get(item.pageUrl, { timeout: 15000 });
    const $ = cheerio.load(html);
    const magnet =
      $("#txtMagnetLink").val() ||
      $("#txtMagnetLink").attr("value") ||
      $('input[value^="magnet:?"]').attr("value") ||
      $('a[href^="magnet:?"]').attr("href") ||
      "";
    const infoHash = extractInfoHash(magnet);
    const q = item.quality || detectQualityTag(`${item.label} ${magnet}`);
    return {
      ...item,
      quality: q,
      magnet: magnet.trim() || null,
      infoHash
    };
  } catch {
    return item;
  }
}

async function searchWatchSoMuchPsa(query, qualityFilter = null) {
  const words = query
    .toLowerCase()
    .split(/\s+/)
    .filter((w) => w.length > 1);

  const slug = query
    .trim()
    .split(/\s+/)
    .map((w) => w.charAt(0).toUpperCase() + w.slice(1).toLowerCase())
    .join("-");

  const pagesToCheck = [
    `${WATCHSOMUCH_BASE}/Movies/${encodeURIComponent(slug)}/`,
    `${WATCHSOMUCH_BASE}/Movies/${encodeURIComponent(query)}/`,
    `${WATCHSOMUCH_BASE}/Movies/PSA-Group/`,
    `${WATCHSOMUCH_BASE}/Movies/Series/`
  ];

  const found = [];
  const seenKeys = new Set();

  for (const url of pagesToCheck) {
    try {
      const { data: html } = await http.get(url, { timeout: 15000 });
      const $ = cheerio.load(html);

      $("a[href]").each((_, el) => {
        const href = ($(el).attr("href") || "").trim();
        const text = $(el).text().replace(/\s+/g, " ").trim();
        const parentText = $(el).closest("tr, div, li").text().replace(/\s+/g, " ").trim();
        const combined = `${href} ${text} ${parentText}`.toLowerCase();

        const isDownloadLink = /\/Movie\/[^"'\s<>]+\/Download-\d+/i.test(href);
        const matchesQuery = words.length === 0 || words.every((w) => combined.includes(w));
        const isPsa = /\bpsa\b/i.test(combined);
        const qTag = detectQualityTag(combined);
        const matchesQuality =
          !qualityFilter ||
          !qTag ||
          qTag.toLowerCase() === qualityFilter.toLowerCase();

        if (isDownloadLink && matchesQuery && isPsa && matchesQuality) {
          const fullUrl = href.startsWith("http")
            ? href
            : new URL(href, WATCHSOMUCH_BASE).href;
          if (!seenKeys.has(fullUrl)) {
            seenKeys.add(fullUrl);
            const title =
              text && text.length > 3
                ? text
                : decodeURIComponent(fullUrl.split("/").pop() || query).replace(/-/g, " ");
            found.push({
              label: qTag && !new RegExp(qTag, "i").test(title) ? `${title} [${qTag}]` : title,
              quality: qTag || qualityFilter || null,
              fileName: sanitizeFileName(`${title}${qTag ? `-${qTag}` : ""}-PSA.torrent`),
              source: "WatchSoMuch (PSA)",
              size: "",
              pageUrl: fullUrl,
              infoHash: null,
              torrentUrl: null
            });
          }
        }
      });

      const rawMatches = html.match(/\/Movie\/[^"'\s<>]+\/Download-\d+\/[^"'\s<>]+/gi) || [];
      for (const rel of rawMatches) {
        const lower = rel.toLowerCase();
        const matchesQuery = words.length === 0 || words.every((w) => lower.includes(w));
        const isPsa = /\bpsa\b/i.test(lower);
        const qTag = detectQualityTag(lower);
        const matchesQuality =
          !qualityFilter ||
          !qTag ||
          qTag.toLowerCase() === qualityFilter.toLowerCase();

        if (matchesQuery && isPsa && matchesQuality) {
          const fullUrl = `${WATCHSOMUCH_BASE}${rel}`;
          if (!seenKeys.has(fullUrl)) {
            seenKeys.add(fullUrl);
            const cleanName = decodeURIComponent(rel.split("/").pop() || query).replace(/-/g, " ");
            found.push({
              label: qTag && !new RegExp(qTag, "i").test(cleanName) ? `${cleanName} [${qTag}]` : cleanName,
              quality: qTag || qualityFilter || null,
              fileName: sanitizeFileName(`${cleanName}${qTag ? `-${qTag}` : ""}-PSA.torrent`),
              source: "WatchSoMuch (PSA)",
              size: "",
              pageUrl: fullUrl,
              infoHash: null,
              torrentUrl: null
            });
          }
        }
      }
    } catch {}
  }

  return found;
}

async function searchApiBayMirrors(searchTerm, { requirePsa = false, qualityFilter = null, category = "0" } = {}) {
  const results = [];
  const seenHashes = new Set();

  for (const apiBase of APIBAY_MIRRORS) {
    try {
      const res = await http.get(apiBase, {
        params: { q: searchTerm, cat: category },
        timeout: 12000
      });
      const list = Array.isArray(res.data) ? res.data : [];
      for (const row of list) {
        if (!row?.info_hash || /^0+$/.test(row.info_hash)) continue;
        const name = String(row.name || "").trim();
        if (!name) continue;
        if (requirePsa && !/\bpsa\b/i.test(name)) continue;

        const qTag = detectQualityTag(name);
        if (qualityFilter && qTag && qTag.toLowerCase() !== qualityFilter.toLowerCase()) {
          continue;
        }

        const hash = row.info_hash.toUpperCase();
        if (seenHashes.has(hash)) continue;
        seenHashes.add(hash);

        const isPsa = /\bpsa\b/i.test(name);
        const hostLabel = new URL(apiBase).hostname.replace(/^www\./, "");
        results.push({
          label: name,
          quality: qTag || qualityFilter || null,
          fileName: sanitizeFileName(`${name}.torrent`),
          source: isPsa ? `PSA / ${hostLabel}` : hostLabel,
          size: formatBytes(row.size),
          pageUrl: null,
          infoHash: hash,
          torrentUrl: null
        });
      }
      if (results.length > 0) break;
    } catch {}
  }

  return results;
}

async function searchExtraIndexers(searchTerm, { requirePsa = false, qualityFilter = null } = {}) {
  const results = [];
  const seenHashes = new Set();
  const seenLabels = new Set();

  const addCandidate = (name, hash, sourceLabel, sizeText = "") => {
    const cleanName = String(name || "").replace(/\s+/g, " ").trim();
    if (!cleanName || cleanName.length < 3) return;
    if (requirePsa && !/\bpsa\b/i.test(cleanName)) return;

    const qTag = detectQualityTag(cleanName);
    if (qualityFilter && qTag && qTag.toLowerCase() !== qualityFilter.toLowerCase()) return;

    const normHash = extractInfoHash(hash);
    const labelKey = cleanName.toLowerCase();
    if (normHash && seenHashes.has(normHash)) return;
    if (!normHash && seenLabels.has(labelKey)) return;

    if (normHash) seenHashes.add(normHash);
    seenLabels.add(labelKey);

    results.push({
      label: cleanName,
      quality: qTag || qualityFilter || null,
      fileName: sanitizeFileName(`${cleanName}.torrent`),
      source: /\bpsa\b/i.test(cleanName) ? `PSA / ${sourceLabel}` : sourceLabel,
      size: sizeText || "",
      pageUrl: null,
      infoHash: normHash || null,
      torrentUrl: null
    });
  };

  await Promise.allSettled(EXTRA_TORRENT_SOURCES.map(async (makeSource) => {
    const { url, source: sourceName } = makeSource(searchTerm);
    try {
      const res = await http.get(url, { timeout: 12000 });
      const rawText = typeof res.data === "string" ? res.data : JSON.stringify(res.data);

      const jsonResults = res.data?.results;
      if (Array.isArray(jsonResults)) {
        for (const r of jsonResults) {
          const name = String(r.title || r.name || "").trim();
          const hash = extractInfoHash(r.infohash || r.hash || r.magnet || "");
          addCandidate(name, hash, sourceName, r.size ? formatBytes(r.size) : "");
        }
      }

      const magnetMatches = rawText.match(/magnet:\?xt=urn:btih:[a-fA-F0-9]{40}[^"'\s<>]*/gi) || [];
      for (const mag of magnetMatches) {
        const hash = extractInfoHash(mag);
        const dnMatch = mag.match(/[?&]dn=([^&"'\s<>]+)/i);
        const decodedName = dnMatch ? decodeURIComponent(dnMatch[1].replace(/\+/g, " ")).trim() : searchTerm;
        addCandidate(decodedName, hash, sourceName, "");
      }

      if (typeof res.data === "string") {
        const $ = cheerio.load(res.data);
        $("a[href]").each((_, el) => {
          const href = ($(el).attr("href") || "").trim();
          const text = $(el).text().replace(/\s+/g, " ").trim();
          const card = $(el).closest("tr, .torrent, .result, .result-item, .torrent-row, .card, article, li");
          const rowText = (card.length ? card.text() : $(el).parent().text()).replace(/\s+/g, " ").trim();
          const hashFromHref = extractInfoHash(href);
          const isTorrentPageLink =
            Boolean(hashFromHref) ||
            /\/(?:torrent|details|download)\/[^?#]+/i.test(href) ||
            /\/[a-z0-9-]+-torrent-\d+\.html/i.test(href) ||
            /\.torrent(?:$|[?#])/i.test(href);
          const candidateName = text.length > 3 ? text : rowText.slice(0, 180);

          if (isTorrentPageLink && candidateName.length > 3) {
            const sizeMatch = rowText.match(/\b(\d+(?:\.\d+)?\s*(?:TB|GB|MB))\b/i);
            addCandidate(candidateName, hashFromHref, sourceName, sizeMatch ? sizeMatch[1] : "");
          }
        });
      }
    } catch {}
  }));

  return results;
}

async function searchYtsReleasesForMovie(query) {
  for (const apiUrl of YTS_API_MIRRORS) {
    try {
      const res = await http.get(apiUrl, {
        params: {
          query_term: query,
          limit: 5,
          sort_by: "year",
          order_by: "desc"
        },
        timeout: 15000
      });

      const movies = res.data?.data?.movies;
      if (!Array.isArray(movies) || movies.length === 0) continue;

      const primaryMovie = movies[0];
      const posterUrl =
        primaryMovie.large_cover_image ||
        primaryMovie.medium_cover_image ||
        null;

      const movieTitle =
        primaryMovie.title_long ||
        `${primaryMovie.title} (${primaryMovie.year || ""})`.trim();

      const sourceHost = new URL(apiUrl).hostname.includes("yts.lu") ? "YTS.LU" : "YTS";
      const releases = [];

      for (const m of movies.slice(0, 4)) {
        const titleBase = m.title_long || `${m.title} (${m.year || ""})`.trim();
        const torrents = Array.isArray(m.torrents) ? m.torrents : [];
        for (const t of torrents) {
          if (!t.url && !t.hash) continue;
          const qTag = [t.quality, t.type ? t.type.toUpperCase() : null, t.video_codec]
            .filter(Boolean)
            .join(" ");
          releases.push({
            label: `${titleBase} — ${qTag} (${sourceHost})`,
            quality: t.quality || null,
            fileName: sanitizeFileName(`${m.slug || m.title}-${t.quality || "release"}-${sourceHost}.torrent`),
            source: sourceHost,
            size: t.size || "",
            pageUrl: null,
            infoHash: t.hash || null,
            torrentUrl: t.url || null
          });
        }
      }

      if (releases.length > 0) {
        let ytsLang = "";
        try {
          const code = String(primaryMovie.language || "").toLowerCase();
          if (code && code !== "xx") ytsLang = new Intl.DisplayNames(["en"], { type: "language" }).of(code) || "";
        } catch {}
        return {
          movieTitle,
          cleanTitle: primaryMovie.title || "",
          ytsMeta: {
            imdbId: primaryMovie.imdb_code || "",
            year: primaryMovie.year ? String(primaryMovie.year) : "",
            runtime: primaryMovie.runtime || 0,
            genres: Array.isArray(primaryMovie.genres) ? primaryMovie.genres.join(", ") : "",
            language: ytsLang,
            certification: primaryMovie.mpa_rating || "",
            rating: primaryMovie.rating ? Number(primaryMovie.rating).toFixed(1) : "",
            overview: primaryMovie.summary || primaryMovie.description_full || ""
          },
          posterUrl,
          releases
        };
      }
    } catch {}
  }

  for (const webBase of YTS_WEB_MIRRORS) {
    try {
      const browseUrl = `${webBase}/browse-movies/${encodeURIComponent(query)}/all/all/0/latest/0/all`;
      const { data: html } = await http.get(browseUrl, { timeout: 15000 });
      const $ = cheerio.load(html);

      const firstCard = $(".browse-movie-wrap").first();
      const posterRel = firstCard.find("img").attr("src") || "";
      const posterUrl = posterRel
        ? (posterRel.startsWith("http") ? posterRel : new URL(posterRel, webBase).href)
        : null;
      const movieTitle =
        firstCard.find(".browse-movie-title").text().trim() || query;

      const releases = [];
      const seenHashes = new Set();

      $('a[href^="magnet:?"]').each((_, el) => {
        const mag = ($(el).attr("href") || "").trim();
        const hash = extractInfoHash(mag);
        if (!hash || seenHashes.has(hash)) return;
        seenHashes.add(hash);

        const rowText = $(el).closest("div, tr, p").text().replace(/\s+/g, " ").trim();
        const qTag = detectQualityTag(`${rowText} ${mag}`) || "Release";
        releases.push({
          label: `${movieTitle} — ${qTag} (YTS.LU)`,
          quality: qTag,
          fileName: sanitizeFileName(`${movieTitle}-${qTag}-YTS.LU.torrent`),
          source: "YTS.LU",
          size: "",
          pageUrl: null,
          infoHash: hash,
          torrentUrl: null
        });
      });

      if (releases.length > 0) {
        return { movieTitle, posterUrl, releases };
      }
    } catch {}
  }

  return {
    movieTitle: query,
    posterUrl: null,
    releases: []
  };
}

const TMDB_MOVIE_GENRES = {
  28: "Action", 12: "Adventure", 16: "Animation", 35: "Comedy", 80: "Crime", 99: "Documentary",
  18: "Drama", 10751: "Family", 14: "Fantasy", 36: "History", 27: "Horror", 10402: "Music",
  9648: "Mystery", 10749: "Romance", 878: "Sci-Fi", 10770: "TV Movie", 53: "Thriller",
  10752: "War", 37: "Western"
};

function shortenText(text, max = 550) {
  const clean = String(text || "").replace(/<[^>]*>/g, " ").replace(/\s+/g, " ").trim();
  if (clean.length <= max) return clean;
  return clean.slice(0, max).replace(/\s+\S*$/, "") + "…";
}

const DETAILS_FOOTER = "©𝙼𝙿𝙼 𝚂𝚃𝚄𝙳𝙸𝙾";

function formatRuntime(minutes) {
  const total = parseInt(minutes, 10);
  if (!total || total < 1) return "";
  const h = Math.floor(total / 60);
  const m = total % 60;
  return h ? `${h}h ${m}m` : `${m}m`;
}

function omdbValue(v) {
  const t = String(v || "").trim();
  return !t || t === "N/A" ? "" : t;
}

async function fetchOmdb(title, year, type, imdbId) {
  const key = process.env.OMDB_API_KEY;
  if (!key || (!title && !imdbId)) return null;
  try {
    const res = await http.get("https://www.omdbapi.com/", {
      params: imdbId
        ? { apikey: key, i: imdbId }
        : { apikey: key, t: title, ...(year ? { y: year } : {}), ...(type ? { type } : {}) },
      timeout: 12000
    });
    return res.data?.Response === "True" ? res.data : null;
  } catch {
    return null;
  }
}

function collectQualities(releases) {
  const found = new Set();
  for (const r of releases || []) {
    const m = `${r.quality || ""} ${r.label || ""}`.match(/\b(2160p|1080p|720p|480p)\b/i);
    if (m) found.add(m[1].toLowerCase());
  }
  return ["2160p", "1080p", "720p", "480p"].filter((q) => found.has(q)).join(", ");
}

function joinDetailLines(parts) {
  return parts.filter((x) => x !== null && x !== undefined).join("\n");
}

async function tmdbGet(apiPath, params = {}) {
  const token = process.env.TMDB_READ_ACCESS_TOKEN;
  const key = process.env.TMDB_API_KEY;
  if (!token && !key) return null;
  try {
    const res = await http.get(`https://api.themoviedb.org/3${apiPath}`, {
      params: { ...(key ? { api_key: key } : {}), ...params },
      headers: token ? { Authorization: `Bearer ${token}` } : {},
      timeout: 12000
    });
    return res.data;
  } catch {
    return null;
  }
}

function tmdbLanguages(d) {
  const names = (d?.spoken_languages || []).map((l) => l.english_name || l.name).filter(Boolean);
  if (names.length) return names.join(", ");
  return d?.original_language ? String(d.original_language).toUpperCase() : "";
}

async function getTmdbMovieDetails(id) {
  if (!id) return null;
  const d = await tmdbGet(`/movie/${id}`, { append_to_response: "release_dates" });
  if (!d || !d.id) return null;
  const us = (d.release_dates?.results || []).find((r) => r.iso_3166_1 === "US");
  const certification = (us?.release_dates || []).map((x) => x.certification).find(Boolean) || "";
  return {
    year: d.release_date ? d.release_date.slice(0, 4) : "",
    runtime: d.runtime || 0,
    genres: (d.genres || []).map((g) => g.name).join(", "),
    language: tmdbLanguages(d),
    certification,
    rating: d.vote_average ? Number(d.vote_average).toFixed(1) : "",
    imdbId: d.imdb_id || "",
    overview: d.overview || ""
  };
}

async function getTmdbMovieByImdb(imdbId) {
  if (!imdbId) return null;
  const f = await tmdbGet(`/find/${imdbId}`, { external_source: "imdb_id" });
  const id = f?.movie_results?.[0]?.id;
  return id ? getTmdbMovieDetails(id) : null;
}

function fillMissing(primary, fallback) {
  if (!primary && !fallback) return null;
  const out = { ...(fallback || {}) };
  for (const [k, v] of Object.entries(primary || {})) if (v) out[k] = v;
  return out;
}

async function getTmdbTvDetails(title) {
  const found = await tmdbGet("/search/tv", { query: title });
  const id = found?.results?.[0]?.id;
  if (!id) return null;
  const d = await tmdbGet(`/tv/${id}`, { append_to_response: "content_ratings,external_ids" });
  if (!d || !d.id) return null;
  const statusMap = { "Returning Series": "Running", "Ended": "Ended", "Canceled": "Canceled" };
  const us = (d.content_ratings?.results || []).find((r) => r.iso_3166_1 === "US");
  return {
    name: d.name || title,
    year: d.first_air_date ? d.first_air_date.slice(0, 4) : "",
    runtime: (d.episode_run_time || [])[0] || d.last_episode_to_air?.runtime || 0,
    genres: (d.genres || []).map((g) => g.name).join(", "),
    language: tmdbLanguages(d),
    certification: us?.rating || "",
    rating: d.vote_average ? Number(d.vote_average).toFixed(1) : "",
    imdbId: d.external_ids?.imdb_id || "",
    status: statusMap[d.status] || d.status || "",
    network: d.networks?.[0]?.name || "",
    seasons: d.number_of_seasons || 0,
    overview: d.overview || ""
  };
}

function ratingLine(omdb, tmdbRating) {
  const imdb = omdbValue(omdb?.imdbRating);
  if (imdb) return `📝𝗜𝗠𝗗𝗕 : ${imdb}/10`;
  if (tmdbRating) return `📝𝗧𝗠𝗗𝗕 : ${tmdbRating}/10`;
  return null;
}

function formatMovieDetails(title, meta = {}, omdb = null, qualities = "", tmdb = null) {
  const year = tmdb?.year || omdbValue(omdb?.Year) || meta.year || "";
  const runtime = tmdb?.runtime ? formatRuntime(tmdb.runtime) : formatRuntime(parseInt(omdbValue(omdb?.Runtime), 10));
  const genres = tmdb?.genres || omdbValue(omdb?.Genre) || meta.genres || "";
  const langNote = process.env.DETAILS_LANGUAGE_NOTE ? `, ${process.env.DETAILS_LANGUAGE_NOTE}` : "";
  const baseLang = tmdb?.language || omdbValue(omdb?.Language) || meta.language || "";
  const language = baseLang ? `${baseLang}${langNote}` : "";
  const rated = tmdb?.certification || omdbValue(omdb?.Rated);
  const overview = shortenText(tmdb?.overview || meta.overview || omdbValue(omdb?.Plot), 480);
  try {
    const imdbScore = omdbValue(omdb?.imdbRating);
    const tmdbScore = tmdb?.rating || meta.rating || "";
    const storyline = overview ? `🔅sᴛᴏʀʏ ʟɪɴᴇ🔅\n\n> ${overview}` : "";
    return renderTemplate(getPosterTemplate("movie"), {
      title, typeline: `Movie${runtime ? ` | ~${runtime}` : ""}`, year: String(year || ""), runtime: runtime || "", genres: genres || "",
      language: language || "", quality: qualities || "", certification: rated || "",
      rating: String(imdbScore || tmdbScore || ""), rating_source: imdbScore ? "IMDb" : (tmdbScore ? "TMDB" : ""),
      rating_line: ratingLine(omdb, tmdbScore) || "", seasons: "", status: "", network: "", overview: overview || "", storyline, footer: DETAILS_FOOTER
    });
  } catch (e) { console.error("[template] movie render failed, using default layout:", e?.message || e); }
  return joinDetailLines([
    `🎥𝗧𝗶𝘁𝗹𝗲 : ${title}`,
    "",
    `> Movie${runtime ? ` | ~${runtime}` : ""}`,
    "",
    year ? `📅𝗬𝗲𝗮𝗿 : ${year}` : null,
    genres ? `🎭𝗚𝗲𝗻𝗿𝗲𝘀 : ${genres}` : null,
    language ? `📃𝗟𝗮𝗻𝗴𝘂𝗮𝗴𝗲 : ${language}` : null,
    qualities ? `📂𝗤𝘂𝗮𝗹𝗶𝘁𝘆 : ${qualities}` : null,
    rated ? `® 𝐑𝐚𝐭𝐢𝐧𝐠: ${rated}` : null,
    ratingLine(omdb, tmdb?.rating || meta.rating),
    overview ? "" : null,
    overview ? "🔅sᴛᴏʀʏ ʟɪɴᴇ🔅" : null,
    overview ? "" : null,
    overview ? `> ${overview}` : null,
    "",
    `> ${DETAILS_FOOTER}`
  ]);
}

async function getTvShowDetails(title) {
  try {
    const res = await http.get("https://api.tvmaze.com/singlesearch/shows", { params: { q: title }, timeout: 12000 });
    const show = res.data;
    if (!show?.name) return null;
    return {
      name: show.name,
      year: show.premiered ? show.premiered.slice(0, 4) : "",
      status: show.status || "",
      network: show.network?.name || show.webChannel?.name || "",
      genres: Array.isArray(show.genres) ? show.genres.join(", ") : "",
      rating: show.rating?.average ? Number(show.rating.average).toFixed(1) : "",
      language: show.language || "",
      runtime: show.runtime || show.averageRuntime || "",
      summary: shortenText(show.summary, 480)
    };
  } catch {
    return null;
  }
}

function formatTvDetails(title, d, filterBadge = "", omdb = null, qualities = "", tmdb = null) {
  const name = tmdb?.name || d?.name || title;
  const year = tmdb?.year || d?.year || omdbValue(omdb?.Year).slice(0, 4);
  const runtime = formatRuntime(tmdb?.runtime || d?.runtime);
  const genres = tmdb?.genres || d?.genres || omdbValue(omdb?.Genre);
  const langNote = process.env.DETAILS_LANGUAGE_NOTE ? `, ${process.env.DETAILS_LANGUAGE_NOTE}` : "";
  const baseLang = tmdb?.language || d?.language || omdbValue(omdb?.Language);
  const language = baseLang ? `${baseLang}${langNote}` : "";
  const rated = tmdb?.certification || omdbValue(omdb?.Rated);
  const status = tmdb?.status || d?.status;
  const network = tmdb?.network || d?.network;
  const overview = tmdb?.overview ? shortenText(tmdb.overview, 480) : (d?.summary || shortenText(omdbValue(omdb?.Plot), 480));
  try {
    const imdbScore = omdbValue(omdb?.imdbRating);
    const tmdbScore = tmdb?.rating || d?.rating || "";
    const storyline = overview ? `🔅sᴛᴏʀʏ ʟɪɴᴇ🔅\n\n> ${overview}` : "";
    return renderTemplate(getPosterTemplate("tv"), {
      title: `${name}${filterBadge}`, typeline: `TV Series${runtime ? ` | ~${runtime}` : ""}`, year: String(year || ""), runtime: runtime || "", genres: genres || "",
      language: language || "", quality: qualities || "", certification: rated || "",
      rating: String(imdbScore || tmdbScore || ""), rating_source: imdbScore ? "IMDb" : (tmdbScore ? "TMDB" : ""),
      rating_line: ratingLine(omdb, tmdbScore) || "", seasons: tmdb?.seasons ? String(tmdb.seasons) : "", status: status || "", network: network || "",
      overview: overview || "", storyline, footer: DETAILS_FOOTER
    });
  } catch (e) { console.error("[template] tv render failed, using default layout:", e?.message || e); }
  return joinDetailLines([
    `📺𝗧𝗶𝘁𝗹𝗲 : ${name}${filterBadge}`,
    "",
    `> TV Series${runtime ? ` | ~${runtime}` : ""}`,
    "",
    year ? `📅𝗬𝗲𝗮𝗿 : ${year}` : null,
    tmdb?.seasons ? `🎞️𝗦𝗲𝗮𝘀𝗼𝗻𝘀 : ${tmdb.seasons}` : null,
    status ? `📡𝗦𝘁𝗮𝘁𝘂𝘀 : ${status}` : null,
    network ? `🏢𝗡𝗲𝘁𝘄𝗼𝗿𝗸 : ${network}` : null,
    genres ? `🎭𝗚𝗲𝗻𝗿𝗲𝘀 : ${genres}` : null,
    language ? `📃𝗟𝗮𝗻𝗴𝘂𝗮𝗴𝗲 : ${language}` : null,
    qualities ? `📂𝗤𝘂𝗮𝗹𝗶𝘁𝘆 : ${qualities}` : null,
    rated ? `® 𝐑𝐚𝐭𝐢𝐧𝐠: ${rated}` : null,
    ratingLine(omdb, tmdb?.rating || d?.rating),
    overview ? "" : null,
    overview ? "🔅sᴛᴏʀʏ ʟɪɴᴇ🔅" : null,
    overview ? "" : null,
    overview ? `> ${overview}` : null,
    "",
    `> ${DETAILS_FOOTER}`
  ]);
}

async function sendDetailsThenList(sock, jid, posterUrl, detailsText, listText) {
  let sentDetails = false;
  if (posterUrl) {
    try {
      await sock.sendMessage(jid, { image: { url: posterUrl }, caption: detailsText });
      sentDetails = true;
    } catch {}
  }
  if (!sentDetails) await sock.sendMessage(jid, { text: detailsText });
  await sock.sendMessage(jid, { text: listText });
}

async function lookupMovieMeta(query) {
  const tmdbToken = process.env.TMDB_READ_ACCESS_TOKEN;
  const tmdbKey = process.env.TMDB_API_KEY;
  if (tmdbToken || tmdbKey) {
    try {
      const headers = tmdbToken ? { Authorization: `Bearer ${tmdbToken}` } : {};
      const res = await http.get("https://api.themoviedb.org/3/search/movie", {
        params: { query, ...(tmdbKey ? { api_key: tmdbKey } : {}) }, headers, timeout: 12000
      });
      const movie = res.data?.results?.[0];
      if (movie) return {
        id: movie.id,
        title: movie.title || query,
        posterUrl: movie.poster_path ? `https://image.tmdb.org/t/p/w500${movie.poster_path}` : null,
        year: movie.release_date ? movie.release_date.slice(0, 4) : "",
        overview: movie.overview || "",
        rating: movie.vote_average ? Number(movie.vote_average).toFixed(1) : "",
        genres: (movie.genre_ids || []).map((id) => TMDB_MOVIE_GENRES[id]).filter(Boolean).join(", "),
        language: movie.original_language ? String(movie.original_language).toUpperCase() : "",
        source: "TMDB"
      };
    } catch {}
  }
  try {
    const res = await http.get("https://www.wikidata.org/w/api.php", {
      params: { action: "wbsearchentities", search: query, language: "en", format: "json", type: "item", limit: 5 },
      headers: { "User-Agent": "MPM-WhatsApp-Bot/1.0 (movie metadata lookup)" }, timeout: 12000
    });
    const hit = (res.data?.search || []).find(x => /film|movie|television film/i.test(x.description || ""));
    if (hit) return { title: hit.label || query, posterUrl: null, year: "", overview: hit.description || "", source: "Wikidata" };
  } catch {}
  return { title: query, posterUrl: null, year: "", overview: "", source: "None" };
}

function isOpenLicenseMetadata(meta) {
  const license = String(meta?.licenseurl || "").toLowerCase();
  const rights = String(meta?.rights || "").toLowerCase();
  return license.includes("creativecommons.org/licenses/") ||
    license.includes("creativecommons.org/publicdomain/") ||
    /public domain|creative commons|cc0|cc-by|cc-by-sa/.test(rights);
}

async function searchLegalArchiveFilms(query) {
  const search = await http.get("https://archive.org/advancedsearch.php", {
    params: { q: `mediatype:movies AND title:(${query})`, fl: ["identifier", "title", "year"], rows: 15, page: 1, output: "json" },
    timeout: 16000
  });
  const docs = search.data?.response?.docs || [];
  const checked = await Promise.allSettled(docs.slice(0, 12).map(async (doc) => {
    if (!doc.identifier) return null;
    const metaRes = await http.get(`https://archive.org/metadata/${encodeURIComponent(doc.identifier)}`, { timeout: 12000 });
    const meta = metaRes.data?.metadata || {};
    if (!isOpenLicenseMetadata(meta)) return null;
    const videoFiles = (Array.isArray(metaRes.data?.files) ? metaRes.data.files : [])
      .filter(file => /\.(mp4|m4v|webm|ogv|avi|mkv)$/i.test(String(file.name || "")))
      .slice(0, 5)
      .map(file => {
        const name = String(file.name || "");
        const quality = detectQualityTag(name) || "Quality not listed";
        return { name, quality, size: file.size ? formatBytes(Number(file.size)) : "Size not listed" };
      });
    return {
      title: doc.title || meta.title || doc.identifier,
      year: doc.year || meta.year || "",
      rights: meta.licenseurl || meta.rights || "Open license",
      files: videoFiles,
      url: `https://archive.org/details/${encodeURIComponent(doc.identifier)}`
    };
  }));
  return checked.filter(x => x.status === "fulfilled" && x.value).map(x => x.value).slice(0, 8);
}

async function searchWikimediaCommonsVideos(query) {
  const res = await http.get("https://commons.wikimedia.org/w/api.php", {
    params: {
      action: "query", generator: "search", gsrsearch: `${query} filetype:video`,
      gsrnamespace: 6, gsrlimit: 8, prop: "imageinfo",
      iiprop: "url|size|mime|extmetadata", format: "json", formatversion: 2
    },
    headers: { "User-Agent": "MPM-WhatsApp-Bot/1.0 (open-license film lookup)" },
    timeout: 15000
  });
  const pages = Array.isArray(res.data?.query?.pages) ? res.data.query.pages : [];
  return pages
    .sort((a, b) => (a.index || 0) - (b.index || 0))
    .map((page) => {
      const info = page.imageinfo?.[0];
      if (!info) return null;
      const licenseName = String(info.extmetadata?.LicenseShortName?.value || "").trim();
      if (!licenseName) return null;
      const fileName = String(page.title || "").replace(/^File:/i, "");
      return {
        title: fileName.replace(/\.[a-z0-9]+$/i, "").replace(/_/g, " "),
        year: "",
        rights: licenseName,
        files: [{
          name: fileName,
          quality: detectQualityTag(fileName) || "Quality not listed",
          size: info.size ? formatBytes(Number(info.size)) : "Size not listed"
        }],
        url: info.descriptionurl || info.url,
        source: "Wikimedia Commons"
      };
    })
    .filter(Boolean)
    .slice(0, 5);
}

async function lookupTvShowMeta(showQuery) {
  try {
    const res = await http.get("https://api.tvmaze.com/singlesearch/shows", {
      params: { q: showQuery },
      timeout: 12000
    });
    const show = res.data;
    if (!show) return { showTitle: showQuery, posterUrl: null, imdbId: null };
    return {
      showTitle: show.name || showQuery,
      posterUrl: show.image?.original || show.image?.medium || null,
      imdbId: show.externals?.imdb || null
    };
  } catch {
    return { showTitle: showQuery, posterUrl: null, imdbId: null };
  }
}

async function lookupTvShowSeasons(showQuery) {
  const showRes = await http.get("https://api.tvmaze.com/singlesearch/shows", {
    params: { q: showQuery }, timeout: 12000
  });
  const show = showRes.data;
  if (!show?.id) return null;
  const [seasonRes, episodeRes] = await Promise.all([
    http.get(`https://api.tvmaze.com/shows/${show.id}/seasons`, { timeout: 12000 }),
    http.get(`https://api.tvmaze.com/shows/${show.id}/episodes`, { params: { specials: 0 }, timeout: 12000 })
  ]);
  const seasons = Array.isArray(seasonRes.data) ? seasonRes.data : [];
  const episodes = Array.isArray(episodeRes.data) ? episodeRes.data : [];
  const counts = new Map();
  for (const episode of episodes) counts.set(episode.season, (counts.get(episode.season) || 0) + 1);
  return {
    name: show.name || showQuery,
    premiered: show.premiered || "Unknown",
    status: show.status || "Unknown",
    network: show.network?.name || show.webChannel?.name || "Unknown",
    genres: Array.isArray(show.genres) ? show.genres.join(", ") : "",
    image: show.image?.medium || null,
    seasons: seasons.map(season => ({ number: season.number, episodeCount: counts.get(season.number) || 0, premiere: season.premiereDate || "Unknown", finale: season.endDate || "Ongoing" }))
  };
}

async function searchEztvByImdb(imdbId) {
  const cleanImdb = String(imdbId || "").replace(/^tt/i, "").trim();
  if (!/^\d+$/.test(cleanImdb)) return [];

  for (const baseUrl of EZTV_API_MIRRORS) {
    try {
      const res = await http.get(baseUrl, {
        params: { imdb_id: cleanImdb, limit: 35, page: 1 },
        timeout: 15000
      });
      const torrents = res.data?.torrents;
      if (!Array.isArray(torrents) || torrents.length === 0) continue;

      return torrents.slice(0, 25).map((t) => ({
        label: t.title || t.filename || `Episode_${t.id}`,
        quality: detectQualityTag(t.title || t.filename || ""),
        fileName: sanitizeFileName(`${t.filename || t.title || `eztv_${t.id}`}.torrent`),
        source: "EZTV",
        size: formatBytes(t.size_bytes),
        pageUrl: null,
        infoHash: t.hash || null,
        torrentUrl: t.torrent_url || null
      }));
    } catch {}
  }
  return [];
}

async function buildTvShowReleaseList(rawInput) {
  const imdbMatch = rawInput.match(/\b(tt\d+)\b/i);
  const explicitImdb = imdbMatch ? imdbMatch[1] : null;
  const withoutImdb = rawInput.replace(/\btt\d+\b/i, "").trim();
  const seFilter = parseSeasonEpisodeFilter(withoutImdb || rawInput);
  const showName = seFilter.cleanedQuery || explicitImdb || rawInput;

  const meta = explicitImdb
    ? { showTitle: withoutImdb || rawInput, posterUrl: null, imdbId: explicitImdb }
    : await lookupTvShowMeta(showName);

  const effectiveImdb = meta.imdbId || explicitImdb;
  const searchTitle = meta.showTitle || showName;

  const queries = [searchTitle];
  if (seFilter.mode === "episode" && seFilter.code) {
    queries.push(`${searchTitle} ${seFilter.code}`);
  } else if (seFilter.mode === "season" && seFilter.seasonCode) {
    queries.push(`${searchTitle} ${seFilter.seasonCode}`);
    queries.push(`${searchTitle} Season ${seFilter.season}`);
    if (seFilter.packRequested) {
      queries.push(`${searchTitle} ${seFilter.seasonCode} Complete`);
      queries.push(`${searchTitle} Season ${seFilter.season} Complete Pack`);
      queries.push(`${searchTitle} ${seFilter.seasonCode} 720p`);
    }
  } else if (seFilter.mode === "pack") {
    queries.push(`${searchTitle} Season Pack`);
    queries.push(`${searchTitle} Complete`);
  }

  const [eztvList, ...extraLists] = await Promise.all([
    effectiveImdb ? searchEztvByImdb(effectiveImdb) : Promise.resolve([]),
    ...queries.map((q) => searchApiBayMirrors(q, { requirePsa: false, category: "205" })),
    ...queries.map((q) => searchExtraIndexers(q, { requirePsa: false })),
    ...queries.map((q) => searchWatchSoMuchPsa(q))
  ]);

  const combined = [
    ...eztvList.slice(0, 15),
    ...extraLists.flat()
  ];

  const unique = [];
  const seen = new Set();
  for (const r of combined) {
    const key = `${r.infoHash || ""}|${r.torrentUrl || ""}|${r.pageUrl || ""}|${r.label.toLowerCase()}`;
    if (seen.has(key)) continue;
    seen.add(key);
    unique.push(r);
  }

  let qualityMatched = unique;
  if (seFilter.quality) {
    const byQuality = unique.filter((r) => new RegExp(`\\b${seFilter.quality}\\b`, 'i').test(r.label));
    if (byQuality.length) qualityMatched = byQuality;
  }
  const ordered = orderAndFilterReleases(qualityMatched, {
    seFilter,
    preferPacks: seFilter.mode === "pack" || seFilter.mode === "season" || seFilter.packRequested
  });

  return {
    showTitle: searchTitle,
    posterUrl: meta.posterUrl,
    seFilter,
    isTvShow: true,
    releases: ordered.slice(0, 30)
  };
}

async function buildMovieReleaseList(query) {
  const [ytsData, wsmPsa, pubPsa, extraPsa, metadata] = await Promise.all([
    searchYtsReleasesForMovie(query),
    searchWatchSoMuchPsa(query),
    searchApiBayMirrors(`${query} PSA`, { requirePsa: true, category: "207" }),
    searchExtraIndexers(`${query} PSA`, { requirePsa: true }),
    lookupMovieMeta(query)
  ]);

  const combined = [
    ...pubPsa.slice(0, 10),
    ...extraPsa.slice(0, 10),
    ...wsmPsa.slice(0, 8),
    ...ytsData.releases.slice(0, 12)
  ];

  const uniqueReleases = [];
  const seen = new Set();
  for (const r of combined) {
    const key = `${r.infoHash || ""}|${r.torrentUrl || ""}|${r.label.toLowerCase()}`;
    if (seen.has(key)) continue;
    seen.add(key);
    uniqueReleases.push(r);
  }

  return {
    movieTitle: ytsData.movieTitle || metadata.title || query,
    cleanTitle: ytsData.cleanTitle || metadata.title || query,
    ytsMeta: ytsData.ytsMeta || null,
    posterUrl: ytsData.posterUrl || metadata.posterUrl || null,
    metadata,
    isTvShow: false,
    releases: uniqueReleases.slice(0, 30)
  };
}

async function sendTorrentFileOnly(sock, jid, resolved) {
  const buf = await fetchTorrentFileBuffer(resolved.torrentUrl, resolved.infoHash);

  if (buf) {
    const fileName = resolved.fileName.toLowerCase().endsWith(".torrent")
      ? resolved.fileName
      : `${resolved.fileName}.torrent`;
    const tempPath = path.join(TEMP_DIR, `${Date.now()}_${fileName}`);
    fs.writeFileSync(tempPath, buf);

    try {
      const sizeLine = resolved.size ? `\n💾 Size: *${resolved.size}*` : "";
      await sock.sendMessage(jid, {
        document: fs.readFileSync(tempPath),
        mimetype: "application/x-bittorrent",
        fileName,
        caption: `🎬 *${resolved.label}*\n📦 Source: *${resolved.source}*${sizeLine}`
      });
      return true;
    } finally {
      if (fs.existsSync(tempPath)) fs.unlinkSync(tempPath);
    }
  }

  return false;
}

function isTvEpisodeOrShowFile(filePath, resolved) {
  if (resolved?.isTvShow) return true;
  const combined = `${filePath} ${resolved?.label || ""}`;
  return /\bS\d{1,2}(?:E\d{1,3}|\b)|\bseason\s*\d{1,2}\b|\bepisode\s*\d{1,3}\b/i.test(combined);
}

function getEpisodeSortKey(filePath) {
  const base = path.basename(filePath);
  const seMatch = base.match(/S(\d{1,2})E(\d{1,3})/i);
  if (seMatch) {
    return {
      hasSe: 0,
      season: Number(seMatch[1]),
      episode: Number(seMatch[2]),
      name: base.toLowerCase()
    };
  }
  const epOnly = base.match(/\b(?:EP?|Episode)[._\-\s]*(\d{1,3})\b/i);
  if (epOnly) {
    return {
      hasSe: 1,
      season: 0,
      episode: Number(epOnly[1]),
      name: base.toLowerCase()
    };
  }
  return {
    hasSe: 2,
    season: 999,
    episode: 999,
    name: base.toLowerCase()
  };
}

function compareEpisodeFiles(a, b) {
  const ka = getEpisodeSortKey(a);
  const kb = getEpisodeSortKey(b);
  if (ka.hasSe !== kb.hasSe) return ka.hasSe - kb.hasSe;
  if (ka.season !== kb.season) return ka.season - kb.season;
  if (ka.episode !== kb.episode) return ka.episode - kb.episode;
  return ka.name.localeCompare(kb.name, undefined, { numeric: true, sensitivity: "base" });
}

async function extractZipArchivesInFolder(rootFolder) {
  const AdmZip = await getAdmZipConstructor();
  const pendingZips = [];

  const scanForZips = (dir) => {
    for (const entry of fs.readdirSync(dir, { withFileTypes: true })) {
      const full = path.join(dir, entry.name);
      if (entry.isDirectory()) {
        scanForZips(full);
      } else if (entry.isFile() && path.extname(entry.name).toLowerCase() === ".zip") {
        pendingZips.push(full);
      }
    }
  };

  scanForZips(rootFolder);
  if (pendingZips.length === 0) return;

  if (!AdmZip) {
    throw new Error("ZIP archive found, but `adm-zip` is not installed. Run `npm install`.");
  }

  let extractedCount = 0;
  for (const zipPath of pendingZips) {
    const extractDest = path.join(
      path.dirname(zipPath),
      `extracted_${path.basename(zipPath, path.extname(zipPath))}_${Date.now()}`
    );
    fs.mkdirSync(extractDest, { recursive: true });
    const zip = new AdmZip(zipPath);
    zip.extractAllTo(extractDest, true);
    extractedCount++;
    try {
      fs.unlinkSync(zipPath);
    } catch {}
  }

  if (extractedCount > 0) {
    await extractZipArchivesInFolder(rootFolder);
  }
}

function collectFilesRecursively(dirPath, acc = []) {
  if (!fs.existsSync(dirPath)) return acc;
  for (const entry of fs.readdirSync(dirPath, { withFileTypes: true })) {
    const full = path.join(dirPath, entry.name);
    if (entry.isDirectory()) {
      collectFilesRecursively(full, acc);
    } else if (entry.isFile()) {
      acc.push(full);
    }
  }
  return acc;
}

function guessMimeType(filePath) {
  const ext = path.extname(filePath).toLowerCase();
  if (ext === ".mp4") return "video/mp4";
  if (ext === ".mkv") return "video/x-matroska";
  if (ext === ".avi") return "video/x-msvideo";
  if (ext === ".mov") return "video/quicktime";
  if (ext === ".webm") return "video/webm";
  if (ext === ".mp3") return "audio/mpeg";
  if (ext === ".flac") return "audio/flac";
  if (ext === ".zip") return "application/zip";
  if (ext === ".rar") return "application/x-rar-compressed";
  if (ext === ".srt") return "application/x-subrip";
  return "application/octet-stream";
}

function findAria2cBinary() {
  const localCandidates = [
    path.join(process.cwd(), "aria2c.exe"),
    path.join(process.cwd(), "bin", "aria2c.exe"),
    path.join(process.cwd(), "aria2", "aria2c.exe")
  ];
  for (const p of localCandidates) {
    if (fs.existsSync(p)) return p;
  }
  return process.platform === "win32" ? "aria2c.exe" : "aria2c";
}

function parseAria2ProgressLine(line) {
  const pctMatch = line.match(/\((\d{1,3}(?:\.\d+)?)%\)/);
  const sizeMatch = line.match(/([0-9.]+\s*[KMGTP]?i?B)\s*\/\s*([0-9.]+\s*[KMGTP]?i?B)/i);
  const dlMatch = line.match(/ DL:([0-9.]+\s*[KMGTP]?i?B(?:\/s)?)/i);
  const etaMatch = line.match(/ ETA:([0-9a-zA-Z]+)/i);

  if (!pctMatch && !sizeMatch && !dlMatch) return null;

  const pct = pctMatch ? Number(pctMatch[1]).toFixed(1) : null;
  const downloadedText = sizeMatch ? sizeMatch[1].replace(/\s+/g, " ") : null;
  const totalText = sizeMatch ? sizeMatch[2].replace(/\s+/g, " ") : null;
  const speedText = dlMatch
    ? `${dlMatch[1].replace(/\s+/g, "")}${dlMatch[1].includes("/") ? "" : "/s"}`
    : null;
  const etaText = etaMatch ? etaMatch[1] : null;

  return { pct, downloadedText, totalText, speedText, etaText };
}

async function leechTorrentAndUpload(sock, jid, quotedMsg, resolved) {
  let rawHash = extractInfoHash(resolved.infoHash || resolved.magnet || "");
  let magnetUri = buildMagnetUri(resolved);
  let ariaSource = null;
  let tempTorrentPath = null;

  if (typeof magnetUri === "string" && /^magnet:\?xt=urn:btih:[a-fA-F0-9]{40}/i.test(magnetUri.trim())) {
    ariaSource = magnetUri.trim();
  } else {
    const torrentBuf = await fetchTorrentFileBuffer(resolved.torrentUrl, resolved.infoHash);
    if (Buffer.isBuffer(torrentBuf) && torrentBuf.length >= 100) {
      tempTorrentPath = path.join(TEMP_DIR, `aria_${Date.now()}_${Math.random().toString(36).slice(2, 7)}.torrent`);
      fs.writeFileSync(tempTorrentPath, torrentBuf);
      ariaSource = tempTorrentPath;
    } else if (rawHash) {
      ariaSource = `magnet:?xt=urn:btih:${rawHash}&dn=${encodeURIComponent(resolved.label || "Torrent")}${PUBLIC_TRACKERS.map((t) => `&tr=${encodeURIComponent(t)}`).join("")}`;
    }
  }

  if (!ariaSource) {
    throw new Error("Could not find a valid Magnet Link or .torrent file for aria2c.");
  }

  const ariaBin = findAria2cBinary();
  const sessionFolder = path.join(LEECH_DIR, `aria_${Date.now()}_${Math.random().toString(36).slice(2, 7)}`);
  fs.mkdirSync(sessionFolder, { recursive: true });

  const statusMsg = await sock.sendMessage(
    jid,
    {
      text:
        `⚡ *aria2c Leech Started...*\n` +
        `🎬 *${resolved.label}*\n` +
        `📦 Source: *${resolved.source}*\n` +
        `📈 *Progress:* *0.0%*\n` +
        `📥 *Downloaded:* *0.0 MB*\n` +
        `📤 *Remaining:* *Calculating...*\n` +
        `🚀 *Speed:* *0.0 KB/s*\n` +
        `_(ZIP files >1.99 GB are downloaded & extracted; individual non-ZIP files >1.99 GB are not uploaded)_`
    },
    quotedMsg ? { quoted: quotedMsg } : undefined
  );

  let lastProgressText = "";
  let lastProgressAt = 0;

  const taskEntry = {
    cancelled: false,
    startedAt: Date.now(),
    label: resolved.label,
    source: resolved.source,
    stage: "Starting aria2c",
    pct: "0.0",
    downloadedText: "0.0 MB",
    remainingText: "Calculating...",
    speedText: "0.0 KB/s",
    cancelFn: null
  };
  activeTasksByChat.set(jid, taskEntry);

  const updateProgress = async (stageText, detailsText, meta = {}) => {
    taskEntry.stage = stageText.replace(/[*_]/g, "");
    if (meta.pct !== undefined) taskEntry.pct = String(meta.pct);
    if (meta.downloadedText !== undefined) taskEntry.downloadedText = meta.downloadedText;
    if (meta.remainingText !== undefined) taskEntry.remainingText = meta.remainingText;
    if (meta.speedText !== undefined) taskEntry.speedText = meta.speedText;

    const text = `${stageText}\n🎬 *${resolved.label}*\n${detailsText}`;
    if (text === lastProgressText) return;
    lastProgressText = text;
    lastProgressAt = Date.now();

    try {
      if (statusMsg?.key) {
        await sock.sendMessage(jid, { text, edit: statusMsg.key });
      } else {
        await sock.sendMessage(jid, { text });
      }
    } catch {}
  };

  return new Promise((resolve, reject) => {
    let settled = false;
    let ariaProc = null;
    let progressInterval = null;
    let stderrTail = "";
    const timeoutMs = 600000;

    const cleanup = () => {
      if (progressInterval) { clearInterval(progressInterval); progressInterval = null; }
      if (activeTasksByChat.get(jid) === taskEntry) activeTasksByChat.delete(jid);
      if (tempTorrentPath && fs.existsSync(tempTorrentPath)) {
        try { fs.unlinkSync(tempTorrentPath); } catch {}
      }
      try { fs.rmSync(sessionFolder, { recursive: true, force: true }); } catch {}
    };

    const fail = (err) => {
      if (settled) return;
      settled = true;
      clearTimeout(timer);
      try { if (ariaProc && !ariaProc.killed) ariaProc.kill("SIGKILL"); } catch {}
      cleanup();
      reject(err);
    };

    taskEntry.cancelFn = () => fail(new Error("Task cancelled by user."));

    const timer = setTimeout(() => {
      fail(new Error("aria2c leech timeout (10m). Seeders may be low or the connection may be slow."));
    }, timeoutMs);

    const args = [
      "--dir", sessionFolder,
      "--seed-time=0",
      "--bt-enable-lpd=true",
      "--enable-dht=true",
      "--enable-peer-exchange=true",
      "--bt-save-metadata=false",
      "--summary-interval=2",
      "--console-log-level=notice",
      "--file-allocation=none",
      "--max-connection-per-server=8",
      "--split=8",
      ariaSource
    ];

    try {
      ariaProc = spawn(ariaBin, args, { windowsHide: true, stdio: ["ignore", "pipe", "pipe"] });
    } catch (spawnErr) {
      fail(new Error(`Could not start aria2c (${ariaBin}). Install aria2c and add it to PATH or place aria2c.exe in the bot folder. (${spawnErr?.message || spawnErr})`));
      return;
    }

    const handleOutputChunk = (chunk) => {
      const text = String(chunk || "");
      for (const rawLine of text.split(/\r?\n/)) {
        const line = rawLine.trim();
        if (!line) continue;
        const parsed = parseAria2ProgressLine(line);
        if (parsed) {
          if (parsed.pct !== null) taskEntry.pct = parsed.pct;
          if (parsed.downloadedText) taskEntry.downloadedText = parsed.downloadedText;
          if (parsed.speedText) taskEntry.speedText = parsed.speedText;
          if (parsed.totalText && parsed.downloadedText) taskEntry.remainingText = parsed.totalText;
          else if (parsed.etaText) taskEntry.remainingText = `ETA ${parsed.etaText}`;
        }
      }
    };

    ariaProc.stdout?.on("data", handleOutputChunk);
    ariaProc.stderr?.on("data", (chunk) => {
      stderrTail = `${stderrTail}\n${String(chunk || "")}`.slice(-1200);
      handleOutputChunk(chunk);
    });

    ariaProc.on("error", (procErr) => {
      if (procErr?.code === "ENOENT") {
        fail(new Error("aria2c was not found. Please install aria2c (or put aria2c.exe in the bot folder) and try again."));
      } else {
        fail(new Error(`aria2c process error: ${procErr.message}`));
      }
    });

    progressInterval = setInterval(() => {
      if (settled || taskEntry.cancelled) return;
      if (Date.now() - lastProgressAt < 2500) return;

      void updateProgress(
        "⬇️ *Leeching with aria2c...*",
        `📈 *Progress:* *${taskEntry.pct}%*\n📥 *Downloaded:* *${taskEntry.downloadedText}*\n📤 *Remaining:* *${taskEntry.remainingText}*\n🚀 *Speed:* *${taskEntry.speedText}*`
      );
    }, 3000);

    ariaProc.on("close", async (code) => {
      if (settled || taskEntry.cancelled) return;
      if (progressInterval) { clearInterval(progressInterval); progressInterval = null; }

      if (code !== 0) {
        const cleanErr = stderrTail.trim().split("\n").filter(Boolean).slice(-2).join(" | ");
        fail(new Error(cleanErr ? `aria2c exited with code ${code}: ${cleanErr}` : `aria2c exited with code ${code}. Torrent may have no active seeders.`));
        return;
      }

      clearTimeout(timer);

      try {
        const doneMbStr = taskEntry.downloadedText || "0.0 MB";
        await updateProgress(
          "📦 *Extracting & Preparing Files...*",
          `📈 *Progress:* *100.0%*\n📥 *Downloaded:* *${doneMbStr}*\n📤 *Remaining:* *0.0 MB*`,
          { pct: "100.0", downloadedText: doneMbStr, remainingText: "0.0 MB", speedText: "0.0 KB/s" }
        );
        if (taskEntry.cancelled) throw new Error("Task cancelled by user.");

        const zipFilesFound = collectFilesRecursively(sessionFolder).filter(
          (f) => path.extname(f).toLowerCase() === ".zip"
        );
        if (zipFilesFound.length > 0) {
          const zipNames = zipFilesFound.map((z) => path.basename(z)).join(", ");
          await sock.sendMessage(jid, {
            text: `🗜️ *ZIP Pack Ready:* Extracting *${zipNames}* (including >2 GB ZIP archives) to upload episodes in order...`
          });
        }

        await extractZipArchivesInFolder(sessionFolder);
        if (taskEntry.cancelled) throw new Error("Task cancelled by user.");

        const allFiles = collectFilesRecursively(sessionFolder).filter((f) => fs.statSync(f).size > 0);
        if (allFiles.length === 0) throw new Error("No leeched files were found.");

        const hasEpisodesOrTv =
          isTvEpisodeOrShowFile(sessionFolder, resolved) ||
          allFiles.some((f) => /S\d{1,2}E\d{1,3}|\b(?:EP?|Episode)[._\-\s]*\d{1,3}\b/i.test(path.basename(f)));

        const eligibleFiles = allFiles.filter((f) => {
          if (path.extname(f).toLowerCase() === ".zip") return true;
          return fs.statSync(f).size <= MAX_UPLOAD_BYTES;
        });

        const skippedOversizedFiles = allFiles.filter((f) => {
          if (path.extname(f).toLowerCase() === ".zip") return false;
          return fs.statSync(f).size > MAX_UPLOAD_BYTES;
        });

        for (const skippedFile of skippedOversizedFiles) {
          const sName = path.basename(skippedFile);
          const sSize = formatBytes(fs.statSync(skippedFile).size);
          await sock.sendMessage(jid, {
            text: `❌ *File too large:* \`${sName}\`${sSize ? ` *(${sSize})*` : ""}\nMaximum upload size is *1.99 GB*. This file was *not uploaded*.`
          });
        }

        const orderedFiles = hasEpisodesOrTv
          ? [...eligibleFiles].sort(compareEpisodeFiles)
          : [...eligibleFiles].sort((a, b) => fs.statSync(b).size - fs.statSync(a).size);

        if (orderedFiles.length === 0) {
          throw new Error("All files are larger than the 1.99 GB upload limit, so nothing was uploaded.");
        }

        const maxFilesToUpload = hasEpisodesOrTv ? 100 : 8;
        const filesToUpload = orderedFiles.slice(0, maxFilesToUpload);
        const totalToUpload = filesToUpload.length;

        for (let idx = 0; idx < totalToUpload; idx++) {
          if (taskEntry.cancelled) throw new Error("Task cancelled by user.");
          const filePath = filesToUpload[idx];
          const stat = fs.statSync(filePath);
          const baseName = path.basename(filePath);
          const mime = guessMimeType(filePath);
          const sizeStr = formatBytes(stat.size);
          const uploadPct = (((idx + 1) / totalToUpload) * 100).toFixed(1);

          await updateProgress(
            `⬆️ *Uploading (${idx + 1}/${totalToUpload})...*`,
            `📈 *Progress:* *${uploadPct}%*\n📄 *File:* \`${baseName}\`${sizeStr ? ` _(${sizeStr})_` : ""}`,
            { pct: uploadPct, downloadedText: doneMbStr, remainingText: "0.0 MB", speedText: "Uploading" }
          );

          if (taskEntry.cancelled) throw new Error("Task cancelled by user.");
          await waitUploadGap(taskEntry);
          if (taskEntry.cancelled) throw new Error("Task cancelled by user.");

          if (mime.startsWith("video/") && stat.size <= 64 * 1024 * 1024) {
            await sendAndMarkUpload(jid, {
              video: { url: filePath },
              mimetype: mime,
              fileName: baseName,
              caption: `✅ *Uploaded (${idx + 1}/${totalToUpload}):* *${baseName}*${sizeStr ? ` _(${sizeStr})_` : ""}`
            });
          } else {
            await sendAndMarkUpload(jid, {
              document: { url: filePath },
              mimetype: mime,
              fileName: baseName,
              caption: `✅ *Uploaded (${idx + 1}/${totalToUpload}):* *${baseName}*${sizeStr ? ` _(${sizeStr})_` : ""}`
            });
          }
        }

        if (taskEntry.cancelled) throw new Error("Task cancelled by user.");

        const notes = [];
        if (skippedOversizedFiles.length > 0) {
          notes.push(`ℹ️ Files too large to upload (>1.99 GB): *${skippedOversizedFiles.length}*`);
        }
        if (orderedFiles.length > maxFilesToUpload) {
          notes.push(`ℹ️ Uploaded *${maxFilesToUpload}* of *${orderedFiles.length}* eligible files.`);
        }
        if (notes.length > 0) {
          await sock.sendMessage(jid, { text: notes.join("\n") });
        }

        settled = true;
        cleanup();
        resolve(true);
      } catch (err) {
        fail(err);
      }
    });
  });
}

// ============================================================================
// FitGirl Repacks (,fg <game>) -> search -> pick -> 1 = torrent, 2 = select files -> RAR name -> leech
// ============================================================================
const FITGIRL_BASE = "https://fitgirl-repacks.site";
const FG_TTL_MS = 10 * 60 * 1000;
const pendingFgSearchByChat = new Map();
const pendingFgActionByChat = new Map();
const pendingFgFileSelectByChat = new Map();
const pendingFgRarNameByChat = new Map();

function fgSenderKey(msg) {
  return String(msg.key.participant || msg.key.remoteJid || "");
}
function getFgPending(map, jid, msg) {
  const s = map.get(jid);
  if (!s) return null;
  if (Date.now() - (s.createdAt || 0) > FG_TTL_MS) { map.delete(jid); return null; }
  if (s.senderKey && msg && s.senderKey !== fgSenderKey(msg)) return null;
  return s;
}
function clearFgPending(jid) {
  pendingFgSearchByChat.delete(jid);
  pendingFgActionByChat.delete(jid);
  pendingFgFileSelectByChat.delete(jid);
  pendingFgRarNameByChat.delete(jid);
}

// Parse inputs like: 1-10 | 1,10 | 1-10,12 | 2,5,8 | all
function parseFgFileSelection(rawText, totalFiles) {
  const raw = String(rawText || "").trim().toLowerCase();
  if (!raw) return { error: "empty" };
  if (raw === "all" || raw === "*") {
    return { all: true, indexes: Array.from({ length: totalFiles }, (_, i) => i) };
  }
  const normalized = raw
    .replace(/\s*(?:to|-|–|—)\s*/g, "-")
    .replace(/\s*,\s*/g, ",")
    .replace(/\s+/g, ",");
  const picked = new Set();
  for (const part of normalized.split(",").filter(Boolean)) {
    const m = part.match(/^(\d+)(?:-(\d+))?$/);
    if (!m) return { error: "bad" };
    const start = Number(m[1]);
    const end = m[2] !== undefined ? Number(m[2]) : start;
    if (start < 1 || end < start || end > totalFiles) return { error: "range", totalFiles };
    for (let n = start; n <= end; n++) picked.add(n - 1);
  }
  if (!picked.size) return { error: "bad" };
  return { all: false, indexes: [...picked].sort((a, b) => a - b) };
}

function compressAriaIndices(ariaNums) {
  const sorted = [...new Set(ariaNums)].sort((a, b) => a - b);
  if (!sorted.length) return "";
  const ranges = [];
  let start = sorted[0], prev = sorted[0];
  for (let i = 1; i < sorted.length; i++) {
    if (sorted[i] === prev + 1) {
      prev = sorted[i];
    } else {
      ranges.push(start === prev ? `${start}` : `${start}-${prev}`);
      start = prev = sorted[i];
    }
  }
  ranges.push(start === prev ? `${start}` : `${start}-${prev}`);
  return ranges.join(",");
}

async function sendLongText(sock, jid, text, quotedMsg) {
  const MAX_CHUNK = 3600;
  const str = String(text || "");
  if (str.length <= MAX_CHUNK) {
    await sock.sendMessage(jid, { text: str }, quotedMsg ? { quoted: quotedMsg } : undefined);
    return;
  }
  const lines = str.split("\n");
  let buf = "";
  let first = true;
  for (const line of lines) {
    if (buf.length + line.length + 1 > MAX_CHUNK && buf.length > 0) {
      await sock.sendMessage(jid, { text: buf }, first && quotedMsg ? { quoted: quotedMsg } : undefined);
      first = false;
      buf = line;
    } else {
      buf = buf ? `${buf}\n${line}` : line;
    }
  }
  if (buf) {
    await sock.sendMessage(jid, { text: buf }, first && quotedMsg ? { quoted: quotedMsg } : undefined);
  }
}

const fgHttp = axios.create({
  timeout: 20000,
  headers: {
    "User-Agent": "Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/128.0.0.0 Safari/537.36",
    Accept: "text/html,application/xhtml+xml,application/json;q=0.9,*/*;q=0.8",
    "Accept-Language": "en-US,en;q=0.9",
    Referer: FITGIRL_BASE + "/"
  }
});

const FG_ALIASES = [
  [/\bgta\s*sa\b/gi, "grand theft auto san andreas"], [/\bgta\s*-?\s*(v|iv|iii|ii|vi|\d+)\b/gi, "grand theft auto $1"], [/\bgta\b/gi, "grand theft auto"], [/\bcod\b/gi, "call of duty"], [/\brdr\s*2\b/gi, "red dead redemption 2"],
  [/\bcp\s*2077\b/gi, "cyberpunk 2077"], [/\bw3\b|\btw3\b/gi, "witcher 3"], [/\bre\s*(\d)\b/gi, "resident evil $1"],
  [/\bac\b/gi, "assassin's creed"], [/\bnfs\b/gi, "need for speed"], [/\bfc\s*(\d+)\b/gi, "far cry $1"],
  [/\bmgs\b/gi, "metal gear solid"], [/\bgow\b/gi, "god of war"], [/\bhzd\b/gi, "horizon zero dawn"],
  [/\bds\s*(\d)\b/gi, "dark souls $1"], [/\bbf\s*(\d)\b/gi, "battlefield $1"], [/\bsw\b/gi, "star wars"]
];
function fgQueryVariants(query) {
  const q = String(query || "").replace(/\s+/g, " ").trim();
  const out = [q];
  let expanded = q;
  for (const [re, to] of FG_ALIASES) expanded = expanded.replace(re, to);
  if (expanded.toLowerCase() !== q.toLowerCase()) out.push(expanded);
  const roman = { " v": " 5", " iv": " 4", " iii": " 3", " ii": " 2", " vi": " 6", " vii": " 7" };
  for (const base of [...out]) for (const [r, n] of Object.entries(roman)) {
    if (base.toLowerCase().endsWith(r)) out.push(base.slice(0, -r.length) + n);
  }
  const words = expanded.split(" ");
  if (words.length > 2) out.push(words.slice(0, -1).join(" "));
  return [...new Set(out.filter(Boolean))];
}

function fgParseBlock(title, pageUrl, htmlBlock) {
  const $ = cheerio.load(htmlBlock || "");
  const text = $.root().text().replace(/\s+/g, " ").trim();
  const posterUrl = $("img").first().attr("src") || null;
  const repackSizeMatch = text.match(/Repack Size:\s*(.+?)(?:\s+Download Mirrors|\s+Magnet|\s+Screenshots|\s+Game Description|$)/i);
  const origSizeMatch = text.match(/Original Size:\s*(.+?)(?:\s+Repack Size|$)/i);
  const magnetHref = $('a[href^="magnet:?"]').first().attr("href") || null;
  const repackSize = repackSizeMatch ? repackSizeMatch[1].trim().slice(0, 40) : "";
  return {
    label: title, pageUrl, posterUrl,
    repackSize, originalSize: origSizeMatch ? origSizeMatch[1].trim().slice(0, 40) : "", size: repackSize,
    magnet: magnetHref, infoHash: extractInfoHash(magnetHref || ""),
    fileName: sanitizeFileName(`${title}.torrent`), source: "FitGirl Repacks"
  };
}

async function fgSearchOnce(q, diag = []) {
  try {
    const r = await fgHttp.get(`${FITGIRL_BASE}/wp-json/wp/v2/posts`, {
      params: { search: q, per_page: 15, _fields: "id,link,title,excerpt,content" },
      headers: { Accept: "application/json" }
    });
    const data = r.data;
    if (Array.isArray(data)) {
      diag.push(`"${q}" API: HTTP ${r.status}, ${data.length} post(s)`);
      const items = [];
      for (const p of data) {
        const title = cheerio.load(`<i>${p?.title?.rendered || ""}</i>`).root().text().replace(/\s+/g, " ").trim();
        if (!title || !p.link) continue;
        items.push(fgParseBlock(title, p.link, (p.content?.rendered || "") + " " + (p.excerpt?.rendered || "")));
      }
      if (items.length) return items;
    } else {
      diag.push(`"${q}" API: HTTP ${r.status}, not JSON (${typeof data === "string" ? data.slice(0, 40).replace(/\s+/g, " ") : typeof data})`);
    }
  } catch (err) {
    diag.push(`"${q}" API: ${err?.response?.status ? "HTTP " + err.response.status : err?.code || err?.message}`);
    console.warn("[fg] REST search failed:", err?.response?.status || err?.message);
  }

  let r2;
  try {
    r2 = await fgHttp.get(`${FITGIRL_BASE}/`, { params: { s: q } });
  } catch (err) {
    diag.push(`"${q}" page: ${err?.response?.status ? "HTTP " + err.response.status : err?.code || err?.message}`);
    throw err;
  }
  const html = String(r2.data || "");
  if (/just a moment|cf-challenge|cf_chl|attention required/i.test(html.slice(0, 4000))) diag.push(`"${q}" page: blocked by Cloudflare challenge`);
  const $ = cheerio.load(html);
  const items = [];
  const seen = new Set();
  $("article").each((_, el) => {
    const art = $(el);
    const titleEl = art.find(".entry-title a, h1 a, h2 a").first();
    const title = titleEl.text().replace(/\s+/g, " ").trim();
    const pageUrl = (titleEl.attr("href") || "").trim();
    if (!title || !pageUrl || seen.has(pageUrl)) return;
    seen.add(pageUrl);
    items.push(fgParseBlock(title, pageUrl, art.html()));
  });
  diag.push(`"${q}" page: HTTP ${r2.status}, ${html.length} bytes, ${items.length} article(s)`);
  return items;
}

async function searchFitGirlGames(query) {
  const diag = [];
  let lastErr = null;
  for (const q of fgQueryVariants(query)) {
    try {
      const items = await fgSearchOnce(q, diag);
      if (items.length) {
        console.log(`[fg] "${q}" -> ${items.length} result(s)`);
        return items.slice(0, 15);
      }
    } catch (err) {
      lastErr = err;
      console.error(`[fg] search "${q}" failed:`, err?.response?.status || err?.message);
    }
  }
  console.warn("[fg] no results:", diag.join(" | "));
  const e = new Error(lastErr?.response?.status ? `FitGirl site returned HTTP ${lastErr.response.status}` : (lastErr?.message || "No results"));
  e.noResults = !lastErr;
  e.diag = diag;
  throw e;
}

async function resolveFitGirlGameDetail(item) {
  let magnet = item.magnet || null, torrentUrl = null;
  let repackSize = item.repackSize || "", originalSize = item.originalSize || "", posterUrl = item.posterUrl || null;

  if (item.pageUrl) {
    try {
      const { data: html } = await fgHttp.get(item.pageUrl, { timeout: 12000 });
      const $ = cheerio.load(html);
      const bodyText = $(".entry-content").text().replace(/\s+/g, " ").trim();
      if (!magnet) magnet = $('a[href^="magnet:?"]').first().attr("href") || null;
      torrentUrl = $('a[href$=".torrent"]').first().attr("href") || null;
      if (!repackSize) {
        const m = bodyText.match(/Repack Size:\s*(.+?)(?:\s+Download Mirrors|\s+Magnet|\s+Screenshots|$)/i);
        if (m) repackSize = m[1].trim().slice(0, 40);
      }
      if (!originalSize) {
        const m = bodyText.match(/Original Size:\s*(.+?)(?:\s+Repack Size|$)/i);
        if (m) originalSize = m[1].trim().slice(0, 40);
      }
      if (!posterUrl) posterUrl = $(".entry-content img").first().attr("src") || null;
    } catch {}
  }

  return { ...item, magnet, torrentUrl, repackSize, originalSize, size: repackSize, posterUrl, infoHash: extractInfoHash(magnet || item.infoHash || "") };
}

function formatFitGirlDetailsText(game) {
  return [
    `🎮 *${game.label}*`,
    `📦 *Source:* FitGirl Repacks`,
    game.originalSize ? `💾 *Original Size:* ${game.originalSize}` : null,
    game.repackSize ? `🗜️ *Repack Size:* ${game.repackSize}` : null,
    `📏 *Auto RAR Rule:* <10 GB → 1 GB | <20 GB → 1.5 GB | ≥20 GB → 1.9 GB`
  ].filter(Boolean).join("\n");
}

async function promptFitGirlAction(sock, jid, quotedMsg, selectedItem) {
  const resolved = await resolveFitGirlGameDetail(selectedItem);
  console.log(`[fg] selected "${resolved.label}" magnet=${resolved.magnet ? "yes" : "no"} torrent=${resolved.torrentUrl ? "yes" : "no"}`);
  pendingFgActionByChat.set(jid, { game: resolved, createdAt: Date.now(), senderKey: fgSenderKey(quotedMsg) });
  const noLink = !resolved.magnet && !resolved.torrentUrl && !resolved.infoHash;
  const choiceText =
    `${formatFitGirlDetailsText(resolved)}\n` +
    (noLink ? `⚠️ _No magnet/torrent link was found on the page, so 1 and 2 may fail._\n` : "") +
    `\n🪟 *Select Action*\n*1.* 📥 *Get Torrent File*\n*2.* ⚡ *Leech to WP*\n\n✍️ Reply with *1* or *2*.`;

  if (resolved.posterUrl) {
    try {
      const img = await fgHttp.get(resolved.posterUrl, { responseType: "arraybuffer", timeout: 10000, maxContentLength: 8 * 1024 * 1024 });
      if (/^image\//i.test(String(img.headers?.["content-type"] || "")) && img.data?.byteLength > 500) {
        await Promise.race([
          sock.sendMessage(jid, { image: Buffer.from(img.data), caption: choiceText }, quotedMsg ? { quoted: quotedMsg } : undefined),
          new Promise((_, rej) => setTimeout(() => rej(new Error("poster send timeout")), 30000))
        ]);
        return;
      }
    } catch (err) {
      console.warn("[fg] poster failed, sending text only:", err?.message);
    }
  }
  await sock.sendMessage(jid, { text: choiceText }, quotedMsg ? { quoted: quotedMsg } : undefined);
}

async function runFitGirlLeechAndRarUpload(sock, jid, msg, game, rarBaseName, torrentSource, extra = {}) {
  const sender = senderFromMsg(sock, msg);
  const { task, start } = startFitGirlJob(sock, {
    jid,
    sender,
    senderName: msg.pushName || "",
    label: game.label,
    input: torrentSource,
    customPrefix: rarBaseName,
    selectFile: extra.selectFile || "",
    selectedCount: extra.selectedCount || 0,
    selectedPaths: extra.selectedPaths || null,
    torrentBuffer: extra.torrentBuffer || null
  });
  await sock.sendMessage(jid, {
    text: `🎮 [MPM] FitGirl task #${task.id} added to queue.\n📦 RAR name: *${rarBaseName}*${extra.selectedCount ? `\n📁 Selected Files: *${extra.selectedCount}*` : ""}\n(cancel it with ,cancel ${task.id})`
  }, { quoted: msg });
  start();
}

async function promptTorrentActionWindow(sock, jid, quotedMsg, selectedItem) {
  const resolved = await resolveWatchSoMuchRelease(selectedItem);
  clearFgPending(jid);
  pendingActionByChat.set(jid, {
    release: resolved,
    createdAt: Date.now()
  });

  const sizeLine = resolved.size ? `💾 Size: *${resolved.size}*\n` : "";
  const promptText =
    `🪟 *Torrent Action Window*\n` +
    `🎬 *${resolved.label}*\n` +
    `📦 Source: *${resolved.source}*\n` +
    sizeLine +
    `\nWhat would you like to do with this torrent?\n` +
    `*1.* 📥 *Download Torrent File* (.torrent)\n` +
    `*2.* ⚡ *Leech Torrent & Upload Files* (Leech & Upload)\n\n` +
    `✍️ Reply with *1* or *2*.`;

  await sock.sendMessage(jid, { text: promptText }, quotedMsg ? { quoted: quotedMsg } : undefined);
}

async function executeTorrentActionChoice(sock, jid, quotedMsg, resolved, choice) {
  if (choice === "1") {
    const sentFile = await sendTorrentFileOnly(sock, jid, resolved);
    if (sentFile) return;

    const magnet = buildMagnetUri(resolved);
    if (magnet) {
      await sock.sendMessage(jid, {
        text:
          `🧲 *${resolved.label}*\n` +
          `_(No cached .torrent available; sending Magnet Link instead)_\n\n` +
          `\`${magnet}\``
      });
      return;
    }

    throw new Error("Could not download the torrent file.");
  }

  if (choice === "2") {
    await leechTorrentAndUpload(sock, jid, quotedMsg, resolved);
  }
}

// ============================================================================
// Live Source Monitor (,sources)
// ============================================================================
function classifySourceCheckError(err, statusCode = null, bodyText = "") {
  const rawMsg = String(err?.message || "");
  const lowerBody = String(bodyText || "").toLowerCase();
  const code = statusCode || err?.response?.status || null;

  const isCloudflareOrBotBlock =
    code === 403 ||
    code === 503 ||
    code === 429 ||
    lowerBody.includes("cf-browser-verification") ||
    lowerBody.includes("just a moment...") ||
    lowerBody.includes("attention required! | cloudflare") ||
    lowerBody.includes("ddos-guard") ||
    lowerBody.includes("verify you are human") ||
    /status code (403|429|503)/i.test(rawMsg);

  if (isCloudflareOrBotBlock) {
    return {
      status: "BLOCKED",
      icon: "🛡️",
      label: "Blocked",
      error: code ? `HTTP ${code} (Cloudflare / Bot Protection)` : "Cloudflare / Bot Protection"
    };
  }

  if (err?.code === "ECONNABORTED" || /timeout/i.test(rawMsg)) {
    return { status: "FAILED", icon: "🔴", label: "Failed", error: "Request timed out" };
  }

  return {
    status: "FAILED",
    icon: "🔴",
    label: "Failed",
    error: code ? `HTTP ${code}` : (rawMsg.slice(0, 65) || "Connection error")
  };
}

const SOURCE_STATUS_RANK = { WORKING: 3, LIMITED: 2, BLOCKED: 1, FAILED: 0 };

async function runSingleSourceLiveCheck(spec) {
  if (!Array.isArray(spec.mirrors) || spec.mirrors.length === 0) {
    return runSingleSourceLiveCheckOnce(spec);
  }
  const results = await Promise.all(
    spec.mirrors.map((mirrorUrl) => runSingleSourceLiveCheckOnce({ ...spec, url: mirrorUrl }))
  );
  let bestIdx = 0;
  for (let i = 1; i < results.length; i++) {
    if ((SOURCE_STATUS_RANK[results[i].status] ?? 0) > (SOURCE_STATUS_RANK[results[bestIdx].status] ?? 0)) bestIdx = i;
  }
  const best = results[bestIdx];
  if (best.status === "WORKING") {
    let host = "";
    try { host = new URL(spec.mirrors[bestIdx]).hostname; } catch {}
    return host ? { ...best, searchResult: `${best.searchResult} via ${host}` } : best;
  }
  return best;
}

async function runSingleSourceLiveCheckOnce(spec) {
  const startedAt = Date.now();
  if (spec.requiresKey) return {
    category: spec.category, name: spec.name, ms: 0, status: "LIMITED", icon: "🟡",
    label: "Key Required", searchResult: "Not tested", error: "Add API key in .env to enable"
  };
  try {
    const res = await http.get(spec.url, {
      params: spec.params || undefined,
      headers: spec.headers || undefined,
      timeout: 11000,
      validateStatus: (s) => s >= 200 && s < 500
    });
    const elapsedMs = Date.now() - startedAt;
    const rawText = typeof res.data === "string" ? res.data : JSON.stringify(res.data || "");

    if (res.status === 403 || res.status === 429 || res.status >= 500) {
      const classified = classifySourceCheckError(null, res.status, rawText);
      return { category: spec.category, name: spec.name, ms: elapsedMs, searchResult: "0 results", ...classified };
    }

    const lowerBody = rawText.toLowerCase();
    if (
      lowerBody.includes("cf-browser-verification") ||
      lowerBody.includes("just a moment...") ||
      lowerBody.includes("attention required! | cloudflare") ||
      lowerBody.includes("verify you are human")
    ) {
      return {
        category: spec.category, name: spec.name, ms: elapsedMs,
        status: "BLOCKED", icon: "🛡️", label: "Blocked",
        searchResult: "Challenge page", error: "Cloudflare / Bot Protection"
      };
    }

    const matchCount = spec.evaluate(res.data, rawText);
    if (matchCount > 0) {
      return {
        category: spec.category, name: spec.name, ms: elapsedMs,
        status: "WORKING", icon: "🟢", label: "Working",
        searchResult: `${matchCount} results found`, error: null
      };
    }

    return {
      category: spec.category, name: spec.name, ms: elapsedMs,
      status: "LIMITED", icon: "🟡", label: "Limited",
      searchResult: "0 search results", error: "Online, but no search results returned"
    };
  } catch (err) {
    const elapsedMs = Date.now() - startedAt;
    const errBody = typeof err?.response?.data === "string" ? err.response.data : "";
    const classified = classifySourceCheckError(err, err?.response?.status || null, errBody);
    return { category: spec.category, name: spec.name, ms: elapsedMs, searchResult: "No response", ...classified };
  }
}

async function checkAllBotSourcesLive() {
  const testQuery = "Inception";
  const tvTestQuery = "Breaking Bad";
  const testImdbId = "0903747";

  const countHtmlTorrents = (rawText) => {
    const magnets = (rawText.match(/magnet:\?xt=urn:btih:[a-fA-F0-9]{40}/gi) || []).length;
    if (magnets > 0) return magnets;

    const $ = cheerio.load(rawText);
    const candidates = new Set();
    const resultContainers = $(".torrent, .result, .result-item, .torrent-row, .browse-movie-wrap, article, tbody tr, .card");
    resultContainers.each((_, el) => {
      const title = $(el).find("a[href]").first().text().replace(/\s+/g, " ").trim() ||
        $(el).text().replace(/\s+/g, " ").trim().slice(0, 180);
      if (title.length > 8) candidates.add(title.toLowerCase());
    });

    $("a[href]").each((_, el) => {
      const href = ($(el).attr("href") || "").trim();
      const text = $(el).text().replace(/\s+/g, " ").trim();
      if (text.length > 3 && (
        extractInfoHash(href) ||
        /\/(?:torrent|details|download)\/[^?#]+/i.test(href) ||
        /\/[a-z0-9-]+-torrent-\d+\.html/i.test(href) ||
        /\.torrent(?:$|[?#])/i.test(href)
      )) candidates.add(text.toLowerCase());
    });
    return candidates.size;
  };

  const checks = [
    { category: "Torrent Search Sources", name: "SolidTorrents", url: `https://solidtorrents.to/api/v1/search?q=${encodeURIComponent(testQuery)}&category=all&sort=seeders`, evaluate: (data, raw) => Array.isArray(data?.results) ? data.results.length : countHtmlTorrents(raw) },
    { category: "Torrent Search Sources", name: "BitSearch", url: `https://bitsearch.to/search?q=${encodeURIComponent(testQuery)}`, evaluate: (_, raw) => countHtmlTorrents(raw) },
    { category: "Torrent Search Sources", name: "Knaben", url: `https://knaben.org/search/${encodeURIComponent(testQuery)}/0/1/seeders`, evaluate: (_, raw) => countHtmlTorrents(raw) },
    { category: "Torrent Search Sources", name: "EXT.to", url: `https://ext.to/search/?q=${encodeURIComponent(testQuery)}`, evaluate: (_, raw) => countHtmlTorrents(raw) },
    { category: "Torrent Search Sources", name: "1337x", url: `https://1337x.to/search/${encodeURIComponent(testQuery)}/1/`, evaluate: (_, raw) => countHtmlTorrents(raw) },
    { category: "Torrent Search Sources", name: "LimeTorrents", url: `https://limetorrents.info/search/all/${encodeURIComponent(testQuery)}/`, evaluate: (_, raw) => countHtmlTorrents(raw) },
    { category: "Torrent Search Sources", name: "TorrentDownloads", url: `https://torrentdownloads.me/search/?search=${encodeURIComponent(testQuery)}`, evaluate: (_, raw) => countHtmlTorrents(raw) },
    { category: "Torrent Search Sources", name: "TorLock", url: `https://torlock.com/all/torrents/${encodeURIComponent(testQuery)}.html`, evaluate: (_, raw) => countHtmlTorrents(raw) },
    { category: "Movie / TV Sources", name: "WatchSoMuch", url: `${WATCHSOMUCH_BASE}/Movies/${encodeURIComponent(testQuery)}/`, evaluate: (_, raw) => { const $ = cheerio.load(raw); return $('a[href*="/Movie/"], a[href*="magnet:?"], a[href*=".torrent"]').length; } },
    { category: "Movie / TV Sources", name: "APIBay", url: APIBAY_MIRRORS[0], mirrors: APIBAY_MIRRORS, params: { q: testQuery, cat: "0" }, evaluate: (data) => Array.isArray(data) ? data.filter((r) => r?.info_hash && !/^0+$/.test(r.info_hash)).length : 0 },
    { category: "Movie / TV Sources", name: "TPB.party", url: "https://tpb.party/q.php", params: { q: testQuery, cat: "0" }, evaluate: (data) => Array.isArray(data) ? data.filter((r) => r?.info_hash && !/^0+$/.test(r.info_hash)).length : 0 },
    { category: "Movie / TV Sources", name: "EZTV", url: EZTV_API_MIRRORS[0], mirrors: EZTV_API_MIRRORS, params: { imdb_id: testImdbId, limit: 10, page: 1 }, evaluate: (data) => (Array.isArray(data?.torrents) ? data.torrents.length : 0) },
    { category: "Movie / TV Sources", name: "YTS", url: YTS_API_MIRRORS[0], mirrors: YTS_API_MIRRORS, params: { query_term: testQuery, limit: 3 }, evaluate: (data) => (Array.isArray(data?.data?.movies) ? data.data.movies.length : 0) },
    { category: "Metadata Source", name: "TVMaze", url: "https://api.tvmaze.com/singlesearch/shows", params: { q: tvTestQuery }, evaluate: (data) => (data && data.id ? 1 : 0) },
    ...["en.yts.lu", "yts.lu", "yts.lt", "yts.ag", "yts.am"].map((domain) => ({
      category: "YTS Mirrors", name: domain, url: `https://${domain}/api/v2/list_movies.json`, params: { query_term: testQuery, limit: 3 },
      evaluate: (data) => (Array.isArray(data?.data?.movies) ? data.data.movies.length : 0)
    })),
    { category: "Metadata & Legal Catalogue", name: "Wikidata Search API", url: "https://www.wikidata.org/w/api.php", params: { action: "wbsearchentities", search: testQuery, language: "en", format: "json", type: "item" }, evaluate: (data) => Array.isArray(data?.search) ? data.search.length : 0 },
    { category: "Metadata & Legal Catalogue", name: "Internet Archive Movie Search", url: "https://archive.org/advancedsearch.php", params: { q: "mediatype:movies AND title:Inception", fl: ["identifier", "title"], rows: 3, output: "json" }, evaluate: (data) => Array.isArray(data?.response?.docs) ? data.response.docs.length : 0 },
    { category: "Metadata & Legal Catalogue", name: "Wikimedia Commons Video Search", url: "https://commons.wikimedia.org/w/api.php", params: { action: "query", generator: "search", gsrsearch: "Big Buck Bunny filetype:video", gsrnamespace: 6, gsrlimit: 3, prop: "imageinfo", iiprop: "url", format: "json", formatversion: 2 }, headers: { "User-Agent": "MPM-WhatsApp-Bot/1.0 (source monitor)" }, evaluate: (data) => Array.isArray(data?.query?.pages) ? data.query.pages.length : 0 },
    { category: "Metadata & Legal Catalogue", name: "TMDB Movie Search", url: "https://api.themoviedb.org/3/search/movie", params: { query: testQuery, ...(process.env.TMDB_API_KEY ? { api_key: process.env.TMDB_API_KEY } : {}) }, headers: process.env.TMDB_READ_ACCESS_TOKEN ? { Authorization: `Bearer ${process.env.TMDB_READ_ACCESS_TOKEN}` } : undefined, evaluate: (data) => Array.isArray(data?.results) ? data.results.length : 0, requiresKey: !(process.env.TMDB_API_KEY || process.env.TMDB_READ_ACCESS_TOKEN) },
    { category: "Metadata & Legal Catalogue", name: "TMDB TV Search", url: "https://api.themoviedb.org/3/search/tv", params: { query: tvTestQuery, ...(process.env.TMDB_API_KEY ? { api_key: process.env.TMDB_API_KEY } : {}) }, headers: process.env.TMDB_READ_ACCESS_TOKEN ? { Authorization: `Bearer ${process.env.TMDB_READ_ACCESS_TOKEN}` } : undefined, evaluate: (data) => Array.isArray(data?.results) ? data.results.length : 0, requiresKey: !(process.env.TMDB_API_KEY || process.env.TMDB_READ_ACCESS_TOKEN) },
    { category: "Metadata & Legal Catalogue", name: "OMDb Movie API", url: "https://www.omdbapi.com/", params: process.env.OMDB_API_KEY ? { apikey: process.env.OMDB_API_KEY, t: testQuery } : undefined, evaluate: (data) => data?.Response === "True" ? 1 : 0, requiresKey: !process.env.OMDB_API_KEY },
    { category: "Metadata & Legal Catalogue", name: "Trakt Search API", url: "https://api.trakt.tv/search/movie", params: { query: testQuery }, headers: process.env.TRAKT_CLIENT_ID ? { "trakt-api-version": "2", "trakt-api-key": process.env.TRAKT_CLIENT_ID } : undefined, evaluate: (data) => Array.isArray(data) ? data.length : 0, requiresKey: !process.env.TRAKT_CLIENT_ID },
    { category: "Metadata & Legal Catalogue", name: "Watchmode Search API", url: "https://api.watchmode.com/v1/search/", params: process.env.WATCHMODE_API_KEY ? { apiKey: process.env.WATCHMODE_API_KEY, search_field: "name", search_value: testQuery } : undefined, evaluate: (data) => Array.isArray(data?.title_results) ? data.title_results.length : 0, requiresKey: !process.env.WATCHMODE_API_KEY },
    { category: "Metadata & Legal Catalogue", name: "Internet Archive Metadata API", url: "https://archive.org/metadata/night_of_the_living_dead", evaluate: (data) => data?.metadata?.identifier ? 1 : 0 },
    { category: "Metadata & Legal Catalogue", name: "TVMaze Show Search API", url: "https://api.tvmaze.com/search/shows", params: { q: tvTestQuery }, evaluate: (data) => Array.isArray(data) ? data.length : 0 },
    { category: "Metadata & Legal Catalogue", name: "TVMaze Web Schedule API", url: "https://api.tvmaze.com/schedule/web", params: { date: new Date().toISOString().slice(0, 10) }, evaluate: (data) => Array.isArray(data) ? data.length : 0 }
  ];

  const settled = await Promise.allSettled(checks.map((spec) => runSingleSourceLiveCheck(spec)));
  return settled.map((entry, idx) =>
    entry.status === "fulfilled"
      ? entry.value
      : { category: checks[idx].category, name: checks[idx].name, ms: 0, status: "FAILED", icon: "🔴", label: "Failed", searchResult: "No response", error: entry.reason?.message || "Unexpected check error" }
  );
}

function isWebTorrentTorrentIdBug(err) {
  const msg = String(err?.message || err || "");
  const stack = String(err?.stack || "");
  return (
    msg.includes("arr2hex") ||
    msg.includes("_onTorrentId") ||
    msg.includes("uint8-util") ||
    stack.includes("_onTorrentId") ||
    stack.includes("uint8-util")
  );
}

const APP_DIR = path.dirname(require("url").fileURLToPath(import.meta.url));
function logCrash(kind, err) {
  try {
    const f = path.join(APP_DIR, "data", "crash.log");
    try { if (fs.statSync(f).size > 1024 * 1024) fs.renameSync(f, f + ".old"); } catch {}
    fs.appendFileSync(f, "[" + new Date().toISOString() + "] " + kind + ": " + (err && err.stack ? err.stack : String(err)) + "\n");
  } catch {}
}
async function crashLoopGuard() {
  try {
    const f = path.join(APP_DIR, "data", "boots.json");
    let boots = [];
    try { boots = JSON.parse(fs.readFileSync(f, "utf8")); } catch {}
    const now = Date.now();
    boots = (Array.isArray(boots) ? boots : []).filter((t) => now - t < 2 * 60 * 1000);
    boots.push(now);
    fs.writeFileSync(f, JSON.stringify(boots));
    if (boots.length >= 5) {
      console.error("⚠️ The bot started " + boots.length + " times in 2 minutes. Waiting 60s before connecting so WhatsApp does not flag the account.");
      await new Promise((r) => setTimeout(r, 60000));
    }
  } catch (e) { console.error("[crashLoopGuard]", e?.message || e); }
}

const recentCrashes = [];
process.on("uncaughtException", (err) => {
  if (isWebTorrentTorrentIdBug(err)) {
    console.error("[Suppressed WebTorrent TorrentId Error]:", err?.message || err);
    return;
  }
  console.error("[Uncaught Exception]:", err);
  logCrash("uncaughtException", err);
  const now = Date.now();
  recentCrashes.push(now);
  while (recentCrashes.length && now - recentCrashes[0] > 2 * 60 * 1000) recentCrashes.shift();
  if (recentCrashes.length >= 5) watchdogExit("5 uncaught errors within 2 minutes.");
});

process.on("unhandledRejection", (reason) => {
  if (isWebTorrentTorrentIdBug(reason)) {
    console.error("[Suppressed WebTorrent Rejection]:", reason?.message || reason);
    return;
  }
  console.error("[Unhandled Rejection]:", reason);
  logCrash("unhandledRejection", reason);
});

const CREDS_FILE = path.join(AUTH_DIR, "creds.json");
const CREDS_BAK = path.join(AUTH_DIR, "creds.json.bak");

function restoreCredsIfBroken() {
  try {
    if (!fs.existsSync(AUTH_DIR)) return;
    let ok = false;
    try {
      const raw = fs.readFileSync(CREDS_FILE, "utf8");
      if (raw && raw.trim()) { JSON.parse(raw); ok = true; }
    } catch {}
    if (!ok && fs.existsSync(CREDS_BAK)) {
      JSON.parse(fs.readFileSync(CREDS_BAK, "utf8"));
      fs.copyFileSync(CREDS_BAK, CREDS_FILE);
      console.log("♻️ creds.json was corrupted - restored from backup (no re-link needed).");
    }
  } catch (e) {
    console.error("[restoreCredsIfBroken]", e?.message || e);
  }
}

function backupCreds() {
  try {
    const raw = fs.readFileSync(CREDS_FILE, "utf8");
    JSON.parse(raw);
    fs.writeFileSync(CREDS_BAK, raw);
  } catch {}
}

let liveSock = null;
let connOpen = false;
let reconnectTimer = null;
let reconnectAttempts = 0;
let badSessionCount = 0;
let startingBot = false;
let lastOpenAt = 0;

function watchdogExit(reason) {
  console.error("🛑 [Watchdog] " + reason + " - exiting so start.bat restarts the bot.");
  setTimeout(() => process.exit(1), 500);
}
const WATCHDOG_DISCONNECT_MS = 5 * 60 * 1000;
const WATCHDOG_RSS_MB = Number(process.env.WATCHDOG_RSS_MB || 2600);
setInterval(() => {
  try {
    if (!connOpen && lastOpenAt && Date.now() - lastOpenAt > WATCHDOG_DISCONNECT_MS) {
      return watchdogExit("WhatsApp has been disconnected for over 5 minutes.");
    }
    const rssMb = process.memoryUsage().rss / (1024 * 1024);
    if (rssMb > WATCHDOG_RSS_MB && activeTasksByChat.size === 0) {
      return watchdogExit("Memory use is " + rssMb.toFixed(0) + " MB while idle.");
    }
  } catch {}
}, 60 * 1000).unref();

function scheduleReconnect(delayMs) {
  if (reconnectTimer) return;
  reconnectTimer = setTimeout(() => {
    reconnectTimer = null;
    startBot();
  }, delayMs);
}

function waitForOpen(ms) {
  return new Promise((resolve) => {
    const t0 = Date.now();
    const iv = setInterval(() => {
      if (connOpen || Date.now() - t0 > ms) {
        clearInterval(iv);
        resolve(connOpen);
      }
    }, 500);
  });
}

const HUMAN_DELAY_ON = String(process.env.HUMAN_DELAY || "1") !== "0";
const sleepMs = (ms) => new Promise((r) => setTimeout(r, ms));
const randBetween = (a, b) => a + Math.floor(Math.random() * (b - a + 1));
let lastTextSlotAt = 0;
async function humanPause(sockRef, jid, content) {
  if (!HUMAN_DELAY_ON || !content || typeof content.text !== "string" || content.edit || content.delete) return;
  try {
    const now = Date.now();
    const slot = Math.max(now, lastTextSlotAt + 700);
    lastTextSlotAt = slot;
    if (slot > now) await sleepMs(slot - now);
    const live = sockRef === liveSock && connOpen;
    if (live) await sockRef.sendPresenceUpdate("composing", jid).catch(() => {});
    await sleepMs(Math.min(2500, randBetween(500, 1200) + content.text.length * 12));
    if (live) await sockRef.sendPresenceUpdate("paused", jid).catch(() => {});
  } catch {}
}

const AUTO_REACT_ON = String(process.env.AUTO_REACT || "1") !== "0";
const DEFAULT_REACTIONS = {
  movie: "🎬", tv: "📺", series: "📺", psa: "🎞️", tvinfo: "ℹ️", freefilm: "🆓", legalrelease: "🆓",
  dl: "⬇️", dl1: "⬇️", dlr: "⬇️", torrent: "🧲", magnet: "🧲", fg: "🎮", gofile: "📁", zip: "🗜️", unzip: "📂", rar: "🗜️", rename: "✏️",
  up: "⬆️", uplist: "📋", updel: "🗑️",
  cancel: "❌", cancelall: "❌", task: "📌", tasks: "📌", status: "📊", speed: "⚡",
  limit: "📏", setlimit: "📏", addlimit: "📏", removelimit: "📏", resetlimit: "📏", limitcheck: "📏", mylimit: "📏", checklimit: "📏",
  users: "👥", stats: "📈", check: "🔍", admin: "👑", addadmin: "👑", removeadmin: "👑", admins: "👑",
  block: "🚫", unblock: "✅", setgroup: "👥", groups: "👥", selectgroup: "👥", removegroup: "👥", template: "🧩",
  restart: "🔄", reboot: "🔄",
  alive: "💚", com: "📜", commands: "📜", help: "📜", menu: "📜", sources: "🌐",
  default: "👍"
};
let reactionOverrides = null;
function getReactionMap() {
  if (reactionOverrides === null) {
    reactionOverrides = {};
    try {
      const cfg = JSON.parse(fs.readFileSync(path.resolve("config.json"), "utf8").replace(/^\uFEFF/, ""));
      if (cfg && typeof cfg.reactions === "object") reactionOverrides = cfg.reactions;
    } catch {}
  }
  return { ...DEFAULT_REACTIONS, ...reactionOverrides };
}
async function reactToCommand(sockRef, msg, text) {
  if (!AUTO_REACT_ON) return;
  try {
    const m = /^[.,]([a-z0-9]+)/i.exec(text) || (/^up$/i.test(text) ? [null, "up"] : null);
    if (!m) return;
    const map = getReactionMap();
    const name = m[1].toLowerCase();
    // the secret admin code must not get any reaction
    if (name === String(process.env.ADMIN_CODE || "ezio12345").trim().toLowerCase()) return;
    let emoji = map[name];
    if (emoji === undefined) {
      // commands the bot matches by prefix (e.g. .movie2024, .tvshow)
      const prefixCmds = ["movie", "psa", "tvinfo", "freefilm", "legalrelease", "series", "tv"];
      const hit = prefixCmds.find((p) => name.startsWith(p));
      // anything else is not a command the bot knows -> wrong command
      emoji = hit ? map[hit] : (map.unknown ?? "❌");
    }
    if (!emoji) return;
    await sockRef.sendMessage(msg.key.remoteJid, { react: { text: emoji, key: msg.key } });
  } catch {}
}

const RETRYABLE_SEND_ERROR = /connection (closed|failure|lost)|timed out|stream errored|socket|not open/i;

const stableSock = new Proxy({}, {
  get(_t, prop) {
    const target = liveSock;
    if (!target) {
      if (typeof prop === "symbol" || prop === "then") return undefined;
      throw new Error("WhatsApp is not connected yet");
    }
    if (prop === "sendMessage") {
      return async (...args) => {
        let lastErr;
        for (let attempt = 1; attempt <= 3; attempt++) {
          try {
            if (!connOpen) await waitForOpen(120000);
            return await liveSock.sendMessage(...args);
          } catch (e) {
            lastErr = e;
            const msg = String(e?.message || e);
            if (attempt < 3 && RETRYABLE_SEND_ERROR.test(msg)) {
              console.log(`[send retry ${attempt}/3] ${msg}`);
              await waitForOpen(120000);
              continue;
            }
            throw e;
          }
        }
        throw lastErr;
      };
    }
    const v = target[prop];
    return typeof v === "function" ? v.bind(target) : v;
  }
});

async function sendAndMarkUpload(jid, content) {
  try {
    return await stableSock.sendMessage(jid, content);
  } finally {
    markUploadDone();
  }
}

async function startBot() {
  if (startingBot) return;
  startingBot = true;
  try {
    await startBotInner();
  } catch (err) {
    console.error("[startBot failed - retrying in 5s]:", err?.message || err);
    scheduleReconnect(5000);
  } finally {
    startingBot = false;
  }
}

async function startBotInner() {
  restoreCredsIfBroken();
  const { state, saveCreds } = await useMultiFileAuthState(AUTH_DIR);

  let version;
  try {
    ({ version } = await fetchLatestBaileysVersion());
  } catch {
    console.log("[fetchLatestBaileysVersion failed - using Baileys default]");
  }

  if (liveSock) {
    try { liveSock.ev.removeAllListeners(); } catch {}
    try { liveSock.end(undefined); } catch {}
  }

  const sock = makeWASocket({
    ...(version ? { version } : {}),
    auth: state,
    logger: pino({ level: "silent" }),
    keepAliveIntervalMs: 25000,
    connectTimeoutMs: 60000,
    defaultQueryTimeout: 120000,
    markOnlineOnConnect: false,
    syncFullHistory: false
  });
  liveSock = sock;
  connOpen = false;

  const rawSendMessage = sock.sendMessage.bind(sock);
  sock.sendMessage = async (jid, content, options) => {
    await humanPause(sock, jid, content);
    return rawSendMessage(jid, content, options);
  };

  sock.ev.on("creds.update", async () => {
    try {
      await saveCreds();
      if (connOpen) backupCreds();
    } catch (e) {
      console.error("[saveCreds]", e?.message || e);
    }
  });

  sock.ev.on("connection.update", ({ connection, lastDisconnect, qr }) => {
    if (sock !== liveSock) return;

    if (qr) {
      console.log("\nScan this QR Code from WhatsApp Linked Devices:\n");
      qrcode.generate(qr, { small: true }, (art) => console.log("\x1b[97m" + art + "\x1b[0m"));
    }

    if (connection === "open") {
      connOpen = true;
      lastOpenAt = Date.now();
      reconnectAttempts = 0;
      badSessionCount = 0;
      backupCreds();
      setLinkedOwner(sock.user?.id || "");
      startQuotaReminders(sock);
      restoreQueue(stableSock);
      console.log("✅ MPM Downloder WhatsApp Bot connected successfully!");
      try {
        const rf = path.join(path.dirname(require("url").fileURLToPath(import.meta.url)), "data", "restart.json");
        if (fs.existsSync(rf)) {
          const info = JSON.parse(fs.readFileSync(rf, "utf8"));
          fs.unlinkSync(rf);
          if (info && info.jid && Date.now() - Number(info.at || 0) < 10 * 60 * 1000) {
            setTimeout(() => { stableSock.sendMessage(info.jid, { text: "✅ [MPM] Bot restarted and online." }).catch(() => {}); }, 2000);
          }
        }
      } catch (e) { console.error("restart notice failed:", e.message); }
    }

    if (connection === "close") {
      if (connOpen) lastOpenAt = Date.now();
      connOpen = false;
      const statusCode = lastDisconnect?.error?.output?.statusCode;
      const reasonText = lastDisconnect?.error?.message || "";
      console.log(`❌ Connection closed (code ${statusCode ?? "?"}${reasonText ? ": " + reasonText : ""})`);

      if (statusCode === DisconnectReason.loggedOut) {
        console.log("🔑 Logged out by WhatsApp. Clearing auth_info - scan the new QR code to link again.");
        try { fs.rmSync(AUTH_DIR, { recursive: true, force: true }); } catch {}
        scheduleReconnect(2000);
        return;
      }

      if (statusCode === DisconnectReason.connectionReplaced) {
        console.log("⚠️ This session was opened somewhere else (another bot window / PC?). Retrying in 30s. Make sure only ONE bot is running.");
        scheduleReconnect(30000);
        return;
      }

      if (statusCode === DisconnectReason.badSession) {
        badSessionCount++;
        if (badSessionCount >= 5) {
          console.log("🧹 Session kept failing (bad session). Clearing auth_info - scan the QR code again.");
          try { fs.rmSync(AUTH_DIR, { recursive: true, force: true }); } catch {}
          badSessionCount = 0;
        }
      }

      reconnectAttempts++;
      const delay = Math.min(3000 * reconnectAttempts, 30000) + Math.floor(Math.random() * 2000);
      console.log(`🔄 Reconnecting in ${Math.round(delay / 1000)}s (attempt ${reconnectAttempts})...`);
      scheduleReconnect(delay);
    }
  });

  const handleIncoming = async (msg) => {
    if (!msg?.message) return;
    const isFromMe = Boolean(msg.key.fromMe);
    if (isFromMe && !/^(?:[,.][a-z0-9]+(?:\s|$)|up$)/i.test((msg.message.conversation || msg.message.extendedTextMessage?.text || "").trim())) {
      return;
    }

    const jid = msg.key.remoteJid;
    let body = (
      msg.message.conversation ||
      msg.message.extendedTextMessage?.text ||
      ""
    ).trim();

    if (!body) return;
    if (/^[.,][a-z]/i.test(body) || /^up$/i.test(body)) {
      reactToCommand(sock, msg, body);
    }
    if (/^[.,][a-z]/i.test(body)) {
      if (await throttleCommand(stableSock, msg)) return;
      if (!msg.key.fromMe) { try { await sock.readMessages([msg.key]); } catch {} }
    }

    if (/^,(cancel|stop)$/i.test(body)) {
      const senderNum = senderFromMsg(stableSock, msg);
      const hadFg = Boolean(
        getFgPending(pendingFgSearchByChat, jid, msg) ||
        getFgPending(pendingFgActionByChat, jid, msg) ||
        getFgPending(pendingFgFileSelectByChat, jid, msg) ||
        getFgPending(pendingFgRarNameByChat, jid, msg)
      );
      if (hadFg && !hasActiveTasksFor(jid, senderNum)) {
        clearFgPending(jid);
        await sock.sendMessage(jid, { text: "🛑 *Cancelled pending FitGirl selection.*" }, { quoted: msg });
        return;
      }
    }

    const adminCodeCmd = body.trim().toLowerCase() === ',' + String(process.env.ADMIN_CODE || 'ezio12345').trim().toLowerCase();
    const downloaderCommand = adminCodeCmd || /^,(dl|dl1|dlr|rename|zip|unzip|gofile|torrent|magnet|limit|setlimit|addlimit|removelimit|resetlimit|limitcheck|mylimit|checklimit|status|admin|addadmin|removeadmin|admins|block|unblock|cancelall|restart|reboot|setgroup|groups|selectgroup|removegroup|rar|tasks|task|cancel|up|uplist|updel|users|stats|check|template)\b/i.test(body) || /^up$/i.test(body) || /^[.,]speed\b/i.test(body);
    if (!downloaderCommand && !/^[.,]/.test(body) && await tryPendingRarReply(stableSock, msg, body)) return;
    if (downloaderCommand) {
      await handleDownloaderMessage(stableSock, msg);
      return;
    }

    if (body.startsWith(",")) body = "." + body.slice(1);
    const lower = body.toLowerCase();

    if (lower === ".alive") {
      const pingMs = msg.messageTimestamp
        ? Math.max(0, Date.now() - Number(msg.messageTimestamp) * 1000)
        : 0;
      const memMb = (process.memoryUsage().rss / (1024 * 1024)).toFixed(1);
      const disk = getDiskSpaceInfo(".");
      const diskLine = disk
        ? `\n┠ Disk → ${disk.freeText} free of ${disk.totalText} (${disk.usedPercent}% used)`
        : "";

      await sock.sendMessage(jid, {
        text:
          `╔═══『 ✅ 𝗠𝗣𝗠 𝗔𝗟𝗜𝗩𝗘 』═══╗\n` +
          `┟ Status → Alive & Working\n` +
          `┠ Uptime → ${formatUptime(Date.now() - BOT_STARTED_AT)}\n` +
          `┠ Latency → ${pingMs} ms\n` +
          `┠ RAM → ${memMb} MB` +
          diskLine
      });
      return;
    }

    if (lower === ".cancel" || lower === ".stop") {
      const hadSelection = pendingSelectionByChat.delete(jid);
      const hadAction = pendingActionByChat.delete(jid);
      const hadFg = Boolean(
        pendingFgSearchByChat.delete(jid) |
        pendingFgActionByChat.delete(jid) |
        pendingFgFileSelectByChat.delete(jid) |
        pendingFgRarNameByChat.delete(jid)
      );
      const activeTask = activeTasksByChat.get(jid);

      if (activeTask) {
        activeTask.cancelled = true;
        try { activeTask.cancelFn?.(); } catch {}
        activeTasksByChat.delete(jid);
      }

      if (activeTask || hadSelection || hadAction || hadFg) {
        await sock.sendMessage(
          jid,
          { text: activeTask ? "🛑 *Cancelled active torrent/upload task.*" : "🛑 *Cancelled pending selection/action.*" },
          { quoted: msg }
        );
      } else {
        await sock.sendMessage(jid, { text: "ℹ️ No active task to cancel." }, { quoted: msg });
      }
      return;
    }

    if (lower === ".task" || lower === ".tasks") {
      const activeTask = activeTasksByChat.get(jid);
      if (!activeTask) {
        await sock.sendMessage(jid, { text: "ℹ️ No active task running right now." }, { quoted: msg });
        return;
      }

      const elapsed = formatUptime(Date.now() - (activeTask.startedAt || Date.now()));
      const stage = activeTask.stage || "Running";
      const pctStr = activeTask.pct !== undefined ? `${activeTask.pct}%` : "N/A";
      const dlLine = activeTask.downloadedText ? `📥 *Downloaded:* *${activeTask.downloadedText}*\n` : "";
      const remLine = activeTask.remainingText ? `📤 *Remaining:* *${activeTask.remainingText}*\n` : "";
      const spdLine = activeTask.speedText ? `🚀 *Speed:* *${activeTask.speedText}*\n` : "";

      await sock.sendMessage(
        jid,
        {
          text:
            `📌 *Active Task Status*\n\n` +
            `🎬 *Item:* *${activeTask.label}*\n` +
            `📦 *Source:* *${activeTask.source}*\n` +
            `⚙️ *Stage:* *${stage}*\n` +
            `📈 *Progress:* *${pctStr}*\n` +
            dlLine + remLine + spdLine +
            `⏱️ *Elapsed:* *${elapsed}*`
        },
        { quoted: msg }
      );
      return;
    }

    if (lower === ".com" || lower === ".commands" || lower === ".help" || lower === ".menu") {
      await sock.sendMessage(jid, {
        text:
          "╔══════════════════════════════╗\n" +
          "  ✨ *𝗠𝗣𝗠 𝗗𝗢𝗪𝗡𝗟𝗢𝗔𝗗𝗘𝗥 𝗣𝗥𝗢* ✨\n" +
          "  🚀 High-Speed WhatsApp Downloader\n" +
          "╚══════════════════════════════╝\n\n" +
          "📥 *𝗗𝗢𝗪𝗡𝗟𝗢𝗔𝗗 & 𝗙𝗜𝗟𝗘 𝗧𝗢𝗢𝗟𝗦*\n" +
          "╭──────────────────────────────\n" +
          "│ 🔗 ,dl <link>\n" +
          "│    ↳ Download direct files or Gofile folders.\n│\n" +
          "│ 🧲 ,torrent [PREFIX] <magnet / .torrent URL>\n" +
          "│    ↳ Download torrent; optional prefix is added to filenames.\n│\n" +
          "│ 🧲 ,magnet [PREFIX] <magnet link>\n" +
          "│    ↳ Download magnet; optional prefix is added to filenames.\n│\n" +
          "│ 🏷️ ,dl1 <link>\n" +
          "│    ↳ Download with [MPM] tag in filename.\n│\n" +
          "│ ✍️ ,dlr [PREFIX] <link>\n" +
          "│    ↳ Download with your custom file prefix.\n│\n" +
          "│ 📝 ,rename [New Name] <link>\n" +
          "│    ↳ Download and rename file before sending.\n│\n" +
          "│ 📦 ,zip [PREFIX] <link>\n" +
          "│    ↳ Extract ZIP and add prefix to all files.\n│\n" +
          "│ 📂 ,unzip [PREFIX] <link>\n" +
          "│    ↳ Extract ZIP and upload inner contents.\n│\n" +
          "│ 🗜️ ,rar <name>  |  ,rar <1-3>\n" +
          "│    ↳ Files over 2 GB: type the RAR name, then pick part size (1 / 1.5 / 1.9 GB).\n│\n" +
          "│ 🎯 ,setgroup  |  ,groups\n" +
          "│    ↳ Save up to 5 target groups and view them.\n│\n" +
          "│ 🖼️ ,template  (poster caption template)\n│\n" +
          "│ 🔀 ,selectgroup <1-5>\n" +
          "│    ↳ Choose where private Gofile downloads go.\n│\n" +
          "│ 🗑️ ,removegroup <number> (Owner)\n" +
          "│    ↳ Remove a saved target group.\n│\n" +
          "│ 🛑 ,cancel\n" +
          "│    ↳ Stop your active download or upload.\n│\n" +
          "│ 🛑 ,cancelall (Admin/Owner)\n" +
          "│    ↳ Cancel all active tasks and clear queued tasks.\n" +
          "╰──────────────────────────────\n\n" +
          "🎬 *𝗠𝗢𝗩𝗜𝗘 & 𝗧𝗩 𝗙𝗜𝗡𝗗𝗘𝗥*\n" +
          "╭──────────────────────────────\n" +
          "│ 🎥 ,movie <Movie Name>\n" +
          "│    ↳ Find movie releases with poster and quality options.\n│\n" +
          "│ 📺 ,tv <Show> <Season/Episode> [Quality]\n" +
          "│    ↳ Search TV episodes and season releases.\n│\n" +
          "│ 📦 ,series <Show> <Season/Episode> [Quality]\n" +
          "│    ↳ Search series releases.\n│\n" +
          "│ 📚 ,tvinfo <Show Name>\n" +
          "│    ↳ Show season counts, episode counts and status (metadata only).\n│\n" +
          "│ ⭐ ,psa <Name> <Season/Episode/pack> [Quality]\n" +
          "│    ↳ Find PSA releases; supports 720p / 1080p / 2160p.\n│\n" +
          "│ 🆓 ,freefilm <Movie Name>\n" +
          "│    ↳ Search open-license films (Internet Archive + Wikimedia Commons) with formats / quality.\n│\n" +
          "│ 🆓 ,legalrelease <Movie Name>\n" +
          "│    ↳ Alias for the open-license film catalogue.\n│\n" +
          "│ 🔍 ,sources\n" +
          "│    ↳ Check live status of download, metadata and legal catalogue APIs.\n" +
          "╰──────────────────────────────\n\n" +
          "🎮 *𝗚𝗔𝗠𝗜𝗡𝗚*\n" +
          "╭──────────────────────────────\n" +
          "│ 🎮 ,fg <Game Name>\n" +
          "│    ↳ Search FitGirl repacks, select files, then leech as auto-sized RAR parts.\n│\n" +
          "│ 📥 ,gofile <link>\n" +
          "│    ↳ DM progress; send files only to selected group.\n│\n" +
          "│ 📂 ,up  (upload `upload` folder → target group)\n" +
          "│    ↳ ,up 1 to 10  |  ,up 5 to 9  |  ,up 3  (only those files)\n│\n" +
          "│ 📋 ,uplist  (list files in `upload` folder)\n│\n" +
          "│ 🗑️ ,updel <no / all>  (delete files from `upload`)\n" +
          "╰──────────────────────────────\n\n" +
          "👤 *𝗔𝗖𝗖𝗢𝗨𝗡𝗧 & 𝗤𝗨𝗢𝗧𝗔*\n" +
          "╭──────────────────────────────\n" +
          "│ 🎟️ ,mylimit\n" +
          "│    ↳ Check quota, used data and expiry date.\n│\n" +
          "│ 📊 ,limitcheck  |  ,checklimit\n" +
          "│    ↳ View your download limit and daily usage.\n│\n" +
          "│ ⚡ ,status\n" +
          "│    ↳ Check account status or live dashboard.\n│\n" +
          "│ 📜 ,menu  |  ,help  |  ,com\n" +
          "│    ↳ Open this bot command menu.\n" +
          "╰──────────────────────────────\n\n" +
          "🛡️ *𝗔𝗗𝗠𝗜𝗡 𝗖𝗢𝗡𝗧𝗥𝗢𝗟𝗦*\n" +
          "╭──────────────────────────────\n" +
          "│ 🎯 ,limit <size> <days> <number>\n" +
          "│    ↳ Assign fresh data quota and validity days.\n│\n" +
          "│ ➕ ,addlimit <size> <days> <number>\n" +
          "│    ↳ Add extra data and extend validity period.\n│\n" +
          "│ 🗑️ ,removelimit <number>\n" +
          "│    ↳ Remove assigned data limit from a user.\n│\n" +
          "│ 🔄 ,resetlimit <number>\n" +
          "│    ↳ Reset a user's used data back to zero.\n│\n" +
          "│ 🔍 ,limitcheck <number>\n" +
          "│    ↳ Inspect another user's quota and usage.\n│\n" +
          "│ ⚙️ ,tasks\n" +
          "│    ↳ Monitor all users' active download/upload tasks.\n│\n" +
          "│ 👥 ,users\n" +
          "│    ↳ List users with a limit, usage and days left.\n│\n" +
          "│ 📊 ,stats\n" +
          "│    ↳ Download statistics (today / 7 days / top users).\n│\n" +
          "│ 🩺 ,check\n" +
          "│    ↳ Health check: connection, disk, memory, aria2, internet, routing.\n" +
          "╰──────────────────────────────\n\n" +
          "👑 *𝗢𝗪𝗡𝗘𝗥 / 𝗔𝗗𝗠𝗜𝗡 𝗖𝗢𝗡𝗧𝗥𝗢𝗟𝗦*\n" +
          "╭──────────────────────────────\n" +
          "│ 🌟 ,admin (Reply)\n" +
          "│    ↳ Reply to a person's message with ,admin to promote them.\n│\n" +
          "│ 🌟 ,addadmin <number>\n" +
          "│    ↳ Promote a user to bot admin by number.\n│\n" +
          "│ 🔻 ,removeadmin <number>\n" +
          "│    ↳ Remove admin access from a user.\n│\n" +
          "│ 📋 ,admins\n" +
          "│    ↳ View bot owner and all active admins.\n│\n" +
          "│ 🚫 ,block <number>\n" +
          "│    ↳ Block a user from using the bot.\n│\n" +
          "│ ✅ ,unblock <number>\n" +
          "│    ↳ Unblock and restore user access.\n" +
          "╰──────────────────────────────\n\n" +
          "📞 *𝗖𝗢𝗡𝗧𝗔𝗖𝗧 & 𝗦𝗨𝗣𝗣𝗢𝗥𝗧*\n" +
          "╭──────────────────────────────\n" +
          "│ 📱 Owner: +94722984072\n" +
          "│    ↳ Message for limits, support and help.\n" +
          "╰──────────────────────────────\n\n" +
          "📌 *Tip:* Always start commands with a comma (, )\n" +
          "⚡ *𝗣𝗼𝘄𝗲𝗿𝗲𝗱 𝗯𝘆 𝗠𝗣𝗠 𝗦𝘆𝘀𝘁𝗲𝗺*"
      }, { quoted: msg });
      return;
    }

    if (lower === ".sources" || lower === ".source") {
      await sock.sendMessage(jid, { text: "🔍 *Checking all configured sources & APIs... Please wait.*" }, { quoted: msg });

      try {
        const results = await checkAllBotSourcesLive();
        const totals = {
          WORKING: results.filter((r) => r.status === "WORKING").length,
          LIMITED: results.filter((r) => r.status === "LIMITED").length,
          FAILED: results.filter((r) => r.status === "FAILED").length,
          BLOCKED: results.filter((r) => r.status === "BLOCKED").length
        };
        const categories = [
          "Torrent Search Sources",
          "Movie / TV Sources",
          "Metadata Source",
          "YTS Mirrors",
          "Metadata & Legal Catalogue"
        ];
        const sectionBlocks = categories.map((cat) => {
          const items = results.filter((r) => r.category === cat);
          const lines = items.map((item) => {
            if (item.status === "WORKING" || item.status === "LIMITED") {
              return `${item.icon} *${item.name}* – ${item.label} – \`${item.ms}ms\` _(${item.searchResult})_`;
            }
            const errNote = item.error ? ` _(${item.error})_` : "";
            return `${item.icon} *${item.name}* – ${item.label}${errNote}`;
          });
          return `📂 *${cat}*\n${lines.join("\n")}`;
        });

        const checkedAt = new Date().toLocaleString("en-GB", {
          year: "numeric", month: "short", day: "2-digit",
          hour: "2-digit", minute: "2-digit", second: "2-digit"
        });

        const reportText =
          `📡 *MPM SOURCE MONITOR*\n` +
          `🔎 *Total checked:* ${results.length}\n` +
          `━━━━━━━━━━━━━━━━━━━━\n` +
          `🟢 *Working:* ${totals.WORKING}\n` +
          `🟡 *Limited:* ${totals.LIMITED}\n` +
          `🔴 *Failed:* ${totals.FAILED}\n` +
          `🛡️ *Blocked:* ${totals.BLOCKED}\n` +
          `━━━━━━━━━━━━━━━━━━━━\n\n` +
          `${sectionBlocks.join("\n\n")}\n\n` +
          `━━━━━━━━━━━━━━━━━━━━\n` +
          `🕒 *Last Checked:* ${checkedAt}`;

        await sock.sendMessage(jid, { text: reportText }, { quoted: msg });
      } catch (err) {
        await sock.sendMessage(jid, { text: `⚠️ Source check error: ${err.message}` }, { quoted: msg });
      }
      return;
    }

    // FitGirl: waiting for the RAR archive name
    {
      const fgCtx = getFgPending(pendingFgRarNameByChat, jid, msg);
      if (fgCtx) {
        if (/^\./.test(body)) {
          pendingFgRarNameByChat.delete(jid);
        } else {
          pendingFgRarNameByChat.delete(jid);
          const rarBaseName = sanitizeFileName(body).replace(/\.rar$/i, "").trim();
          if (!rarBaseName) {
            await sock.sendMessage(jid, { text: "⚠️ Please send a valid name for the RAR archive." }, { quoted: msg });
            return;
          }
          const torrentSource = buildMagnetUri(fgCtx.game) || fgCtx.game.torrentUrl;
          if (!torrentSource && !fgCtx.torrentBuffer) {
            await sock.sendMessage(jid, { text: "❌ No magnet link or .torrent URL found on that FitGirl repack page." }, { quoted: msg });
            return;
          }
          try {
            await runFitGirlLeechAndRarUpload(sock, jid, msg, fgCtx.game, rarBaseName, torrentSource, {
              selectFile: fgCtx.selectFile || "",
              selectedCount: fgCtx.selectedCount || 0,
              selectedPaths: fgCtx.selectedPaths || null,
              torrentBuffer: fgCtx.torrentBuffer || null
            });
          } catch (err) {
            await sock.sendMessage(jid, { text: `⚠️ FitGirl error: ${err.message}` }, { quoted: msg });
          }
          return;
        }
      }
    }

    // FitGirl: waiting for file selection (1-10 | 1,10 | 1-10,12 | 2,5,8 | all)
    {
      const fgFileCtx = getFgPending(pendingFgFileSelectByChat, jid, msg);
      if (fgFileCtx) {
        if (/^\./.test(body)) {
          pendingFgFileSelectByChat.delete(jid);
        } else {
          const parsed = parseFgFileSelection(body, fgFileCtx.files.length);
          if (parsed.error === "range") {
            await sock.sendMessage(jid, {
              text: `⚠️ Invalid file number! This torrent has only *${parsed.totalFiles}* file(s). Reply with numbers from *1* to *${parsed.totalFiles}* or *all*.`
            }, { quoted: msg });
            return;
          }
          if (parsed.error) {
            await sock.sendMessage(jid, {
              text: "⚠️ Invalid selection format.\nExamples:\n`1-10`\n`1,10`\n`1-10,12`\n`2,5,8`\n`all`"
            }, { quoted: msg });
            return;
          }

          pendingFgFileSelectByChat.delete(jid);
          const pickedFiles = parsed.indexes.map(i => fgFileCtx.files[i]);
          const selectFileArg = parsed.all ? "" : compressAriaIndices(pickedFiles.map(f => f.ariaIndex));
          const selectedPaths = parsed.all ? null : pickedFiles.map(f => f.diskRelPath);

          pendingFgRarNameByChat.set(jid, {
            game: fgFileCtx.game,
            selectFile: selectFileArg,
            selectedCount: pickedFiles.length,
            selectedPaths,
            torrentBuffer: fgFileCtx.torrentBuffer || null,
            createdAt: Date.now(),
            senderKey: fgSenderKey(msg)
          });

          await sock.sendMessage(jid, {
            text:
              `✅ Files Selected Successfully!\n\n` +
              `📁 Selected Files: ${pickedFiles.length}\n\n` +
              `✍️ Enter RAR File Name:`
          }, { quoted: msg });
          return;
        }
      }
    }

    // FitGirl: 1 = torrent file / magnet, 2 = leech + file selection + RAR
    if (/^[12]$/.test(body) && getFgPending(pendingFgActionByChat, jid, msg)) {
      const act = getFgPending(pendingFgActionByChat, jid, msg);
      pendingFgActionByChat.delete(jid);
      if (body === "1") {
        const sentTorrent = await sendTorrentFileOnly(sock, jid, act.game).catch(() => false);
        if (!sentTorrent) {
          const magnet = buildMagnetUri(act.game);
          if (magnet) await sock.sendMessage(jid, { text: `🧲 *${act.game.label}*\n\n\`${magnet}\`` }, { quoted: msg });
          else await sock.sendMessage(jid, { text: "⚠️ Could not fetch .torrent file or magnet link." }, { quoted: msg });
        }
        return;
      }

      const contentsSrc = buildMagnetUri(act.game) || act.game.torrentUrl;
      let meta = null;
      if (contentsSrc) {
        await sock.sendMessage(jid, { text: "⏳ Reading torrent contents… (up to ~75s)" }, { quoted: msg }).catch(() => {});
        try {
          meta = await getFitGirlTorrentContents(contentsSrc, act.game.label);
        } catch (err) {
          console.warn("[fg] contents failed:", err?.message);
          await sock.sendMessage(jid, { text: "ℹ️ Could not read the file list (" + (err?.code === "ENOENT" ? "aria2c is not installed" : err?.message || "error") + "). Continuing with all files." }, { quoted: msg }).catch(() => {});
        }
      }

      if (meta && Array.isArray(meta.files) && meta.files.length > 0) {
        await sendLongText(sock, jid, meta.text, msg);
        pendingFgFileSelectByChat.set(jid, {
          game: act.game,
          files: meta.files,
          torrentBuffer: meta.torrentBuffer,
          createdAt: Date.now(),
          senderKey: fgSenderKey(msg)
        });
        await sock.sendMessage(jid, {
          text:
            `✍️ *Select Files to Download*\n` +
            `Send file numbers or ranges:\n` +
            `• \`1-10\`\n` +
            `• \`1,10\`\n` +
            `• \`1-10,12\`\n` +
            `• \`2,5,8\`\n` +
            `• \`all\``
        }, { quoted: msg });
        return;
      }

      if (contentsSrc) {
        await sock.sendMessage(jid, { text: "ℹ️ Could not read the file list (no peers answered in time). You can still continue with all files." }, { quoted: msg }).catch(() => {});
      }
      pendingFgRarNameByChat.set(jid, { game: act.game, createdAt: Date.now(), senderKey: fgSenderKey(msg) });
      await sock.sendMessage(jid, {
        text: `✍️ *Enter RAR File Name*\n🎮 Game: *${act.game.label}*\n\nReply with the *name* you want for the RAR archive.\n• *< 10 GB* → *1 GB* parts\n• *< 20 GB* → *1.5 GB* parts\n• *≥ 20 GB* → *1.9 GB* parts`
      }, { quoted: msg });
      return;
    }

    // FitGirl: pick a game (1..10, 11 = Next page)
    if (/^(1[01]|[1-9])$/.test(body) && getFgPending(pendingFgSearchByChat, jid, msg)) {
      const session = getFgPending(pendingFgSearchByChat, jid, msg);
      const paged = getPagedItems(session.releases, session.page || 0);
      const pickedNum = Number(body);
      if (pickedNum === 11 && paged.hasMore) {
        session.page = (session.page || 0) + 1;
        await sock.sendMessage(jid, { text: formatReleasePageText(session, session.page).text });
        return;
      }
      const idx = paged.start + (pickedNum - 1);
      if (idx >= 0 && idx < session.releases.length) {
        pendingFgSearchByChat.delete(jid);
        await sock.sendMessage(jid, { text: `⏳ Getting details for *${session.releases[idx].label}*…` }, { quoted: msg }).catch(() => {});
        try {
          await promptFitGirlAction(sock, jid, msg, session.releases[idx]);
        } catch (err) {
          await sock.sendMessage(jid, { text: `⚠️ FitGirl error: ${err.message}` }, { quoted: msg });
        }
      } else {
        await sock.sendMessage(jid, { text: `⚠️ Send a number from *1* to *${paged.items.length}*.` });
      }
      return;
    }

    // Pending Torrent Action Window (1 = Download .torrent file, 2 = Leech & Upload files)
    if (/^[12]$/.test(body) && pendingActionByChat.has(jid)) {
      const actionSession = pendingActionByChat.get(jid);
      pendingActionByChat.delete(jid);
      try {
        await executeTorrentActionChoice(sock, jid, msg, actionSession.release, body);
      } catch (err) {
        await sock.sendMessage(jid, { text: `⚠️ Error: ${err.message}` });
      }
      return;
    }

    // Select a number (1..10) from the pending list or 11 -> Next pagination
    if (/^(1[01]|[1-9])$/.test(body) && pendingSelectionByChat.has(jid)) {
      const session = pendingSelectionByChat.get(jid);
      const currentPage = session.page || 0;
      const paged = getPagedItems(session.releases, currentPage);
      const pickedNum = Number(body);
      const isRepliedMessage = isReplyToBotMessage(msg, sock.user?.id, sock.user?.lid);

      if (pickedNum === 11 && paged.hasMore) {
        const nextPage = currentPage + 1;
        session.page = nextPage;
        const nextView = formatReleasePageText(session, nextPage);
        await sock.sendMessage(jid, { text: nextView.text }, isRepliedMessage ? { quoted: msg } : undefined);
        return;
      }

      const globalIdx = paged.start + (pickedNum - 1);
      if (globalIdx >= 0 && globalIdx < session.releases.length) {
        const chosen = { ...session.releases[globalIdx], isTvShow: Boolean(session.isTvShow) };
        try {
          await promptTorrentActionWindow(sock, jid, msg, chosen);
        } catch (err) {
          await sock.sendMessage(jid, { text: `⚠️ Error: ${err.message}` });
        }
      } else {
        await sock.sendMessage(jid, { text: `⚠️ Please send a number from *1* to *${paged.items.length}*.` });
      }
      return;
    }

    if (lower.startsWith(".freefilm") || lower.startsWith(".legalrelease")) {
      const query = lower.startsWith(".legalrelease") ? body.slice(13).trim() : body.slice(9).trim();
      if (!query) {
        await sock.sendMessage(jid, { text: "⚠️ Usage: ,freefilm [Movie Name] (alias: ,legalrelease)\nExample: ,freefilm Night of the Living Dead" }, { quoted: msg });
        return;
      }
      try {
        const [archiveRes, commonsRes] = await Promise.allSettled([
          searchLegalArchiveFilms(query),
          searchWikimediaCommonsVideos(query)
        ]);
        if (archiveRes.status === "rejected" && commonsRes.status === "rejected") throw archiveRes.reason;
        const films = [
          ...(archiveRes.status === "fulfilled" ? archiveRes.value : []).map((f) => ({ ...f, source: "Internet Archive" })),
          ...(commonsRes.status === "fulfilled" ? commonsRes.value : [])
        ];
        if (!films.length) {
          await sock.sendMessage(jid, { text: `ℹ️ No openly licensed / public-domain matches verified for *${query}*. Try another title.` }, { quoted: msg });
          return;
        }
        const lines = films.map((film, i) => {
          const fileLine = film.files?.length
            ? `\n   🎞️ Files: ${film.files.map(f => `${f.quality} · ${f.size}`).join(" | ")}`
            : "\n   🎞️ Video file / quality not listed";
          return `${i + 1}. *${film.title}*${film.year ? ` (${film.year})` : ""}\n   🔗 ${film.url}\n   📜 ${film.rights} · ${film.source}${fileLine}`;
        });
        await sock.sendMessage(jid, { text: `🆓 *OPEN-LICENSE FILM RESULTS*\n━━━━━━━━━━━━━━━━━━━━\n${lines.join("\n\n")}\n\n_Sources: Internet Archive, Wikimedia Commons. License details are shown per item; check the item page before reuse._` }, { quoted: msg });
      } catch (err) {
        await sock.sendMessage(jid, { text: `⚠️ Open-license search error: ${err.message}` }, { quoted: msg });
      }
      return;
    }

    if (lower.startsWith(".movie")) {
      const query = body.slice(6).trim();
      if (!query) {
        await sock.sendMessage(jid, { text: "⚠️ Usage: `,movie` [Movie Name]*\nExample: `,movie` Moana*" });
        return;
      }

      try {
        const data = await buildMovieReleaseList(query);
        if (!data.releases || data.releases.length === 0) {
          await sock.sendMessage(jid, { text: `❌ No releases found for *"${query}"*.` });
          return;
        }

        const session = {
          headerTitle: `🎬 *${data.movieTitle}*`,
          subTitle: "📋 *Available Releases (YTS.LU, YTS & PSA):*",
          releases: data.releases,
          isTvShow: false,
          page: 0,
          createdAt: Date.now()
        };
        clearFgPending(jid);
        pendingSelectionByChat.set(jid, session);

        const firstView = formatReleasePageText(session, 0);
        const ym = data.ytsMeta || null;
        let tmdbRaw = ym?.imdbId ? await getTmdbMovieByImdb(ym.imdbId) : null;
        if (!tmdbRaw) tmdbRaw = await getTmdbMovieDetails(data.metadata?.id);
        const tmdb = fillMissing(tmdbRaw, ym);
        const omdb = await fetchOmdb(data.cleanTitle, tmdb?.year || data.metadata?.year, "movie", tmdb?.imdbId || ym?.imdbId);
        const details = formatMovieDetails(data.cleanTitle, data.metadata || {}, omdb, collectQualities(data.releases), tmdb);
        await sendDetailsThenList(sock, jid, data.posterUrl, details, firstView.text);
      } catch (err) {
        await sock.sendMessage(jid, { text: `⚠️ Error: ${err.message}` });
      }
      return;
    }

    if (lower.startsWith(".psa")) {
      const rawQuery = body.slice(4).trim();
      if (!rawQuery) {
        await sock.sendMessage(jid, { text: "⚠️ Usage: `,psa` [Show/Movie] [01/S01/S02/S02E01/pack] [720p/1080p]*\nExample: `,psa` Silo 01 1080p or `,psa` Silo S02 1080p* or `,psa` Silo pack*" });
        return;
      }

      const qMatch = rawQuery.match(/\b(2160p|1080p|720p|480p)\b/i);
      const qualityFilter = qMatch ? qMatch[1].toLowerCase() : null;
      const withoutQuality = qMatch ? rawQuery.replace(qMatch[0], " ").replace(/\s+/g, " ").trim() : rawQuery;

      const seFilter = parseSeasonEpisodeFilter(withoutQuality);
      const query = seFilter.cleanedQuery || withoutQuality;
      const isTvLikeQuery = Boolean(seFilter.mode) || /\b(tv|series|show)\b/i.test(rawQuery);

      const searchQueries = [query];
      if (seFilter.mode === "episode" && seFilter.code) {
        searchQueries.push(`${query} ${seFilter.code}`);
      } else if (seFilter.mode === "season" && seFilter.seasonCode) {
        searchQueries.push(`${query} ${seFilter.seasonCode}`);
        searchQueries.push(`${query} Season ${seFilter.season}`);
        if (seFilter.packRequested) {
          searchQueries.push(`${query} ${seFilter.seasonCode} Complete`);
          searchQueries.push(`${query} Season ${seFilter.season} Complete Pack`);
        }
      } else if (seFilter.mode === "pack") {
        searchQueries.push(`${query} Season Pack`);
        searchQueries.push(`${query} Complete`);
      }

      try {
        const [wsmLists, pubLists, extraLists] = await Promise.all([
          Promise.all(searchQueries.map((q) => searchWatchSoMuchPsa(q, qualityFilter))),
          Promise.all(searchQueries.map((q) => searchApiBayMirrors(`${q} PSA`, { requirePsa: true, qualityFilter, category: "0" }))),
          Promise.all(searchQueries.map((q) => searchExtraIndexers(`${q} PSA`, { requirePsa: true, qualityFilter })))
        ]);

        const merged = [...pubLists.flat(), ...extraLists.flat(), ...wsmLists.flat()];
        const seen = new Set();
        const uniquePsa = [];
        for (const r of merged) {
          const key = `${r.infoHash || ""}|${r.torrentUrl || ""}|${r.pageUrl || ""}|${r.label.toLowerCase()}`;
          if (seen.has(key)) continue;
          seen.add(key);
          uniquePsa.push(r);
        }

        const psaList = orderAndFilterReleases(uniquePsa, {
          seFilter,
          preferPacks: seFilter.mode === "pack" || seFilter.mode === "season" || seFilter.packRequested
        }).slice(0, 30);

        if (psaList.length === 0) {
          await sock.sendMessage(jid, { text: `❌ No *PSA* releases found for *"${rawQuery}"*.` });
          return;
        }

        const filterTags = [seFilter.code ? `*${seFilter.code}*` : null, qualityFilter ? `_(${qualityFilter})_` : null].filter(Boolean).join(" ");
        const session = {
          headerTitle: `📦 *PSA Releases — ${query}*${filterTags ? ` ${filterTags}` : ""}`,
          subTitle: "📋 *Matching PSA Releases:*",
          releases: psaList,
          isTvShow: isTvLikeQuery,
          page: 0,
          createdAt: Date.now()
        };
        clearFgPending(jid);
        pendingSelectionByChat.set(jid, session);

        const firstView = formatReleasePageText(session, 0);
        await sock.sendMessage(jid, { text: firstView.text });
      } catch (err) {
        await sock.sendMessage(jid, { text: `⚠️ Error: ${err.message}` });
      }
      return;
    }

    if (lower.startsWith(".tvinfo")) {
      const showQuery = body.slice(7).trim();
      if (!showQuery) {
        await sock.sendMessage(jid, { text: "⚠️ Usage: ,tvinfo [Show Name]\nExample: ,tvinfo Silo" }, { quoted: msg });
        return;
      }
      try {
        const info = await lookupTvShowSeasons(showQuery);
        if (!info) {
          await sock.sendMessage(jid, { text: `ℹ️ No TVMaze show metadata found for *${showQuery}*.` }, { quoted: msg });
          return;
        }
        const seasonLines = info.seasons.slice(0, 20).map(season => `S${String(season.number).padStart(2, "0")} — ${season.episodeCount} episodes (${season.premiere} to ${season.finale})`);
        const message = `📺 *TV SHOW INFORMATION*\n━━━━━━━━━━━━━━━━━━━━\n*${info.name}*\n📅 Premiered: ${info.premiered}\n📡 Status: ${info.status}\n🏢 Network: ${info.network}\n🎭 Genres: ${info.genres || "Not listed"}\n\n📦 *SEASONS & EPISODES*\n${seasonLines.length ? seasonLines.join("\n") : "Season data not listed"}\n\n_Source: TVmaze. Metadata only; no download links._`;
        await sock.sendMessage(jid, { text: message }, { quoted: msg });
      } catch (err) {
        await sock.sendMessage(jid, { text: `⚠️ TV information lookup failed: ${err.message}` }, { quoted: msg });
      }
      return;
    }

    if (lower === ".fg" || lower.startsWith(".fg ")) {
      const query = body.slice(3).trim();
      if (!query) {
        await sock.sendMessage(jid, { text: "⚠️ Usage: ,fg <Game Name>\nExample: ,fg Cyberpunk 2077" }, { quoted: msg });
        return;
      }
      pendingSelectionByChat.delete(jid);
      pendingActionByChat.delete(jid);
      clearFgPending(jid);
      await sock.sendMessage(jid, { text: `🔎 Searching FitGirl for *${query}*…` }, { quoted: msg }).catch(() => {});
      try {
        const results = await searchFitGirlGames(query);
        if (results.length === 1) {
          await promptFitGirlAction(sock, jid, msg, results[0]);
          return;
        }
        const session = {
          headerTitle: `🎮 *FitGirl Search — ${query}*`, subTitle: "📋 *Select a game repack:*",
          releases: results, page: 0, createdAt: Date.now(), senderKey: fgSenderKey(msg)
        };
        pendingFgSearchByChat.set(jid, session);
        await sock.sendMessage(jid, { text: formatReleasePageText(session, 0).text }, { quoted: msg });
      } catch (err) {
        const dg = (err.diag || []).slice(0, 8).map(d => "• " + d).join("\n");
        const head = err.noResults
          ? `❌ No FitGirl repacks found for *"${query}"*.\n💡 Try the full game name, e.g. ,fg grand theft auto v`
          : `⚠️ FitGirl search failed: ${err.message}`;
        await sock.sendMessage(jid, { text: head + (dg ? `\n\n🛠️ Debug:\n${dg}` : "") }, { quoted: msg });
      }
      return;
    }

    if (lower.startsWith(".tv") || lower.startsWith(".series")) {
      const cmdLen = lower.startsWith(".series") ? 7 : 3;
      const rawQuery = body.slice(cmdLen).trim();
      if (!rawQuery) {
        await sock.sendMessage(jid, { text: "⚠️ Usage: `,tv` [Show Name] [01/S01/S02/S02E01/pack] [720p/1080p]*\nExample: `,tv` Silo 01 720p, `,tv` Silo S02E03*, `,tv` Silo pack*" });
        return;
      }

      try {
        const data = await buildTvShowReleaseList(rawQuery);
        if (!data.releases || data.releases.length === 0) {
          await sock.sendMessage(jid, { text: `❌ No TV Show torrents found for *"${rawQuery}"*.` });
          return;
        }

        const filterBadge = data.seFilter?.code ? ` *(${data.seFilter.code})*` : "";
        const session = {
          headerTitle: `📺 *${data.showTitle}*${filterBadge}`,
          subTitle: "📋 *Available TV Releases & Season Packs:*",
          releases: data.releases,
          isTvShow: true,
          page: 0,
          createdAt: Date.now()
        };
        clearFgPending(jid);
        pendingSelectionByChat.set(jid, session);

        const firstView = formatReleasePageText(session, 0);
        const tvDetails = await getTvShowDetails(data.showTitle);
        const tmdbTv = await getTmdbTvDetails(data.showTitle);
        const omdb = await fetchOmdb(data.showTitle, null, "series", tmdbTv?.imdbId);
        const details = formatTvDetails(data.showTitle, tvDetails, filterBadge, omdb, collectQualities(data.releases), tmdbTv);
        await sendDetailsThenList(sock, jid, data.posterUrl, details, firstView.text);
      } catch (err) {
        await sock.sendMessage(jid, { text: `⚠️ Error: ${err.message}` });
      }
    }
  };

  let lastErrorReplyAt = 0;
  sock.ev.on("messages.upsert", ({ messages }) => {
    for (const m of messages || []) {
      // Ignore messages that were sent while the bot was offline / before this start,
      // so a restart does not answer old commands. Set PROCESS_OLD_MESSAGES=1 in .env to turn this off.
      if (String(process.env.PROCESS_OLD_MESSAGES || "0") !== "1") {
        const ts = Number(m?.messageTimestamp?.low ?? m?.messageTimestamp ?? 0) * 1000;
        if (ts && ts < BOT_STARTED_AT - 15000) continue;
      }
      handleIncoming(m).catch(async (e) => {
        console.error("[message handler]", e?.stack || e);
        logCrash("message handler", e);
        try {
          const text = String(m?.message?.conversation || m?.message?.extendedTextMessage?.text || "").trim();
          const jid = m?.key?.remoteJid;
          if (jid && !m.key.fromMe && /^[.,][a-z]/i.test(text) && Date.now() - lastErrorReplyAt > 15000) {
            lastErrorReplyAt = Date.now();
            await sock.sendMessage(jid, { text: "⚠️ Something went wrong while handling that command. Please try again in a moment." });
          }
        } catch {}
      });
    }
  });
}

await crashLoopGuard();
startBot();