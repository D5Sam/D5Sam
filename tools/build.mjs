#!/usr/bin/env node
/**
 * build.mjs — AI 个人档案构建流水线
 *
 *   node tools/build.mjs            全流程：采集 → 脱敏 → 提炼 → 渲染 → 推送
 *   node tools/build.mjs --dry      只采集并打印统计（不落盘）
 *   node tools/build.mjs --collect  只采集，写 .local/events.ndjson
 *   node tools/build.mjs --sanitize 采集 + 脱敏，写 .local/sanitized.ndjson
 *   node tools/build.mjs --render   全流程但不推送
 *   node tools/build.mjs --no-push  同 --render
 *
 * 输出（仓库内，可公开）：
 *   README.md
 *   llms.txt
 *   profile/ai-context.md
 *   profile/ai-context.json
 *
 * 中间产物（.local/，已 gitignore，绝不入库）：
 *   events.ndjson / sanitized.ndjson / distill.json / tier-b-review.json
 */

import { createHash } from 'node:crypto';
import {
  existsSync,
  mkdirSync,
  readFileSync,
  readdirSync,
  statSync,
  writeFileSync,
} from 'node:fs';
import { homedir } from 'node:os';
import { dirname, join, resolve } from 'node:path';
import { execFileSync } from 'node:child_process';
import { fileURLToPath } from 'node:url';
import zlib from 'node:zlib';

const VERSION = '1.0.0';
const ROOT = resolve(dirname(fileURLToPath(import.meta.url)), '..');
const LOCAL_DIR = join(ROOT, '.local');
const EVENTS_FILE = join(LOCAL_DIR, 'events.ndjson');
const SANITIZED_FILE = join(LOCAL_DIR, 'sanitized.ndjson');
const DISTILL_FILE = join(LOCAL_DIR, 'distill.json');
const TIERB_FILE = join(LOCAL_DIR, 'tier-b-review.json');
const CONFIG_FILE = join(ROOT, 'profile.config.json');

// ─────────────────────────────────────────────────────────────
// 通用工具
// ─────────────────────────────────────────────────────────────

const ZSTD_MAGIC = Buffer.from([0x28, 0xb5, 0x2f, 0xfd]);

/** 按 zstd 帧魔数切分多帧文件，逐帧解压后拼回 jsonl 文本 */
function decodeMultiFrameZstd(buf) {
  const starts = [];
  let i = 0;
  while (true) {
    const idx = buf.indexOf(ZSTD_MAGIC, i);
    if (idx === -1) break;
    starts.push(idx);
    i = idx + 4;
  }
  const parts = [];
  let badFrames = 0;
  for (let k = 0; k < starts.length; k++) {
    const start = starts[k];
    const end = k + 1 < starts.length ? starts[k + 1] : buf.length;
    try {
      parts.push(zlib.zstdDecompressSync(buf.subarray(start, end)).toString('utf8'));
    } catch {
      badFrames++;
    }
  }
  return { frameCount: starts.length, badFrames, text: parts.join('') };
}

function parseJsonl(text) {
  const events = [];
  let badLines = 0;
  for (const line of text.split('\n')) {
    const t = line.trim();
    if (!t) continue;
    try {
      events.push(JSON.parse(t));
    } catch {
      badLines++;
    }
  }
  return { events, badLines };
}

function walk(dir, predicate) {
  const out = [];
  const stack = [dir];
  while (stack.length) {
    const cur = stack.pop();
    let entries;
    try {
      entries = readdirSync(cur, { withFileTypes: true });
    } catch {
      continue;
    }
    for (const e of entries) {
      const full = join(cur, e.name);
      if (e.isDirectory()) stack.push(full);
      else if (e.isFile()) {
        const hit = predicate(e.name, full);
        if (hit) {
          try {
            const st = statSync(full);
            out.push({ path: full, size: st.size, mtime: st.mtimeMs });
          } catch {
            /* ignore */
          }
        }
      }
    }
  }
  return out.sort((a, b) => a.path.localeCompare(b.path));
}

function shortHash(s) {
  return createHash('sha1').update(s).digest('hex').slice(0, 12);
}

function localIso(ms) {
  const d = new Date(ms);
  const pad = (n, w = 2) => String(n).padStart(w, '0');
  const off = -d.getTimezoneOffset();
  const sign = off >= 0 ? '+' : '-';
  return (
    d.getFullYear() + '-' + pad(d.getMonth() + 1) + '-' + pad(d.getDate()) + 'T' +
    pad(d.getHours()) + ':' + pad(d.getMinutes()) + ':' + pad(d.getSeconds()) +
    sign + pad(Math.floor(Math.abs(off) / 60)) + ':' + pad(Math.abs(off) % 60)
  );
}

const len = (s) => [...s].length;
const round = (n, d = 1) => Math.round(n * 10 ** d) / 10 ** d;

// ─────────────────────────────────────────────────────────────
// 运行时注入过滤
// ─────────────────────────────────────────────────────────────

const INJECTION_MARKERS = [
  'Current runtime context',
  'Time sampled while preparing',
  '<system-reminder',
  '<available_skills>',
  'A skill is a reusable set of task-specific instructions',
  '<user_info>',
  '<identity_context>',
  '<craft_mode>',
  '<current_time>',
  '<user_references>',
  'Note: Prefer using absolute paths',
  'Browser time zone for this request',
  'Elapsed since the preceding model-visible message',
  'The following skills are available in this session',
  '<task-notification>',
  '<task-id>',
  '<subagent',
  '<user-approval',
  '<working-directory',
  'This snapshot supersedes',
  'The user has approved',
  'tool_call_id',
];

const NON_USER_SOURCES = new Set([
  'runtime-context', 'time-context', 'skill-catalog', 'model-selection',
  'user-approval', 'tool-jobs', 'working-directory', 'agent-message',
  'subagent-settled', 'retry',
]);

function looksLikeInjection(text) {
  const head = text.slice(0, 200);
  return INJECTION_MARKERS.some((m) => head.includes(m));
}

/** 从 WorkBuddy 的系统包裹里挖出真正的 <user_query> */
function extractUserQuery(raw) {
  const q = raw.match(/<user_query>([\s\S]*?)<\/user_query>/);
  if (q) return q[1].trim();
  let rest = raw.replace(/<system-reminder[^>]*>[\s\S]*?<\/system-reminder>/g, '');
  rest = rest.replace(/<!--[\s\S]*?-->/g, '');
  return rest.trim();
}

// ─────────────────────────────────────────────────────────────
// 适配器：DSH
// ─────────────────────────────────────────────────────────────

const dshAdapter = {
  name: 'dsh',
  version: 4,
  root: join(homedir(), '.dsh', 'sessions'),
  enabled: true,

  files() {
    return walk(this.root, (name) => name === 'session.v4.jsonl.zstd');
  },

  parse(fileInfo) {
    const { frameCount, badFrames, text } = decodeMultiFrameZstd(readFileSync(fileInfo.path));
    const { events, badLines } = parseJsonl(text);

    const stats = {
      frames: frameCount, badFrames, badLines,
      rawUserMessageEvents: 0, rawAssistantMessageEvents: 0,
      keptUser: 0, keptAssistant: 0,
    };

    const head = events.find((e) => e.type === 'session');
    const sessionId = head?.id ?? shortHash(fileInfo.path);
    const cwd = head?.cwd ?? null;
    const project = cwd ? cwd.split(/[\\/]/).filter(Boolean).pop() : null;
    const createdAt = head?.createdAt ?? fileInfo.mtime;

    const out = [];
    for (const e of events) {
      if (e.type === 'user/message') {
        stats.rawUserMessageEvents++;
        const kind = e.data?.source?.kind ?? null;
        if (kind === null || NON_USER_SOURCES.has(kind)) continue;
        const t = (e.data?.content ?? [])
          .filter((b) => b?.type === 'text' && typeof b.text === 'string')
          .map((b) => b.text).join('\n').trim();
        if (!t || looksLikeInjection(t)) continue;
        stats.keptUser++;
        out.push({
          id: 'dsh:' + sessionId + ':' + (e.seq ?? shortHash(t)),
          source: 'dsh', sessionId, project,
          ts: e.time ?? createdAt, iso: localIso(e.time ?? createdAt),
          role: 'user', text: t, chars: len(t),
        });
      } else if (e.type === 'assistant/message') {
        stats.rawAssistantMessageEvents++;
        const blocks = e.data?.message?.content ?? e.data?.content ?? [];
        const t = blocks
          .filter((b) => b?.type === 'text' && typeof b.text === 'string')
          .map((b) => b.text).join('\n').trim().slice(0, 4000);
        if (!t) continue;
        stats.keptAssistant++;
        out.push({
          id: 'dsh:' + sessionId + ':' + (e.seq ?? shortHash(t)),
          source: 'dsh', sessionId, project,
          ts: e.time ?? createdAt, iso: localIso(e.time ?? createdAt),
          role: 'assistant', text: t, chars: len(t),
        });
      }
    }
    return { sessionId, project, cwd, createdAt, events: out, stats };
  },
};

// ─────────────────────────────────────────────────────────────
// 适配器：WorkBuddy
// ─────────────────────────────────────────────────────────────

const workbuddyAdapter = {
  name: 'workbuddy',
  version: 1,
  root: join(homedir(), '.workbuddy', 'projects'),
  enabled: true,

  files() {
    return walk(this.root, (name, full) =>
      /^[0-9a-f-]{36}\.jsonl$/.test(name) && !full.includes('tool-results'));
  },

  parse(fileInfo) {
    const { events, badLines } = parseJsonl(readFileSync(fileInfo.path, 'utf8'));
    const stats = { badLines, rawMessageEvents: 0, keptUser: 0, keptAssistant: 0 };

    const head = events.find((e) => e.type === 'session-meta');
    const sessionId = head?.sessionId ?? shortHash(fileInfo.path);
    const projectDir = fileInfo.path.split(/[\\/]/).slice(-2)[0];
    const project = projectDir ? projectDir.replace(/^d-/, '') : null;

    const out = [];
    for (const e of events) {
      if (e.type !== 'message') continue;
      stats.rawMessageEvents++;
      const blocks = Array.isArray(e.content) ? e.content : [];
      const raw = blocks.filter((b) => b && typeof b.text === 'string').map((b) => b.text).join('\n');
      if (!raw.trim()) continue;
      const ts = e.timestamp ?? 0;
      if (e.role === 'user') {
        const clean = extractUserQuery(raw);
        if (!clean || looksLikeInjection(clean)) continue;
        stats.keptUser++;
        out.push({
          id: 'wb:' + sessionId + ':' + (e.id ?? shortHash(clean)),
          source: 'workbuddy', sessionId, project,
          ts, iso: localIso(ts), role: 'user', text: clean, chars: len(clean),
        });
      } else if (e.role === 'assistant') {
        stats.keptAssistant++;
        out.push({
          id: 'wb:' + sessionId + ':' + (e.id ?? shortHash(raw)),
          source: 'workbuddy', sessionId, project,
          ts, iso: localIso(ts), role: 'assistant',
          text: raw.trim().slice(0, 4000), chars: len(raw.trim()),
        });
      }
    }
    return { sessionId, project, cwd: null, createdAt: events[0]?.timestamp ?? fileInfo.mtime, events: out, stats };
  },
};

const ADAPTERS = [dshAdapter, workbuddyAdapter];

// ─────────────────────────────────────────────────────────────
// S1 采集
// ─────────────────────────────────────────────────────────────

function collect() {
  const report = { adapters: [], events: [] };

  for (const adapter of ADAPTERS) {
    if (!adapter.enabled) continue;
    const t0 = Date.now();
    const files = adapter.files();
    const sessions = [];
    const adapterEvents = [];
    const a = {
      name: adapter.name, version: adapter.version, root: adapter.root,
      sessionFiles: files.length, rawUserMessageEvents: 0, rawAssistantMessageEvents: 0,
      rawMessageEvents: 0, keptUser: 0, keptAssistant: 0,
      badFrames: 0, badLines: 0, sessionsWithZeroUser: 0,
    };

    for (const f of files) {
      const res = adapter.parse(f);
      const s = res.stats;
      a.rawUserMessageEvents += s.rawUserMessageEvents ?? 0;
      a.rawAssistantMessageEvents += s.rawAssistantMessageEvents ?? 0;
      a.rawMessageEvents += s.rawMessageEvents ?? 0;
      a.keptUser += s.keptUser;
      a.keptAssistant += s.keptAssistant;
      a.badFrames += s.badFrames ?? 0;
      a.badLines += s.badLines ?? 0;
      if (s.keptUser === 0) a.sessionsWithZeroUser++;

      sessions.push({
        sessionId: res.sessionId, project: res.project, cwd: res.cwd,
        createdAt: res.createdAt,
        startedAt: res.events[0]?.iso ?? null,
        endedAt: res.events.at(-1)?.iso ?? null,
        userMessages: s.keptUser, assistantMessages: s.keptAssistant,
      });
      adapterEvents.push(...res.events);
    }

    adapterEvents.sort((x, y) => x.ts - y.ts || x.id.localeCompare(y.id));
    a.elapsedMs = Date.now() - t0;
    a.sessionCount = sessions.length;
    a.eventCount = adapterEvents.length;
    a.userChars = adapterEvents.filter((e) => e.role === 'user').reduce((n, e) => n + e.chars, 0);
    a.assistantChars = adapterEvents.filter((e) => e.role === 'assistant').reduce((n, e) => n + e.chars, 0);
    a.sessions = sessions;

    report.adapters.push(a);
    report.events.push(...adapterEvents);
  }

  report.events.sort((x, y) => x.ts - y.ts || x.id.localeCompare(y.id));
  report.totalEvents = report.events.length;
  return report;
}

// ─────────────────────────────────────────────────────────────
// S2-a 脱敏
// Tier C：永不输出，硬替换
// ─────────────────────────────────────────────────────────────

const REDACTIONS = [
  ['api-key', /\b(?:sk|pk|rk|ghp|gho|ghu|ghs|ghr)_?[A-Za-z0-9_\-]{12,}\b/g, '‹key›'],
  ['bearer', /\bBearer\s+[A-Za-z0-9._\-]{12,}/gi, 'Bearer ‹token›'],
  ['secret-assign', /(?:api[_-]?key|token|secret|password|passwd|pwd)\s*[:=]\s*["']?[A-Za-z0-9._\-]{8,}/gi, '‹credential›'],
  ['email', /[A-Za-z0-9._%+\-]+@[A-Za-z0-9.\-]+\.[A-Za-z]{2,}/g, '‹email›'],
  ['phone-cn', /(?<!\d)1[3-9]\d{9}(?!\d)/g, '‹手机号›'],
  ['idcard', /(?<!\d)\d{17}[\dXx](?!\d)/g, '‹证件号›'],
  ['card', /(?<!\d)\d{16,19}(?!\d)/g, '‹长数字号›'],
  ['priv-ip', /\b(?:10\.\d{1,3}|192\.168|172\.(?:1[6-9]|2\d|3[01]))\.\d{1,3}\.\d{1,3}\b/g, '‹内网地址›'],
  ['home-path', /[A-Za-z]:\\Users\\[^\\\s"'*?<>|]+/gi, 'C:\\Users\\‹user›'],
  ['unc-path', /\\\\[A-Za-z0-9.\-_]+\\[^\s"']+/g, '‹网络路径›'],
  ['win-path', /[A-Za-z]:\\(?:[^\\\/:*?"<>|\r\n]+\\)*[^\\\/:*?"<>|\r\n]*/g, '‹本地路径›'],
  ['url-creds', /\bhttps?:\/\/[^\s/:@]+:[^\s/@]+@/g, 'https://‹cred›@'],
];

/** 机构类关键词：命中即列入 Tier B 待确认清单 */
const INSTITUTION_PATTERNS = [
  /[\u4e00-\u9fa5]{2,8}(?:大学|学院|研究院|银行|证券|保险|集团|医院|研究院|事务所)/g,
  /\b[A-Za-z0-9.-]+\.edu\.cn\b/g,
];

function applyRedactions(text) {
  let out = text;
  const hits = {};
  for (const [name, re, to] of REDACTIONS) {
    const matches = out.match(re);
    if (matches) {
      hits[name] = (hits[name] ?? 0) + matches.length;
      out = out.replace(re, to);
    }
  }
  return { text: out, hits };
}

function sanitizeReport(report, config) {
  const redactionTotals = {};
  const tierB = new Map();
  const extraBlock = (config?.redact?.institutions ?? []).filter(Boolean);

  const events = report.events.map((e) => {
    const { text, hits } = applyRedactions(e.text);
    for (const [k, v] of Object.entries(hits)) redactionTotals[k] = (redactionTotals[k] ?? 0) + v;

    for (const re of INSTITUTION_PATTERNS) {
      const m = text.match(re);
      if (!m) continue;
      for (const s of m) {
        if (s.length < 3) continue;
        const prev = tierB.get(s) ?? { term: s, count: 0, sampleIds: [] };
        prev.count++;
        if (prev.sampleIds.length < 3) prev.sampleIds.push(e.id);
        tierB.set(s, prev);
      }
    }
    return { ...e, text };
  });

  // 配置里显式拉黑的词，直接硬替换
  if (extraBlock.length) {
    for (const ev of events) {
      for (const term of extraBlock) {
        if (ev.text.includes(term)) {
          ev.text = ev.text.split(term).join('‹机构›');
          redactionTotals['config-institution'] = (redactionTotals['config-institution'] ?? 0) + 1;
        }
      }
    }
  }

  return {
    events,
    redactionTotals,
    tierB: [...tierB.values()].sort((a, b) => b.count - a.count).slice(0, 40),
  };
}

// ─────────────────────────────────────────────────────────────
// S2-b 提炼
// ─────────────────────────────────────────────────────────────

const TOPIC_RULES = [
  ['结构仿真 / FEA', /abaqus|ansys|calculix|comsol|adams|\bcst\b|仿真|有限元|网格|拓扑优化|载荷|约束|应力|odb|\binp\b|模态|springback|回弹/i],
  ['三维建模 / CAD', /solidworks|建模|装配体|零件|工程图|\bxt\b|step文件|三维模型|参数化/i],
  ['机械检测 / 计量', /螺纹|通规|止规|检测|计量|工装|量规|公差/i],
  ['轻量化 / 结构设计', /轻量化|减重|仿生|人形机器人|连杆|拓扑|支架|航空发动机/i],
  ['AI 工具链 / 插件', /插件|skill|\bmcp\b|\bdsh\b|安装|配置|模型|api|token|token|提示词|工作流/i],
  ['文档交付 / 排版', /ppt|word|docx|报告|排版|导出|pdf|模板|页/i],
  ['数据分析 / 脚本', /python|脚本|数据|\bcsv\b|excel|爬|自动化|批处理/i],
  ['个人档案 / 记忆', /记忆|档案|会话|profile|个人主页|github/i],
];

const STYLE_SIGNALS = [
  ['要求落盘到指定目录', /所有文件|保存在|放到|目录|文件夹|路径/i],
  ['不喜欢反复确认，要直接产出', /不用.{0,6}确认|不用问我|直接(?:导出|生成|做|写|给)/i],
  ['要求可见证据（截图/结果图/数据）', /截图|显示|效果要明显|给我看|证明|实测|跑通/i],
  ['拒绝专业术语黑话', /看不懂|术语|说人话|通俗|别用.{0,4}词/i],
  ['坚持数据不出本机 / 别占 C 盘', /不出本机|本地|不要放.{0,4}C盘|不想放在C盘|D盘|隐私/i],
  ['同一问题会反复追问直到解决', null],
];

/** 从命中集合里挑最有代表性的引用：偏短、含中文、不是链接开头 */
function pickEvidence(hits, n = 2) {
  const score = (e) => {
    let s = 0;
    const t = e.text;
    if (/[\u4e00-\u9fa5]/.test(t)) s += 2;
    if (!/^(https?:|@|<)/.test(t)) s += 2;
    if (e.chars <= 40) s += 3;
    else if (e.chars <= 80) s += 2;
    else if (e.chars <= 160) s += 1;
    if (/[?？]/.test(t) || /(请|帮我|不要|需要|直接|必须)/.test(t)) s += 1;
    return s;
  };
  return hits
    .map((e) => ({ e, s: score(e) }))
    .sort((a, b) => b.s - a.s || b.e.ts - a.e.ts)
    .slice(0, n)
    .map(({ e }) => ({ date: e.iso.slice(0, 10), quote: e.text.replace(/\s+/g, ' ').slice(0, 40) }));
}

function buildDistill(report, sanitized) {
  const userEvents = sanitized.events.filter((e) => e.role === 'user');
  const asstEvents = sanitized.events.filter((e) => e.role === 'assistant');

  // 活跃时段
  const hours = new Array(24).fill(0);
  for (const e of userEvents) hours[new Date(e.ts).getHours()]++;
  const hourBuckets = [
    ['凌晨 0–6', [0, 1, 2, 3, 4, 5]],
    ['上午 6–12', [6, 7, 8, 9, 10, 11]],
    ['下午 12–18', [12, 13, 14, 15, 16, 17]],
    ['晚上 18–24', [18, 19, 20, 21, 22, 23]],
  ].map(([label, hs]) => ({ label, count: hs.reduce((n, h) => n + hours[h], 0) }));
  const peakHour = hours.indexOf(Math.max(...hours));

  // 语言：按「消息主体语言」判定，而不是逐字符（逐字符会被路径和英文术语带偏）
  let cjk = 0;
  let latin = 0;
  let zhMessages = 0;
  let enMessages = 0;
  for (const e of userEvents) {
    let c = 0;
    let l = 0;
    for (const ch of e.text) {
      if (/[\u4e00-\u9fa5]/.test(ch)) c++;
      else if (/[A-Za-z]/.test(ch)) l++;
    }
    cjk += c;
    latin += l;
    if (c > l) zhMessages++;
    else if (l > c) enMessages++;
  }
  const cjkRatio = cjk + latin ? cjk / (cjk + latin) : 0;
  const zhMessageRatio = userEvents.length ? zhMessages / userEvents.length : 0;

  // 提问风格：句中只要出现疑问词就算提问（中文很少以「？」收尾）
  const total = userEvents.length || 1;
  const questionish = userEvents.filter((e) =>
    /[?？]/.test(e.text)
    || /(为什么|怎么|如何|能不能|可以吗|是不是|有没有|哪些|什么|多少|哪一|是否|吗[。！!]?$)/.test(e.text)).length;
  const short = userEvents.filter((e) => e.chars <= 20).length;
  const long = userEvents.filter((e) => e.chars >= 200).length;

  const norm = (s) => s.replace(/\s+/g, '').slice(0, 40);
  const counts = new Map();
  for (const e of userEvents) {
    const k = norm(e.text);
    counts.set(k, (counts.get(k) ?? 0) + 1);
  }
  const repeats = [...counts.entries()].filter(([, n]) => n >= 3).sort((a, b) => b[1] - a[1]).slice(0, 5);

  const styleSignals = STYLE_SIGNALS.filter(([, re]) => re).map(([label, re]) => {
    const hits = userEvents.filter((e) => re.test(e.text));
    return {
      label,
      count: hits.length,
      ratio: round(hits.length / total, 2),
      evidence: pickEvidence(hits),
    };
  }).filter((s) => s.count > 0).sort((a, b) => b.count - a.count);

  // 主题分桶
  const topics = TOPIC_RULES.map(([name, re]) => {
    const hits = userEvents.filter((e) => re.test(e.text));
    return {
      name,
      count: hits.length,
      share: round(hits.length / total, 2),
      evidence: pickEvidence(hits),
    };
  }).filter((t) => t.count > 0).sort((a, b) => b.count - a.count);

  // 会话与时间跨度
  const sessions = report.adapters.flatMap((a) =>
    (a.sessions ?? []).filter((s) => s.userMessages > 0).map((s) => ({ ...s, adapter: a.name })));
  const dates = userEvents.map((e) => e.iso.slice(0, 10)).sort();

  return {
    generatedFrom: {
      adapters: report.adapters.map((a) => ({
        name: a.name, version: a.version, sessionFiles: a.sessionFiles,
        sessionCount: a.sessionCount,
      })),
      dataThrough: dates.at(-1) ?? null,
      firstSeen: dates[0] ?? null,
    },
    totals: {
      sessions: sessions.length,
      userMessages: userEvents.length,
      assistantMessages: asstEvents.length,
      userChars: userEvents.reduce((n, e) => n + e.chars, 0),
      activeDays: new Set(dates).size,
    },
    rhythm: { hours, peakHour, buckets: hourBuckets },
    language: {
      zhMessageRatio: round(zhMessageRatio, 3),
      zhMessages,
      enMessages,
      cjkRatio: round(cjkRatio, 3),
      cjkChars: cjk,
      latinChars: latin,
    },
    style: {
      avgChars: round(userEvents.reduce((n, e) => n + e.chars, 0) / total, 1),
      medianish: round(
        userEvents.map((e) => e.chars).sort((a, b) => a - b)[Math.floor(total / 2)] ?? 0, 1),
      questionRatio: round(questionish / total, 2),
      shortRatio: round(short / total, 2),
      longRatio: round(long / total, 2),
      repeatedAsks: repeats.map(([k, n]) => ({ text: k, times: n })),
      signals: styleSignals,
    },
    topics: topics.slice(0, 8),
    sessions: sessions
      .sort((a, b) => b.userMessages - a.userMessages)
      .map((s) => ({
        adapter: s.adapter,
        project: s.project,
        userMessages: s.userMessages,
        startedAt: s.startedAt?.slice(0, 10) ?? null,
        endedAt: s.endedAt?.slice(0, 10) ?? null,
      })),
  };
}

// ─────────────────────────────────────────────────────────────
// S3-a 渲染
// ─────────────────────────────────────────────────────────────

const FENCE = String.fromCharCode(96, 96, 96);

function pct(x) {
  return Math.round(x * 100) + '%';
}

function renderAiContextJson(cfg, d) {
  return {
    schema: 'ai-context/v1',
    generatedBy: 'tools/build.mjs ' + VERSION,
    readme: 'llms.txt 是纯文本速读版；本文件是结构化版。',
    identity: {
      handle: cfg.handle,
      name: cfg.name,
      headline: cfg.headline,
      domains: cfg.domains,
      languages: {
        primary: '中文',
        zhMessageRatio: d.language.zhMessageRatio,
        note: '日常用中文，专业术语直接夹英文原词（Abaqus、SolidWorks、MCP 等不翻译）。英文长句一般来自直接贴入的英文任务模板或文档。',
      },
    },
    workingStyle: cfg.workingStyle,
    preferences: cfg.preferences.map((p) => ({ ...p, evidence: p.evidence ?? [] })),
    dislikes: cfg.dislikes,
    stack: cfg.stack,
    currentFocus: cfg.currentFocus,
    observed: {
      dataThrough: d.generatedFrom.dataThrough,
      firstSeen: d.generatedFrom.firstSeen,
      sessions: d.totals.sessions,
      userMessages: d.totals.userMessages,
      activeDays: d.totals.activeDays,
      peakHour: d.rhythm.peakHour,
      rhythm: d.rhythm.buckets,
      avgUserMessageChars: d.style.avgChars,
      questionRatio: d.style.questionRatio,
      topics: d.topics.map((t) => ({ name: t.name, count: t.count, share: t.share })),
    },
    howToHelp: cfg.howToHelp,
    boundaries: {
      // 注意：绝不回显被屏蔽的具体机构词，否则等于把敏感词本身写进公开文件
      withheldCategories: cfg.redact.institutions.length,
      withheld: ['机构名/单位名', '凭据与密钥', '联系方式', '证件号', '本机用户名路径', '内网地址'],
      note: '未出现在本档案中的话题不代表不存在，只代表未经本人确认。',
    },
  };
}

function renderAiContextMd(cfg, d) {
  const L = [];
  L.push('# ' + cfg.name + ' — AI 上下文');
  L.push('');
  L.push('> ' + cfg.headline);
  L.push('');
  L.push('本文件为机器与助手准备。纯文本速读版见 [../llms.txt](../llms.txt)，结构化版见 [ai-context.json](ai-context.json)。');
  L.push('');
  L.push('## 1. 身份');
  L.push('');
  L.push('- 账号：' + cfg.handle);
  L.push('- 主语言：中文（' + pct(d.language.zhMessageRatio) + ' 的消息以中文为主）');
  L.push('- 专业域：' + cfg.domains.join('、'));
  L.push('');
  L.push('## 2. 工作方式');
  L.push('');
  for (const w of cfg.workingStyle) L.push('- ' + w);
  L.push('');
  L.push('## 3. 协作偏好');
  L.push('');
  for (const p of cfg.preferences) {
    L.push('### ' + p.claim);
    L.push('');
    L.push(p.detail);
    if (p.evidence?.length) {
      L.push('');
      for (const ev of p.evidence) L.push('> ' + ev);
    }
    L.push('');
  }
  L.push('## 4. 不要把这样回答给他');
  L.push('');
  for (const x of cfg.dislikes) L.push('- ' + x);
  L.push('');
  L.push('## 5. 技术栈');
  L.push('');
  for (const s of cfg.stack) L.push('- **' + s.group + '**：' + s.items.join('、'));
  L.push('');
  L.push('## 6. 当前在做什么');
  L.push('');
  for (const c of cfg.currentFocus) L.push('- ' + c);
  L.push('');
  L.push('## 7. 助手应该怎么帮');
  L.push('');
  for (const h of cfg.howToHelp) L.push('- ' + h);
  L.push('');
  L.push('## 8. 观测到的行为数据');
  L.push('');
  L.push('| 指标 | 值 |');
  L.push('| --- | --- |');
  L.push('| 数据截止 | ' + d.generatedFrom.dataThrough + ' |');
  L.push('| 有效会话 | ' + d.totals.sessions + ' |');
  L.push('| 本人消息 | ' + d.totals.userMessages + ' 条 |');
  L.push('| 活跃天数 | ' + d.totals.activeDays + ' 天 |');
  L.push('| 最活跃时段 | ' + d.rhythm.peakHour + ':00 前后 |');
  L.push('| 单条消息平均字数 | ' + d.style.avgChars + ' |');
  L.push('| 疑问句占比 | ' + pct(d.style.questionRatio) + ' |');
  L.push('');
  L.push('### 主题分布（按命中消息数）');
  L.push('');
  L.push('| 主题 | 消息数 | 占比 |');
  L.push('| --- | --- | --- |');
  for (const t of d.topics) L.push('| ' + t.name + ' | ' + t.count + ' | ' + pct(t.share) + ' |');
  L.push('');
  L.push('## 9. 边界');
  L.push('');
  L.push('- 本档案由本人授权，从本机会话记录中提炼，已做分级脱敏。');
  L.push('- 不包含：凭据、联系方式、证件号、本机用户名路径、内网地址、未确认的机构名。');
  L.push('- 未出现的话题不代表不存在。');
  L.push('');
  return L.join('\n');
}

function renderLlmsTxt(cfg, d) {
  const L = [];
  L.push('# ' + cfg.name);
  L.push('');
  L.push('> ' + cfg.headline);
  L.push('');
  L.push('## 他是谁');
  L.push('');
  for (const line of cfg.whoLines) L.push(line);
  L.push('');
  L.push('## 专业域');
  L.push('');
  L.push(cfg.domains.join(' / '));
  L.push('');
  L.push('## 用什么');
  L.push('');
  for (const s of cfg.stack) L.push('- ' + s.group + '：' + s.items.join('、'));
  L.push('');
  L.push('## 怎么跟他合作');
  L.push('');
  for (const h of cfg.howToHelp) L.push('- ' + h);
  L.push('');
  L.push('## 他不喜欢');
  L.push('');
  for (const x of cfg.dislikes) L.push('- ' + x);
  L.push('');
  L.push('## 机器可读');
  L.push('');
  const base = 'https://raw.githubusercontent.com/' + cfg.handle + '/' + cfg.handle + '/main/';
  L.push('- 结构化：' + base + 'profile/ai-context.json');
  L.push('- 说明文档：' + base + 'profile/ai-context.md');
  L.push('');
  L.push('## 数据来源');
  L.push('');
  L.push('本人授权，从 ' + d.totals.sessions + ' 个有效会话（' + d.totals.userMessages + ' 条本人消息，'
    + d.generatedFrom.firstSeen + ' 至 ' + d.generatedFrom.dataThrough + '）提炼，已分级脱敏。');
  L.push('');
  return L.join('\n');
}

function renderReadme(cfg, d) {
  const L = [];
  L.push('# ' + cfg.name + ' 👋');
  L.push('');
  L.push('**' + cfg.headline + '**');
  L.push('');
  L.push('> 这份主页是给 AI 读的：任何助手花 30 秒读完，就知道我在做什么、习惯怎么被回答。');
  L.push('> 机器可读版：[llms.txt](llms.txt) · [profile/ai-context.json](profile/ai-context.json)');
  L.push('');
  L.push('---');
  L.push('');
  L.push('## 30 秒速读');
  L.push('');
  L.push('| | |');
  L.push('| --- | --- |');
  L.push('| 做什么 | ' + cfg.domains.join('；') + ' |');
  L.push('| 常用工具 | ' + cfg.stack.map((s) => s.items.slice(0, 3).join('、')).join('；') + ' |');
  L.push('| 沟通语言 | 中文，术语保留英文原词 |');
  L.push('| 回答风格 | ' + cfg.answerStyle + ' |');
  L.push('');
  L.push('## 我在做什么');
  L.push('');
  for (const c of cfg.currentFocus) L.push('- ' + c);
  L.push('');
  L.push('## 专业域');
  L.push('');
  for (const dom of cfg.domainCards) {
    L.push('### ' + dom.title);
    L.push('');
    L.push(dom.body);
    L.push('');
  }
  L.push('## 技术栈');
  L.push('');
  for (const s of cfg.stack) L.push('- **' + s.group + '** — ' + s.items.join('、'));
  L.push('');
  L.push('## 跟我协作的 6 条规则');
  L.push('');
  cfg.howToHelp.forEach((h, i) => L.push((i + 1) + '. ' + h));
  L.push('');
  L.push('## 别这样回答我');
  L.push('');
  for (const x of cfg.dislikes) L.push('- ❌ ' + x);
  L.push('');
  L.push('---');
  L.push('');
  L.push('## 这份档案怎么来的');
  L.push('');
  L.push('不是我手写的自述，是从真实会话里提炼的，每条偏好都带原文证据：');
  L.push('');
  L.push('| | |');
  L.push('| --- | --- |');
  L.push('| 数据来源 | 本机 AI 助手会话（DSH / WorkBuddy） |');
  L.push('| 有效会话 | ' + d.totals.sessions + ' 个 |');
  L.push('| 本人消息 | ' + d.totals.userMessages + ' 条 |');
  L.push('| 时间跨度 | ' + d.generatedFrom.firstSeen + ' → ' + d.generatedFrom.dataThrough + ' |');
  L.push('| 最活跃时段 | ' + d.rhythm.buckets.slice().sort((a, b) => b.count - a.count)[0].label + ' |');
  L.push('');
  L.push('**脱敏原则**：凭据、联系方式、证件号、本机用户名路径、内网地址、未确认机构名一律不输出；');
  L.push('原始会话正文只留在本机，从不进入仓库。');
  L.push('');
  L.push(FENCE + 'bash');
  L.push('# 重新生成（在本机跑，需要会话数据）');
  L.push('node tools/build.mjs');
  L.push(FENCE);
  L.push('');
  return L.join('\n');
}

// ─────────────────────────────────────────────────────────────
// S3-b 白名单硬门禁
// ─────────────────────────────────────────────────────────────

const FORBIDDEN = [
  ['api-key', /\b(?:sk|pk|rk|ghp|gho|ghu|ghs|ghr)_?[A-Za-z0-9_\-]{16,}\b/],
  ['bearer', /\bBearer\s+[A-Za-z0-9._\-]{16,}/i],
  ['email', /[A-Za-z0-9._%+\-]+@[A-Za-z0-9.\-]+\.[A-Za-z]{2,}/],
  ['phone', /(?<!\d)1[3-9]\d{9}(?!\d)/],
  ['idcard', /(?<!\d)\d{17}[\dXx](?!\d)/],
  ['home-path', /[A-Za-z]:\\Users\\/i],
  ['priv-ip', /\b(?:10\.\d{1,3}|192\.168|172\.(?:1[6-9]|2\d|3[01]))\.\d{1,3}\.\d{1,3}\b/],
  ['local-path', /[A-Za-z]:\\(?:[^\\\/:*?"<>|\r\n]+\\)*[^\\\/:*?"<>|\r\n]+/],
];

function gate(outputs, config) {
  const violations = [];
  const inst = (config?.redact?.institutions ?? []).filter(Boolean);
  for (const [name, content] of Object.entries(outputs)) {
    for (const [kind, re] of FORBIDDEN) {
      const m = content.match(re);
      if (m) violations.push({ file: name, kind, sample: m[0].slice(0, 24) });
    }
    for (const term of inst) {
      if (content.includes(term)) violations.push({ file: name, kind: 'institution', sample: term });
    }
  }
  return violations;
}

// ─────────────────────────────────────────────────────────────
// 配置
// ─────────────────────────────────────────────────────────────

function loadConfig() {
  if (!existsSync(CONFIG_FILE)) {
    throw new Error('缺少 profile.config.json（叙事层配置）。请先创建它。');
  }
  const cfg = JSON.parse(readFileSync(CONFIG_FILE, 'utf8'));
  cfg.redact = cfg.redact ?? {};
  // 机构名黑名单不能写进公开的 config（写进去就等于把敏感词本身公开），
  // 一律放 .local/redact.txt（gitignored），一行一个词。
  const file = join(LOCAL_DIR, 'redact.txt');
  const fromFile = existsSync(file)
    ? readFileSync(file, 'utf8')
        .split('\n')
        .map((s) => s.trim())
        .filter((s) => s && !s.startsWith('#'))
    : [];
  const fromConfig = (cfg.redact.institutions ?? []).filter(Boolean);
  cfg.redact.institutions = [...new Set([...fromConfig, ...fromFile])];
  return cfg;
}

// ─────────────────────────────────────────────────────────────
// CLI
// ─────────────────────────────────────────────────────────────

function printCollect(report) {
  const line = (s = '') => console.log(s);
  line('='.repeat(64));
  line('  采集报告 (build ' + VERSION + ')');
  line('='.repeat(64));
  let ts = 0;
  let tu = 0;
  let ta = 0;
  for (const a of report.adapters) {
    line('');
    line('▌ ' + a.name + '  (adapter v' + a.version + ')');
    line('  根目录            ' + a.root);
    line('  会话文件 / 会话数  ' + a.sessionFiles + ' / ' + a.sessionCount);
    if (a.name === 'dsh') {
      line('  原始 user/message  ' + a.rawUserMessageEvents + '  (含运行时注入)');
    } else {
      line('  原始 message       ' + a.rawMessageEvents + '  (含系统包裹)');
    }
    line('  真人输入           ' + a.keptUser);
    line('  助手消息           ' + a.keptAssistant);
    line('  坏帧 / 坏行        ' + a.badFrames + ' / ' + a.badLines);
    line('  无真人消息的会话   ' + a.sessionsWithZeroUser);
    line('  正文 用户/助手 字  ' + a.userChars + ' / ' + a.assistantChars);
    line('  耗时               ' + a.elapsedMs + ' ms');
    ts += a.sessionCount;
    tu += a.keptUser;
    ta += a.keptAssistant;
  }
  line('');
  line('-'.repeat(64));
  line('  合计：会话 ' + ts + '   真人消息 ' + tu + '   助手消息 ' + ta + '   事件 ' + report.totalEvents);
  line('-'.repeat(64));
  line('');
}

function main(argv) {
  const args = new Set(argv.slice(2));
  const dry = args.has('--dry');
  const onlyCollect = args.has('--collect') && !args.has('--render') && !args.has('--sanitize');

  const t0 = Date.now();
  const report = collect();
  printCollect(report);

  if (dry) {
    console.log('  （--dry：到此为止，未写任何文件）');
    return 0;
  }

  mkdirSync(LOCAL_DIR, { recursive: true });
  writeFileSync(EVENTS_FILE, report.events.map((e) => JSON.stringify(e)).join('\n') + '\n', 'utf8');
  console.log('  已写 ' + EVENTS_FILE);

  if (onlyCollect) return 0;

  const config = loadConfig();
  const san = sanitizeReport(report, config);
  writeFileSync(SANITIZED_FILE, san.events.map((e) => JSON.stringify(e)).join('\n') + '\n', 'utf8');
  writeFileSync(TIERB_FILE, JSON.stringify({ tierB: san.tierB, redactions: san.redactionTotals }, null, 2), 'utf8');

  console.log('');
  console.log('  脱敏命中：' + (Object.keys(san.redactionTotals).length
    ? Object.entries(san.redactionTotals).map(([k, v]) => k + '×' + v).join(', ')
    : '无'));
  console.log('  Tier B 待确认词 ' + san.tierB.length + ' 个（见 .local/tier-b-review.json）');

  const distill = buildDistill(report, san);
  writeFileSync(DISTILL_FILE, JSON.stringify(distill, null, 2), 'utf8');

  const jsonObj = renderAiContextJson(config, distill);
  const outputs = {
    'README.md': renderReadme(config, distill),
    'llms.txt': renderLlmsTxt(config, distill),
    'profile/ai-context.md': renderAiContextMd(config, distill),
    'profile/ai-context.json': JSON.stringify(jsonObj, null, 2) + '\n',
  };

  const violations = gate(outputs, config);
  if (violations.length) {
    console.error('');
    console.error('✗ 白名单门禁未通过，已中止写入：');
    for (const v of violations) console.error('  - ' + v.file + '  [' + v.kind + ']  ' + v.sample);
    return 2;
  }

  mkdirSync(join(ROOT, 'profile'), { recursive: true });
  for (const [rel, content] of Object.entries(outputs)) {
    writeFileSync(join(ROOT, rel), content, 'utf8');
    console.log('  写出 ' + rel + '  (' + len(content) + ' 字符)');
  }

  console.log('');
  console.log('✓ 门禁通过，全部产物已写入。耗时 ' + (Date.now() - t0) + ' ms');

  if (args.has('--no-push') || args.has('--render')) {
    console.log('  （未推送）');
    return 0;
  }

  try {
    const status = execFileSync('git', ['status', '--porcelain'], { cwd: ROOT, encoding: 'utf8' });
    if (!status.trim()) {
      console.log('  工作树无变化，无需推送（产物是幂等的）。');
      return 0;
    }
    execFileSync('git', ['add', '-A'], { cwd: ROOT });
    execFileSync('git', ['commit', '-m', 'chore(profile): 重新生成 AI 速读档案'], { cwd: ROOT });
    execFileSync('git', ['push', 'origin', 'HEAD'], { cwd: ROOT, stdio: 'inherit' });
    console.log('  已推送。');
  } catch (err) {
    console.error('  推送失败：' + err.message);
    console.error('  产物已在本地生成，可稍后用 tools\\gn.cmd push 补推。');
    return 3;
  }
  return 0;
}

process.exitCode = main(process.argv);
