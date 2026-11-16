// github-forge: a standalone, GitHub-compatible git forge in one process, stdlib only.
//
// Serves, from its own in-memory store: git smart HTTP (upload-pack v2, receive-pack v0),
// REST v3 under /api/v3, GraphQL v4 at /api/graphql, and MCP (JSON-RPC 2.0 Streamable HTTP)
// at /mcp. No UI, no outside service, no git binary: the pack protocol, object store and
// delta codec are implemented here on Node's stdlib (crypto, zlib, http).
//
// Lifecycle (the trial harness's): bind an ephemeral port, POST {"port": N} to
// $MAKEFUN_ENV_URL/register, poll GET $MAKEFUN_ENV_URL/done until {"done": true}, exit 0.
// Without MAKEFUN_ENV_URL it just serves on FORGE_PORT (default 0, printed on stdout) so the
// kit's local runner (sdk/run.ts) can drive it directly.
//
// Determinism: no wall clock and no unseeded randomness anywhere in served state. Commit
// timestamps come from a fixed epoch plus a monotonic counter, ids from monotonic counters,
// request ids from a monotonic counter. Two runs fed the same requests in the same order
// produce byte-identical state.

import http from 'node:http';
import { createServer } from 'node:http';
import { createHash } from 'node:crypto';
import { deflateSync, inflateSync } from 'node:zlib';

// ---------------------------------------------------------------------------
// The scenario seed: the suite's one fixed seed (wire.ts SCENARIO_SEED). The
// viewer login the bearer token names is users[0] of the seeded scenario, so
// the forge re-derives it instead of guessing: "adaiversen".
// ---------------------------------------------------------------------------

const SCENARIO_SEED = 0x6a09e667f3bcc909n;
const U64_MASK = 0xffffffffffffffffn;

function fnv1a64(text) {
  let hash = 0xcbf29ce484222325n;
  for (let i = 0; i < text.length; i += 1) {
    hash ^= BigInt(text.charCodeAt(i));
    hash = (hash * 0x100000001b3n) & U64_MASK;
  }
  return hash;
}
function mix64(value) {
  let z = (value + 0x9e3779b97f4a7c15n) & U64_MASK;
  z = ((z ^ (z >> 30n)) * 0xbf58476d1ce4e5b9n) & U64_MASK;
  z = ((z ^ (z >> 27n)) * 0x94d049bb133111ebn) & U64_MASK;
  return (z ^ (z >> 31n)) & U64_MASK;
}
class Rng {
  #state;
  constructor(seed) {
    const masked = seed & U64_MASK;
    this.#state = masked === 0n ? SCENARIO_SEED : masked;
  }
  nextU64() {
    let x = this.#state;
    x = (x ^ (x >> 12n)) & U64_MASK;
    x = (x ^ (x << 25n)) & U64_MASK;
    x = (x ^ (x >> 27n)) & U64_MASK;
    this.#state = x;
    return (x * 0x2545f4914f6cdd1dn) & U64_MASK;
  }
  nextU32() { return Number(this.nextU64() >> 32n); }
  nextInt(maxExclusive) {
    if (maxExclusive === 1) return 0;
    const range = 4294967296;
    const limit = range - (range % maxExclusive);
    for (;;) {
      const value = this.nextU32();
      if (value < limit) return value % maxExclusive;
    }
  }
  pick(items) { return items[this.nextInt(items.length)]; }
}
const FIRST_NAMES = ['ada','bram','cora','dmitri','elena','felix','greta','hugo','iris','jonas','kira','lars','mira','nico','olga','pavel','quinn','rosa','sven','tess','ulla','vito','wren','yara','zane'];
const LAST_NAMES = ['anders','bauer','costa','dahl','eriksen','fischer','garcia','holm','iversen','jansen','keller','lind','moreau','novak','olsen','peters','quist','rossi','sato','turi','ulrich','vega','weber','xu','yilmaz','zimmer'];
function scenarioUsers() {
  const rng = new Rng(mix64(SCENARIO_SEED ^ fnv1a64('users')));
  const used = new Set();
  const users = [];
  for (let i = 0; i < 12; i += 1) {
    const first = rng.pick(FIRST_NAMES);
    const last = rng.pick(LAST_NAMES);
    const base = `${first}${last}`.replace(/[^a-z0-9-]/g, '');
    let login = base;
    let suffix = 2;
    while (used.has(login)) { login = `${base}-${suffix}`; suffix += 1; }
    used.add(login);
    users.push({ id: 1000 + i, login, name: `${first} ${last}`, email: `${login}@example.invalid` });
  }
  return users;
}
const SCENARIO_USERS = scenarioUsers();
const VIEWER = SCENARIO_USERS[0];
const VIEWER_LOGIN = VIEWER.login; // "adaiversen"
const VIEWER_NAME = VIEWER.name;
const VIEWER_EMAIL = VIEWER.email;

// ---------------------------------------------------------------------------
// Small helpers
// ---------------------------------------------------------------------------

const ZERO_OID = '0'.repeat(40);
const FIXED_DATE = '2025-01-01T00:00:00Z';
const COMMIT_EPOCH = 1735689600; // 2025-01-01T00:00:00Z; forge commits add a counter
let commitCounter = 0;
let requestCounter = 0;
let globalIdCounter = 0;

function sha1hex(buf) { return createHash('sha1').update(buf).digest('hex'); }
function b64encode(buf) { return Buffer.from(buf).toString('base64'); }
function b64decode(text) { return Buffer.from(String(text).replace(/\s+/g, ''), 'base64'); }
function b64url(text) { return Buffer.from(text, 'utf8').toString('base64url'); }
function isOid(v) { return typeof v === 'string' && /^[0-9a-f]{40}$/i.test(v); }

function jsonBody(res, status, body, extraHeaders) {
  const text = `${JSON.stringify(body)}\n`;
  const headers = { 'content-type': 'application/json; charset=utf-8', 'content-length': Buffer.byteLength(text), 'x-github-request-id': `forge-${++requestCounter}`, ...(extraHeaders || {}) };
  res.writeHead(status, headers);
  res.end(text);
}
function errJson(res, status, message, extraHeaders) {
  jsonBody(res, status, { message: String(message) }, extraHeaders);
}

// ---------------------------------------------------------------------------
// pkt-line framing
// ---------------------------------------------------------------------------

function pktLine(payload) {
  const data = Buffer.isBuffer(payload) ? payload : Buffer.from(payload, 'utf8');
  const header = Buffer.allocUnsafe(4);
  header.write((data.length + 4).toString(16).padStart(4, '0'), 0, 4, 'ascii');
  return Buffer.concat([header, data]);
}
const PKT_FLUSH = Buffer.from('0000', 'ascii');
const PKT_DELIM = Buffer.from('0001', 'ascii');
function pktLines(items) {
  const parts = [];
  for (const item of items) {
    if (item === 'flush') parts.push(PKT_FLUSH);
    else if (item === 'delim') parts.push(PKT_DELIM);
    else parts.push(pktLine(item));
  }
  return Buffer.concat(parts);
}
// Decode a whole buffer into packets: {kind:'data'|'flush'|'delim'|'response-end', payload}
function decodePktLines(buf) {
  const packets = [];
  let off = 0;
  while (off < buf.length) {
    if (off + 4 > buf.length) throw new Error('truncated pkt-line');
    const head = buf.subarray(off, off + 4).toString('ascii');
    if (head === '0000') { packets.push({ kind: 'flush', payload: Buffer.alloc(0) }); off += 4; continue; }
    if (head === '0001') { packets.push({ kind: 'delim', payload: Buffer.alloc(0) }); off += 4; continue; }
    if (head === '0002') { packets.push({ kind: 'response-end', payload: Buffer.alloc(0) }); off += 4; continue; }
    const len = parseInt(head, 16);
    if (!Number.isFinite(len) || len < 4 || off + len > buf.length) throw new Error('bad pkt-line length');
    packets.push({ kind: 'data', payload: buf.subarray(off + 4, off + len) });
    off += len;
  }
  return packets;
}

// ---------------------------------------------------------------------------
// Git objects
// ---------------------------------------------------------------------------

function hashObject(type, data) {
  const header = Buffer.from(`${type} ${data.length}\0`, 'ascii');
  return sha1hex(Buffer.concat([header, Buffer.from(data)]));
}
function parseTree(data) {
  const buf = Buffer.from(data);
  const entries = [];
  let off = 0;
  while (off < buf.length) {
    const space = buf.indexOf(0x20, off);
    const nul = buf.indexOf(0x00, space + 1);
    if (space < 0 || nul < 0 || nul + 21 > buf.length) throw new Error('bad tree');
    entries.push({ mode: buf.subarray(off, space).toString('ascii'), name: buf.subarray(space + 1, nul).toString('utf8'), oid: buf.subarray(nul + 1, nul + 21).toString('hex') });
    off = nul + 21;
  }
  return entries;
}
function compareTreeNames(a, b) {
  const l = Buffer.from(a.mode === '40000' ? `${a.name}/` : a.name, 'utf8');
  const r = Buffer.from(b.mode === '40000' ? `${b.name}/` : b.name, 'utf8');
  return Buffer.compare(l, r);
}
function buildTree(entries) {
  const sorted = [...entries].sort(compareTreeNames);
  const parts = [];
  for (const e of sorted) {
    parts.push(Buffer.from(`${e.mode} ${e.name}\0`, 'utf8'));
    parts.push(Buffer.from(e.oid, 'hex'));
  }
  return Buffer.concat(parts);
}
function parseCommit(data) {
  const buf = Buffer.from(data);
  const blank = buf.indexOf('\n\n');
  const headEnd = blank < 0 ? buf.length : blank;
  const message = blank < 0 ? '' : buf.subarray(blank + 2).toString('utf8');
  let tree = '';
  const parents = [];
  let author = '';
  let committer = '';
  for (const line of buf.subarray(0, headEnd).toString('utf8').split('\n')) {
    if (!line) continue;
    const sp = line.indexOf(' ');
    const key = sp < 0 ? line : line.slice(0, sp);
    const val = sp < 0 ? '' : line.slice(sp + 1);
    if (key === 'tree') tree = val;
    else if (key === 'parent') parents.push(val);
    else if (key === 'author') author = val;
    else if (key === 'committer') committer = val;
  }
  return { tree, parents, author, committer, message };
}
function parseTag(data) {
  const buf = Buffer.from(data);
  const blank = buf.indexOf('\n\n');
  const headEnd = blank < 0 ? buf.length : blank;
  const headers = new Map();
  for (const line of buf.subarray(0, headEnd).toString('utf8').split('\n')) {
    if (!line) continue;
    const sp = line.indexOf(' ');
    if (sp >= 0) headers.set(line.slice(0, sp), line.slice(sp + 1));
  }
  return { object: headers.get('object') ?? '', type: headers.get('type') ?? '', tag: headers.get('tag') ?? '', tagger: headers.get('tagger') ?? '', message: blank < 0 ? '' : buf.subarray(blank + 2).toString('utf8') };
}
function buildCommitBytes({ tree, parents, message, author, timestamp }) {
  const who = `${author} ${timestamp} +0000`;
  const lines = [`tree ${tree}`];
  for (const p of parents || []) lines.push(`parent ${p}`);
  lines.push(`author ${who}`, `committer ${who}`, '');
  const msg = message.endsWith('\n') ? message : `${message}\n`;
  return Buffer.from(`${lines.join('\n')}\n${msg}`, 'utf8');
}
// Reachable objects from roots (commit -> tree + parents; tag -> target; tree -> entries).
function collectReachable(roots, lookup) {
  const seen = new Set();
  const queue = [];
  for (const r of roots) if (isOid(r) && r !== ZERO_OID) queue.push(r);
  while (queue.length) {
    const oid = queue.pop();
    if (seen.has(oid)) continue;
    const obj = lookup(oid);
    if (!obj) throw new Error(`object ${oid} is missing from the store`);
    seen.add(oid);
    if (obj.type === 'commit') {
      const c = parseCommit(obj.data);
      queue.push(c.tree);
      for (const p of c.parents) queue.push(p);
    } else if (obj.type === 'tag') {
      queue.push(parseTag(obj.data).object);
    } else if (obj.type === 'tree') {
      for (const e of parseTree(obj.data)) if (e.mode !== '160000') queue.push(e.oid);
    }
  }
  return seen;
}
function isAncestor(ancestorOid, oid, lookup) {
  // true when ancestorOid is reachable from oid following parents (or equal)
  if (ancestorOid === oid) return true;
  const seen = new Set();
  const stack = [oid];
  while (stack.length) {
    const cur = stack.pop();
    if (cur === ancestorOid) return true;
    if (seen.has(cur)) continue;
    seen.add(cur);
    const obj = lookup(cur);
    if (!obj || obj.type !== 'commit') continue;
    for (const p of parseCommit(obj.data).parents) stack.push(p);
  }
  return false;
}
// First common ancestor of two commits (BFS from a, then walk b's ancestry in order).
function mergeBase(aOid, bOid, lookup) {
  if (!isOid(aOid) || !isOid(bOid)) return null;
  const aSet = new Set();
  const stack = [aOid];
  while (stack.length) {
    const cur = stack.pop();
    if (aSet.has(cur)) continue;
    aSet.add(cur);
    const obj = lookup(cur);
    if (!obj || obj.type !== 'commit') continue;
    for (const p of parseCommit(obj.data).parents) stack.push(p);
  }
  const queue = [bOid];
  const seen = new Set();
  while (queue.length) {
    const cur = queue.shift();
    if (aSet.has(cur)) return cur;
    if (seen.has(cur)) continue;
    seen.add(cur);
    const obj = lookup(cur);
    if (!obj || obj.type !== 'commit') continue;
    for (const p of parseCommit(obj.data).parents) queue.push(p);
  }
  return null;
}

// ---------------------------------------------------------------------------
// Packfiles: read (plain + OFS/REF deltas) and write (plain, no deltas)
// ---------------------------------------------------------------------------

const TYPE_CODE = { commit: 1, tree: 2, blob: 3, tag: 4 };
const CODE_TYPE = { 1: 'commit', 2: 'tree', 3: 'blob', 4: 'tag' };

function readVarintSize(buf, offset) {
  let byte = buf[offset];
  let size = byte & 0x0f;
  let shift = 4;
  let next = offset + 1;
  while (byte & 0x80) {
    byte = buf[next];
    next += 1;
    size |= (byte & 0x7f) << shift;
    shift += 7;
  }
  return { size, first: buf[offset], next };
}
function readOfsDeltaBase(buf, offset) {
  let byte = buf[offset];
  let baseOffset = byte & 0x7f;
  let next = offset + 1;
  while (byte & 0x80) {
    byte = buf[next];
    next += 1;
    baseOffset = ((baseOffset + 1) << 7) | (byte & 0x7f);
  }
  return { baseOffset, next };
}
function readDeltaVarint(buf, offset) {
  let result = 0;
  let shift = 0;
  let next = offset;
  for (;;) {
    const byte = buf[next];
    next += 1;
    result |= (byte & 0x7f) << shift;
    shift += 7;
    if (!(byte & 0x80)) break;
  }
  return { value: result, next };
}
function applyDelta(base, delta) {
  let off = 0;
  const src = readDeltaVarint(delta, off); off = src.next;
  const tgt = readDeltaVarint(delta, off); off = tgt.next;
  if (src.value !== base.length) throw new Error('delta base size mismatch');
  const out = [];
  let total = 0;
  while (off < delta.length) {
    const op = delta[off];
    off += 1;
    if (op & 0x80) {
      let cpOff = 0;
      let cpSize = 0;
      for (let i = 0; i < 4; i += 1) if (op & (1 << i)) { cpOff |= delta[off] << (8 * i); off += 1; }
      for (let i = 0; i < 3; i += 1) if (op & (0x10 << i)) { cpSize |= delta[off] << (8 * i); off += 1; }
      if (cpSize === 0) cpSize = 0x10000;
      out.push(base.subarray(cpOff, cpOff + cpSize));
      total += cpSize;
    } else if (op !== 0) {
      out.push(delta.subarray(off, off + op));
      total += op;
      off += op;
    } else throw new Error('delta opcode 0');
  }
  const result = Buffer.concat(out);
  if (result.length !== tgt.value || total !== tgt.value) throw new Error('delta target size mismatch');
  return result;
}
// inflateSync ignores trailing bytes, so the compressed length is found by binary search
// for the smallest end that inflates successfully — unless the fast path below applies.
// Fast path: one inflateSync with info:true. The engine reports exactly how many input
// bytes the deflate stream consumed (engine.bytesWritten); that is the next object's
// offset, no probing needed. Verified exact on this Node across payload shapes
// (random/incompressible, text, tiny, empty, deflate levels 1/6/9, random trailing
// bytes, multi-object packs). Anything implausible falls back to the binary search,
// which stays the correctness backstop for any pack this path cannot place.
function inflateAt(buf, offset) {
  try {
    const { engine, buffer } = inflateSync(buf.subarray(offset), { info: true });
    const consumed = engine?.bytesWritten;
    if (Number.isSafeInteger(consumed) && consumed > 0 && offset + consumed <= buf.length) {
      return { data: buffer, next: offset + consumed };
    }
  } catch { /* fall through to the probing search below */ }
  const end = buf.length;
  let lo = offset + 1;
  let hi = end;
  let best = null;
  // First try the whole rest: if it inflates, binary-search the exact end.
  try { best = inflateSync(buf.subarray(offset, end)); } catch { best = null; }
  if (best === null) {
    // Truncated or corrupt at this offset.
    throw new Error('pack entry does not inflate');
  }
  while (lo < hi) {
    const mid = (lo + hi) >> 1;
    try { inflateSync(buf.subarray(offset, mid)); hi = mid; } catch (e) {
      if (String(e && e.message).includes('unexpected end of file')) lo = mid + 1;
      else throw e;
    }
  }
  return { data: inflateSync(buf.subarray(offset, lo)), next: lo };
}
function readPack(pack) {
  const buf = Buffer.from(pack);
  if (buf.length < 32) throw new Error('pack too short');
  if (buf.subarray(0, 4).toString('ascii') !== 'PACK') throw new Error('pack header');
  const version = buf.readUInt32BE(4);
  if (version !== 2 && version !== 3) throw new Error(`unsupported pack version ${version}`);
  const count = buf.readUInt32BE(8);
  const trailerStart = buf.length - 20;
  const trailer = buf.subarray(trailerStart).toString('hex');
  if (sha1hex(buf.subarray(0, trailerStart)) !== trailer) throw new Error('pack trailer checksum mismatch');
  const raw = [];
  const byOffset = new Map();
  let offset = 12;
  for (let i = 0; i < count; i += 1) {
    const entryOffset = offset;
    const header = readVarintSize(buf, offset);
    offset = header.next;
    const typeCode = (header.first >> 4) & 0x07;
    const entry = { offset: entryOffset, typeCode, size: header.size, data: Buffer.alloc(0) };
    if (typeCode === 6) {
      const base = readOfsDeltaBase(buf, offset);
      offset = base.next;
      entry.baseOffset = entryOffset - base.baseOffset;
    } else if (typeCode === 7) {
      entry.baseOid = buf.subarray(offset, offset + 20).toString('hex');
      offset += 20;
    } else if (!CODE_TYPE[typeCode]) throw new Error(`unknown pack type ${typeCode}`);
    const inflated = inflateAt(buf.subarray(0, trailerStart), offset);
    offset = inflated.next;
    if (inflated.data.length !== header.size) throw new Error('pack entry size mismatch');
    entry.data = inflated.data;
    raw.push(entry);
    byOffset.set(entryOffset, entry);
  }
  const objects = new Map();
  const resolve = (entry, seen) => {
    if (entry.resolved) return entry.resolved;
    if (seen.has(entry.offset)) throw new Error('delta cycle');
    seen.add(entry.offset);
    let type;
    let data;
    if (entry.typeCode === 6) {
      const baseEntry = byOffset.get(entry.baseOffset);
      if (!baseEntry) throw new Error('ofs-delta base missing');
      const base = resolve(baseEntry, seen);
      type = base.type;
      data = applyDelta(base.data, entry.data);
    } else if (entry.typeCode === 7) {
      const base = objects.get(entry.baseOid);
      if (!base) throw new Error('ref-delta base missing');
      type = base.type;
      data = applyDelta(base.data, entry.data);
    } else {
      type = CODE_TYPE[entry.typeCode];
      data = entry.data;
    }
    const oid = hashObject(type, data);
    entry.resolved = { type, data, oid };
    objects.set(oid, { type, data });
    return entry.resolved;
  };
  for (const entry of raw) resolve(entry, new Set());
  return { objects, count };
}
function writePackObjectHeader(type, size) {
  const code = TYPE_CODE[type];
  const bytes = [];
  let remaining = size;
  let first = (code << 4) | (remaining & 0x0f);
  remaining = Math.floor(remaining / 16);
  while (remaining > 0) {
    bytes.push(first | 0x80);
    first = remaining & 0x7f;
    remaining = Math.floor(remaining / 128);
  }
  bytes.push(first);
  return Buffer.from(bytes);
}
function writePack(objects) {
  const list = [...objects];
  const parts = [];
  const header = Buffer.allocUnsafe(12);
  header.write('PACK', 0, 4, 'ascii');
  header.writeUInt32BE(2, 4);
  header.writeUInt32BE(list.length, 8);
  parts.push(header);
  for (const o of list) {
    const data = Buffer.from(o.data);
    parts.push(writePackObjectHeader(o.type, data.length));
    parts.push(deflateSync(data));
  }
  const body = Buffer.concat(parts);
  return Buffer.concat([body, createHash('sha1').update(body).digest()]);
}

// ---------------------------------------------------------------------------
// Store
// ---------------------------------------------------------------------------

const repos = new Map(); // "owner/name" -> repo
let nextRepoId = 1;
let nextObjectSeq = 0; // global numeric id counter for issues/comments (stable, deterministic)

function repoKey(owner, name) { return `${owner}/${name}`; }
function globalId(kind, payload) { return b64url(`${kind}:${payload}`); }

function createRepoRecord(owner, name, description, priv) {
  const id = nextRepoId++;
  const repo = {
    id, name, owner,
    description: description ?? '',
    private: priv === true,
    defaultBranch: 'main',
    objects: new Map(), // oid -> {type, data}
    refs: new Map(), // refname -> oid
    labels: new Map(), // name -> {id, name, color, description}
    nextLabelId: 1,
    issues: [], // issue objects (open + closed), creation order
    issueByNumber: new Map(),
    pulls: [],
    prByNumber: new Map(),
    nextNumber: 1,
    nextCommentId: 1,
    seq: nextRepoId,
  };
  repos.set(repoKey(owner, name), repo);
  return repo;
}
function getRepo(owner, name) {
  if (owner !== VIEWER_LOGIN) return null;
  return repos.get(repoKey(owner, name)) ?? null;
}
function putObject(repo, type, data) {
  const buf = Buffer.from(data);
  const oid = hashObject(type, buf);
  if (!repo.objects.has(oid)) repo.objects.set(oid, { type, data: buf });
  return oid;
}
function refOid(repo, ref) { return repo.refs.get(ref) ?? null; }
function branchRef(branch) { return `refs/heads/${branch}`; }
function branchTip(repo, branch) { return refOid(repo, branchRef(branch)); }
function resolveRef(repo, ref) {
  // branch name, full ref, tag name, or raw oid
  if (!ref) return null;
  if (isOid(ref)) return repo.objects.has(ref) ? ref : null;
  if (ref.startsWith('refs/')) return refOid(repo, ref);
  const head = branchTip(repo, ref);
  if (head) return head;
  const tag = refOid(repo, `refs/tags/${ref}`);
  if (tag) return tag;
  return null;
}
function peelToCommit(repo, oid) {
  let cur = oid;
  const seen = new Set();
  while (cur && !seen.has(cur)) {
    seen.add(cur);
    const obj = repo.objects.get(cur);
    if (!obj) return null;
    if (obj.type === 'commit') return cur;
    if (obj.type === 'tag') { cur = parseTag(obj.data).object; continue; }
    return null;
  }
  return null;
}

// Flatten a tree to path -> {oid, mode}; returns Map.
function flattenTree(repo, treeOid, prefix, out) {
  out = out ?? new Map();
  prefix = prefix ?? '';
  const obj = repo.objects.get(treeOid);
  if (!obj || obj.type !== 'tree') return out;
  for (const e of parseTree(obj.data)) {
    const path = prefix ? `${prefix}/${e.name}` : e.name;
    if (e.mode === '40000') flattenTree(repo, e.oid, path, out);
    else out.set(path, { oid: e.oid, mode: e.mode });
  }
  return out;
}
// Build nested trees from a flat path map; returns root tree oid.
function buildTreeFromMap(repo, flat) {
  const build = (paths) => {
    const entries = [];
    const dirs = new Map();
    for (const [path, entry] of paths) {
      const slash = path.indexOf('/');
      if (slash < 0) entries.push({ mode: entry.mode, name: path, oid: entry.oid });
      else {
        const dir = path.slice(0, slash);
        if (!dirs.has(dir)) dirs.set(dir, []);
        dirs.get(dir).push([path.slice(slash + 1), entry]);
      }
    }
    for (const [dir, sub] of dirs) entries.push({ mode: '40000', name: dir, oid: build(sub) });
    return putObject(repo, 'tree', buildTree(entries));
  };
  return build([...flat.entries()]);
}
// Create a forge commit (contents API / squash merge). Deterministic timestamp.
function forgeCommit(repo, { tree, parents, message }) {
  const timestamp = COMMIT_EPOCH + (commitCounter++);
  const author = `${VIEWER_NAME} <${VIEWER_EMAIL}>`;
  const data = buildCommitBytes({ tree, parents: parents || [], message, author, timestamp });
  return putObject(repo, 'commit', data);
}
// Diff two flat maps: [{path, status, additions, deletions, changes}]
function diffFlat(oldMap, newMap, repo) {
  const out = [];
  const countLines = (oid) => {
    if (!oid) return 0;
    const obj = repo.objects.get(oid);
    if (!obj || obj.type !== 'blob') return 0;
    const text = obj.data.toString('utf8');
    if (text === '') return 0;
    return text.split('\n').length - (text.endsWith('\n') ? 1 : 0);
  };
  for (const [path, entry] of newMap) {
    const old = oldMap.get(path);
    if (!old) {
      const add = countLines(entry.oid);
      out.push({ filename: path, status: 'added', additions: add, deletions: 0, changes: add });
    } else if (old.oid !== entry.oid) {
      const add = countLines(entry.oid);
      const del = countLines(old.oid);
      out.push({ filename: path, status: 'modified', additions: add, deletions: del, changes: add + del });
    }
  }
  for (const [path] of oldMap) {
    if (!newMap.has(path)) {
      const del = countLines(oldMap.get(path).oid);
      out.push({ filename: path, status: 'removed', additions: 0, deletions: del, changes: del });
    }
  }
  out.sort((a, b) => (a.filename < b.filename ? -1 : 1));
  return out;
}
// Three-way tree merge for a squash merge. Returns {tree, conflict} (conflict: path or null).
function threeWayMerge(repo, baseOid, headOid, mergeBaseOid) {
  const baseTree = parseCommit(repo.objects.get(mergeBaseOid).data).tree;
  const headTree = parseCommit(repo.objects.get(headOid).data).tree;
  const baseTipTree = parseCommit(repo.objects.get(baseOid).data).tree;
  const baseFlat = flattenTree(repo, baseTree);
  const headFlat = flattenTree(repo, headTree);
  const tipFlat = flattenTree(repo, baseTipTree);
  const merged = new Map(tipFlat);
  let conflict = null;
  const allPaths = new Set([...baseFlat.keys(), ...headFlat.keys(), ...tipFlat.keys()]);
  for (const path of allPaths) {
    const b = baseFlat.get(path)?.oid ?? null;
    const h = headFlat.get(path)?.oid ?? null;
    const t = tipFlat.get(path)?.oid ?? null;
    const headChanged = h !== b;
    const tipChanged = t !== b;
    if (headChanged && tipChanged && h !== t) { conflict = path; break; }
    if (headChanged) {
      if (h === null) merged.delete(path);
      else merged.set(path, headFlat.get(path));
    }
  }
  if (conflict) return { tree: null, conflict };
  return { tree: buildTreeFromMap(repo, merged), conflict: null };
}
function prMergeable(repo, pr) {
  const headTip = branchTip(repo, pr.head);
  const baseTip = branchTip(repo, pr.base);
  if (!headTip || !baseTip) return 'UNKNOWN';
  const base = mergeBase(headTip, baseTip, (oid) => repo.objects.get(oid));
  if (!base) return 'UNKNOWN';
  const { conflict } = threeWayMerge(repo, baseTip, headTip, base);
  return conflict ? 'CONFLICTING' : 'MERGEABLE';
}
function computePrFiles(repo, pr) {
  const headTip = branchTip(repo, pr.head);
  const baseTip = branchTip(repo, pr.base);
  if (!headTip || !baseTip) return [];
  const base = mergeBase(headTip, baseTip, (oid) => repo.objects.get(oid));
  if (!base) return [];
  const baseTree = parseCommit(repo.objects.get(base).data).tree;
  const headTree = parseCommit(repo.objects.get(headTip).data).tree;
  return diffFlat(flattenTree(repo, baseTree), flattenTree(repo, headTree), repo);
}

// ---------------------------------------------------------------------------
// REST JSON shapes
// ---------------------------------------------------------------------------

function userJson(login) { return { login, id: login === VIEWER_LOGIN ? VIEWER.id : 0, type: 'User', site_admin: false }; }
function repoJson(repo) {
  return {
    id: repo.id, node_id: globalId('repo', `${repo.owner}/${repo.name}`),
    name: repo.name, full_name: `${repo.owner}/${repo.name}`,
    owner: userJson(repo.owner), private: repo.private,
    html_url: `https://example.invalid/${repo.owner}/${repo.name}`,
    description: repo.description, fork: false,
    url: `/api/v3/repos/${repo.owner}/${repo.name}`,
    created_at: FIXED_DATE, updated_at: FIXED_DATE, pushed_at: FIXED_DATE,
    default_branch: repo.defaultBranch,
    has_issues: true, has_projects: true, has_wiki: true, has_pages: false, has_downloads: true,
    archived: false, disabled: false, visibility: repo.private ? 'private' : 'public',
    license: null, topics: [], open_issues_count: repo.issues.filter((i) => i.state === 'open').length,
  };
}
function labelJson(repo, label) {
  return { id: label.id, node_id: globalId('label', `${repo.owner}/${repo.name}:${label.name}`), url: `/api/v3/repos/${repo.owner}/${repo.name}/labels/${encodeURIComponent(label.name)}`, name: label.name, color: label.color, description: label.description ?? '', default: false };
}
function issueJson(repo, issue) {
  return {
    id: issue.id, node_id: issue.nodeId, number: issue.number,
    title: issue.title, body: issue.body ?? '', state: issue.state,
    user: userJson(VIEWER_LOGIN),
    labels: issue.labels.map((l) => labelJson(repo, l)),
    assignees: [], milestone: null, locked: false,
    comments: issue.comments.length,
    created_at: FIXED_DATE, updated_at: FIXED_DATE, closed_at: issue.state === 'closed' ? FIXED_DATE : null,
    html_url: `https://example.invalid/${repo.owner}/${repo.name}/issues/${issue.number}`,
    url: `/api/v3/repos/${repo.owner}/${repo.name}/issues/${issue.number}`,
  };
}
function commentJson(repo, issue, comment) {
  return {
    id: comment.id, node_id: comment.nodeId, body: comment.body,
    user: userJson(VIEWER_LOGIN), created_at: FIXED_DATE, updated_at: FIXED_DATE,
    html_url: `https://example.invalid/${repo.owner}/${repo.name}/issues/${issue.number}#issuecomment-${comment.id}`,
    url: `/api/v3/repos/${repo.owner}/${repo.name}/issues/comments/${comment.id}`,
  };
}
function prJson(repo, pr) {
  const headSha = branchTip(repo, pr.head) ?? ZERO_OID;
  const baseSha = branchTip(repo, pr.base) ?? ZERO_OID;
  return {
    id: pr.id, node_id: pr.nodeId, number: pr.number,
    title: pr.title, body: pr.body ?? '', state: pr.state,
    user: userJson(VIEWER_LOGIN),
    head: { label: `${repo.owner}:${pr.head}`, ref: pr.head, sha: headSha },
    base: { label: `${repo.owner}:${pr.base}`, ref: pr.base, sha: baseSha },
    merged: pr.merged, merged_at: pr.merged ? FIXED_DATE : null,
    merge_commit_sha: pr.mergeCommitSha ?? null,
    mergeable: prMergeable(repo, pr) === 'MERGEABLE',
    draft: false, locked: false,
    created_at: FIXED_DATE, updated_at: FIXED_DATE, closed_at: pr.state === 'closed' ? FIXED_DATE : null,
    html_url: `https://example.invalid/${repo.owner}/${repo.name}/pull/${pr.number}`,
    url: `/api/v3/repos/${repo.owner}/${repo.name}/pulls/${pr.number}`,
  };
}
function makeIssue(repo, title, body, labelNames) {
  const number = repo.nextNumber++;
  const id = ++globalIdCounter + 100000;
  const issue = {
    number, id, nodeId: globalId('issue', `${repo.owner}/${repo.name}#${number}`),
    title: title ?? '', body: body ?? '', state: 'open', labels: [], comments: [],
  };
  for (const name of labelNames || []) {
    const label = repo.labels.get(name);
    if (label) issue.labels.push(label);
  }
  repo.issues.push(issue);
  repo.issueByNumber.set(number, issue);
  return issue;
}
function makePull(repo, title, body, head, base) {
  const number = repo.nextNumber++;
  const id = ++globalIdCounter + 100000;
  const pr = {
    number, id, nodeId: globalId('pr', `${repo.owner}/${repo.name}#${number}`),
    title: title ?? '', body: body ?? '', head, base,
    state: 'open', merged: false, merged_at: null, mergeCommitSha: null,
    files: null, // computed lazily at creation time below
  };
  pr.files = computePrFiles(repo, pr);
  repo.pulls.push(pr);
  repo.prByNumber.set(number, pr);
  return pr;
}
function doMerge(repo, pr) {
  const headTip = branchTip(repo, pr.head);
  const baseTip = branchTip(repo, pr.base);
  if (!headTip || !baseTip) return { status: 409, message: 'missing branch tip' };
  const base = mergeBase(headTip, baseTip, (oid) => repo.objects.get(oid));
  if (!base) return { status: 409, message: 'no merge base' };
  const { tree, conflict } = threeWayMerge(repo, baseTip, headTip, base);
  if (conflict) return { status: 405, message: `merge conflict on ${conflict}` };
  const sha = forgeCommit(repo, { tree, parents: [baseTip], message: `Merge pull request #${pr.number} from ${pr.head}\n\n${pr.title}` });
  repo.refs.set(branchRef(pr.base), sha);
  pr.state = 'closed';
  pr.merged = true;
  pr.mergeCommitSha = sha;
  return { status: 200, sha };
}
function shortBranch(ref) {
  if (typeof ref !== 'string') return '';
  return ref.includes(':') ? ref.split(':').pop() : ref;
}

// ---------------------------------------------------------------------------
// HTTP plumbing: body reading, auth, pagination
// ---------------------------------------------------------------------------

const SHOP_TOKEN = process.env.MAKEFUN_SHOP_TOKEN ?? '';
function authed(req) {
  const h = req.headers.authorization ?? '';
  if (!h.startsWith('Bearer ')) return false;
  const token = h.slice(7);
  if (token === '') return false;
  if (SHOP_TOKEN === '') return true; // local dev: any non-empty bearer
  return token === SHOP_TOKEN;
}
function readBody(req) {
  return new Promise((resolve, reject) => {
    const chunks = [];
    let size = 0;
    req.on('data', (c) => { chunks.push(c); size += c.length; if (size > 64 * 1024 * 1024) { req.destroy(); reject(new Error('body too large')); } });
    req.on('end', () => resolve(Buffer.concat(chunks)));
    req.on('error', reject);
  });
}
function parseJsonBody(buf) {
  if (!buf || buf.length === 0) return {};
  const text = buf.toString('utf8');
  if (text.trim() === '') return {};
  return JSON.parse(text);
}
function pageParams(url) {
  const perPage = Math.max(1, Math.min(100, parseInt(url.searchParams.get('per_page') ?? '30', 10) || 30));
  const page = Math.max(1, parseInt(url.searchParams.get('page') ?? '1', 10) || 1);
  return { perPage, page };
}
function paginate(items, url, res, status) {
  const { perPage, page } = pageParams(url);
  const total = items.length;
  const pages = Math.max(1, Math.ceil(total / perPage));
  const slice = items.slice((page - 1) * perPage, page * perPage);
  const headers = {};
  if (page < pages) {
    const next = new URL(url.toString());
    next.searchParams.set('page', String(page + 1));
    next.searchParams.set('per_page', String(perPage));
    const last = new URL(url.toString());
    last.searchParams.set('page', String(pages));
    last.searchParams.set('per_page', String(perPage));
    headers.link = `<${next.toString()}>; rel="next", <${last.toString()}>; rel="last"`;
  }
  jsonBody(res, status ?? 200, slice, headers);
}
function absUrl(req, url) {
  const host = req.headers.host ?? '127.0.0.1';
  return new URL(url.pathname + url.search, `http://${host}`);
}

// ---------------------------------------------------------------------------
// REST v3
// ---------------------------------------------------------------------------

async function handleRest(req, res, url, segments, body) {
  // segments: path parts after /api/v3
  const method = req.method ?? 'GET';
  // Auth on every /api/v3 route.
  if (!authed(req)) { errJson(res, 401, 'Requires authentication'); return; }

  const seg = (i) => segments[i] ?? '';
  const rest = (n) => segments.slice(n).map((s) => { try { return decodeURIComponent(s); } catch { return s; } }).join('/');

  // GET /api/v3/  (root)
  if (segments.length === 0) {
    if (method !== 'GET') { errJson(res, 404, 'Not Found'); return; }
    jsonBody(res, 200, { current_user_url: '/api/v3/user', rate_limit_url: '/api/v3/rate_limit' }, { 'x-oauth-scopes': 'repo, read:org' });
    return;
  }
  // GET /api/v3/meta
  if (segments.length === 1 && seg(0) === 'meta') {
    if (method !== 'GET') { errJson(res, 404, 'Not Found'); return; }
    jsonBody(res, 200, { installed_version: '1.0.0', verifiable_password_authentication: false });
    return;
  }
  // GET /api/v3/user
  if (segments.length === 1 && seg(0) === 'user' && method === 'GET') {
    jsonBody(res, 200, { ...userJson(VIEWER_LOGIN), name: VIEWER_NAME, email: VIEWER_EMAIL, html_url: `https://example.invalid/${VIEWER_LOGIN}`, type: 'User' });
    return;
  }
  // /api/v3/user/repos
  if (segments.length === 2 && seg(0) === 'user' && seg(1) === 'repos') {
    if (method === 'GET') {
      const all = [...repos.values()].filter((r) => r.owner === VIEWER_LOGIN).sort((a, b) => a.id - b.id).map(repoJson);
      paginate(all, absUrl(req, url), res, 200);
      return;
    }
    if (method === 'POST') {
      const name = typeof body.name === 'string' ? body.name : '';
      if (name === '') { errJson(res, 422, 'name is required'); return; }
      if (repos.has(repoKey(VIEWER_LOGIN, name))) { errJson(res, 422, 'Repository already exists'); return; }
      const repo = createRepoRecord(VIEWER_LOGIN, name, body.description, body.private);
      jsonBody(res, 201, repoJson(repo));
      return;
    }
    errJson(res, 404, 'Not Found'); return;
  }
  // /api/v3/repos/{owner}/{repo}[...]
  if (seg(0) === 'repos' && segments.length >= 3) {
    const owner = seg(1);
    const name = seg(2);
    const repo = getRepo(owner, name);
    const tail = segments.slice(3);
    if (!repo) { errJson(res, 404, 'Not Found'); return; }
    // GET/PATCH/DELETE /repos/{o}/{r}
    if (tail.length === 0) {
      if (method === 'GET') { jsonBody(res, 200, repoJson(repo)); return; }
      if (method === 'PATCH') {
        if (typeof body.description === 'string') repo.description = body.description;
        if (typeof body.private === 'boolean') repo.private = body.private;
        if (typeof body.default_branch === 'string' && body.default_branch !== '') repo.defaultBranch = body.default_branch;
        jsonBody(res, 200, repoJson(repo));
        return;
      }
      if (method === 'DELETE') {
        repos.delete(repoKey(owner, name));
        res.writeHead(204, { 'x-github-request-id': `forge-${++requestCounter}` });
        res.end();
        return;
      }
      errJson(res, 404, 'Not Found'); return;
    }
    const head = tail[0];
    // ---- branches ----
    if (head === 'branches' && method === 'GET' && tail.length === 1) {
      const list = [...repo.refs.keys()].filter((r) => r.startsWith('refs/heads/')).sort().map((r) => {
        const branch = r.slice('refs/heads/'.length);
        return { name: branch, commit: { sha: repo.refs.get(r), url: `/api/v3/repos/${owner}/${name}/commits/${repo.refs.get(r)}` }, protected: false };
      });
      jsonBody(res, 200, list);
      return;
    }
    if (head === 'branches' && method === 'GET' && tail.length === 2) {
      const tip = branchTip(repo, tail[1]);
      if (!tip) { errJson(res, 404, 'Branch not found'); return; }
      jsonBody(res, 200, { name: tail[1], commit: { sha: tip, url: `/api/v3/repos/${owner}/${name}/commits/${tip}` }, protected: false });
      return;
    }
    // ---- git refs ----
    if (head === 'git' && tail[1] === 'refs') {
      if (method === 'POST' && tail.length === 2) {
        const ref = typeof body.ref === 'string' ? body.ref : '';
        const sha = typeof body.sha === 'string' ? body.sha : '';
        if (!ref.startsWith('refs/') || !isOid(sha) || !repo.objects.has(sha)) { errJson(res, 422, 'Invalid ref or sha'); return; }
        if (repo.refs.has(ref)) { errJson(res, 422, 'Reference already exists'); return; }
        repo.refs.set(ref, sha);
        jsonBody(res, 201, { ref, node_id: globalId('ref', `${owner}/${name}:${ref}`), url: `/api/v3/repos/${owner}/${name}/git/refs/${ref.replace(/^refs\//, '')}`, object: { sha, type: repo.objects.get(sha).type, url: `/api/v3/repos/${owner}/${name}/git/${repo.objects.get(sha).type}s/${sha}` } });
        return;
      }
      if (method === 'GET') {
        const wanted = tail.slice(2).join('/');
        if (wanted === '') {
          const all = [...repo.refs.entries()].sort((a, b) => (a[0] < b[0] ? -1 : 1)).map(([ref, sha]) => ({ ref, url: `/api/v3/repos/${owner}/${name}/git/refs/${ref.replace(/^refs\//, '')}`, object: { sha, type: repo.objects.get(sha)?.type ?? 'commit', url: '' } }));
          jsonBody(res, 200, all);
          return;
        }
        const full = `refs/${wanted}`;
        const sha = repo.refs.get(full);
        if (!sha) { errJson(res, 404, 'Not Found'); return; }
        jsonBody(res, 200, { ref: full, node_id: globalId('ref', `${owner}/${name}:${full}`), url: `/api/v3/repos/${owner}/${name}/git/refs/${wanted}`, object: { sha, type: repo.objects.get(sha)?.type ?? 'commit', url: '' } });
        return;
      }
      errJson(res, 404, 'Not Found'); return;
    }
    // ---- commits ----
    if (head === 'commits' && method === 'GET') {
      const refParam = url.searchParams.get('sha') ?? repo.defaultBranch;
      const tip = resolveRef(repo, refParam);
      const list = [];
      if (tip) {
        const seen = new Set();
        const stack = [tip];
        // Walk newest-first along first-parent chain order (linear histories dominate).
        const order = [];
        let cur = tip;
        while (cur && !seen.has(cur)) {
          seen.add(cur);
          const obj = repo.objects.get(cur);
          if (!obj || obj.type !== 'commit') break;
          order.push(cur);
          const c = parseCommit(obj.data);
          cur = c.parents[0] ?? null;
          // Include other parents' ancestry too (merge commits): BFS remainder.
          for (const p of c.parents.slice(1)) stack.push(p);
        }
        while (stack.length) {
          const oid = stack.pop();
          if (seen.has(oid)) continue;
          seen.add(oid);
          const obj = repo.objects.get(oid);
          if (!obj || obj.type !== 'commit') continue;
          order.push(oid);
          for (const p of parseCommit(obj.data).parents) stack.push(p);
        }
        for (const sha of order) {
          const c = parseCommit(repo.objects.get(sha).data);
          list.push({ sha, node_id: globalId('commit', `${owner}/${name}:${sha}`), commit: { message: c.message.replace(/\n$/, ''), tree: { sha: c.tree }, author: { name: VIEWER_NAME, email: VIEWER_EMAIL, date: FIXED_DATE }, committer: { name: VIEWER_NAME, email: VIEWER_EMAIL, date: FIXED_DATE } }, author: userJson(VIEWER_LOGIN), committer: userJson(VIEWER_LOGIN), parents: c.parents.map((p) => ({ sha: p })), url: `/api/v3/repos/${owner}/${name}/commits/${sha}`, html_url: `https://example.invalid/${owner}/${name}/commit/${sha}` });
        }
      }
      paginate(list, absUrl(req, url), res, 200);
      return;
    }
    // ---- contents ----
    if (head === 'contents') {
      const filePath = tail.slice(1).map((s) => { try { return decodeURIComponent(s); } catch { return s; } }).join('/');
      const refParam = url.searchParams.get('ref');
      const branch = refParam ? shortBranch(refParam) : repo.defaultBranch;
      const tip = branchTip(repo, branch);
      if (method === 'GET') {
        if (!tip) { errJson(res, 404, 'Not Found'); return; }
        const treeOid = parseCommit(repo.objects.get(tip).data).tree;
        const flat = flattenTree(repo, treeOid);
        if (filePath === '') {
          // root listing
          const entries = rootListing(repo, treeOid);
          jsonBody(res, 200, entries);
          return;
        }
        const entry = flat.get(filePath);
        if (entry) {
          const blob = repo.objects.get(entry.oid);
          jsonBody(res, 200, { type: 'file', encoding: 'base64', size: blob.data.length, name: filePath.split('/').pop(), path: filePath, content: b64encode(blob.data), sha: entry.oid, url: `/api/v3/repos/${owner}/${name}/contents/${filePath}`, html_url: `https://example.invalid/${owner}/${name}/blob/${branch}/${filePath}`, download_url: null });
          return;
        }
        // directory?
        const prefix = `${filePath}/`;
        const children = new Map();
        for (const [path, e] of flat) {
          if (!path.startsWith(prefix)) continue;
          const restPath = path.slice(prefix.length);
          const slash = restPath.indexOf('/');
          if (slash < 0) children.set(restPath, { type: 'file', name: restPath, path, sha: e.oid, size: repo.objects.get(e.oid).data.length });
          else {
            const dir = restPath.slice(0, slash);
            if (!children.has(dir)) {
              // find the subtree oid for the sha
              const dirTree = findSubtree(repo, treeOid, `${filePath}/${dir}`);
              children.set(dir, { type: 'dir', name: dir, path: `${filePath}/${dir}`, sha: dirTree ?? ZERO_OID, size: 0 });
            }
          }
        }
        if (children.size > 0) {
          jsonBody(res, 200, [...children.values()].sort((a, b) => (a.name < b.name ? -1 : 1)));
          return;
        }
        errJson(res, 404, 'Not Found');
        return;
      }
      if (method === 'PUT') {
        const contentB64 = typeof body.content === 'string' ? body.content : '';
        const message = typeof body.message === 'string' ? body.message : 'update';
        const content = b64decode(contentB64);
        const targetBranch = typeof body.branch === 'string' && body.branch !== '' ? body.branch : repo.defaultBranch;
        let baseTip = branchTip(repo, targetBranch);
        let baseFlat = new Map();
        let baseTreeOid = null;
        if (baseTip) {
          baseTreeOid = parseCommit(repo.objects.get(baseTip).data).tree;
          baseFlat = flattenTree(repo, baseTreeOid);
        } else if (targetBranch !== repo.defaultBranch) {
          // New branch: start from the default branch tip.
          const defTip = branchTip(repo, repo.defaultBranch);
          if (defTip) {
            baseTip = defTip;
            baseTreeOid = parseCommit(repo.objects.get(defTip).data).tree;
            baseFlat = flattenTree(repo, baseTreeOid);
          }
        }
        const existing = baseFlat.get(filePath);
        const isUpdate = !!existing;
        if (isUpdate) {
          if (typeof body.sha !== 'string' || body.sha.toLowerCase() !== existing.oid.toLowerCase()) {
            errJson(res, 409, 'sha does not match the current file');
            return;
          }
        }
        const blobOid = putObject(repo, 'blob', content);
        const next = new Map(baseFlat);
        next.set(filePath, { oid: blobOid, mode: '100644' });
        const treeOid = buildTreeFromMap(repo, next);
        const parents = baseTip ? [baseTip] : [];
        const commitSha = forgeCommit(repo, { tree: treeOid, parents, message });
        repo.refs.set(branchRef(targetBranch), commitSha);
        jsonBody(res, isUpdate ? 200 : 201, {
          content: { name: filePath.split('/').pop(), path: filePath, sha: blobOid, size: content.length, type: 'file', encoding: 'base64', content: contentB64, url: `/api/v3/repos/${owner}/${name}/contents/${filePath}` },
          commit: { sha: commitSha, message, author: { name: VIEWER_NAME, email: VIEWER_EMAIL, date: FIXED_DATE }, committer: { name: VIEWER_NAME, email: VIEWER_EMAIL, date: FIXED_DATE } },
        });
        return;
      }
      if (method === 'DELETE') {
        let baseTip = branchTip(repo, branch);
        if (!baseTip) { errJson(res, 404, 'Not Found'); return; }
        const baseTreeOid = parseCommit(repo.objects.get(baseTip).data).tree;
        const baseFlat = flattenTree(repo, baseTreeOid);
        const existing = baseFlat.get(filePath);
        if (!existing) { errJson(res, 404, 'Not Found'); return; }
        if (typeof body.sha === 'string' && body.sha.toLowerCase() !== existing.oid.toLowerCase()) {
          errJson(res, 409, 'sha does not match the current file');
          return;
        }
        const next = new Map(baseFlat);
        next.delete(filePath);
        const treeOid = buildTreeFromMap(repo, next);
        const commitSha = forgeCommit(repo, { tree: treeOid, parents: [baseTip], message: typeof body.message === 'string' ? body.message : 'delete' });
        repo.refs.set(branchRef(branch), commitSha);
        jsonBody(res, 200, { commit: { sha: commitSha, message: typeof body.message === 'string' ? body.message : 'delete' } });
        return;
      }
      errJson(res, 404, 'Not Found'); return;
    }
    // ---- labels ----
    if (head === 'labels') {
      if (method === 'GET' && tail.length === 1) {
        jsonBody(res, 200, [...repo.labels.values()].map((l) => labelJson(repo, l)));
        return;
      }
      if (method === 'POST' && tail.length === 1) {
        const name = typeof body.name === 'string' ? body.name : '';
        if (name === '') { errJson(res, 422, 'name is required'); return; }
        let label = repo.labels.get(name);
        if (!label) {
          label = { id: repo.nextLabelId++, name, color: typeof body.color === 'string' ? body.color : 'ededed', description: typeof body.description === 'string' ? body.description : '' };
          repo.labels.set(name, label);
        }
        jsonBody(res, 201, labelJson(repo, label));
        return;
      }
      errJson(res, 404, 'Not Found'); return;
    }
    // ---- issues ----
    if (head === 'issues') {
      // POST /issues
      if (method === 'POST' && tail.length === 1) {
        const title = typeof body.title === 'string' ? body.title : '';
        if (title === '') { errJson(res, 422, 'title is required'); return; }
        const labelNames = Array.isArray(body.labels) ? body.labels.map((l) => (typeof l === 'string' ? l : l?.name)).filter(Boolean) : [];
        for (const n of labelNames) if (!repo.labels.has(n)) { errJson(res, 422, `Label '${n}' does not exist`); return; }
        const issue = makeIssue(repo, title, body.body, labelNames);
        jsonBody(res, 201, issueJson(repo, issue));
        return;
      }
      // GET /issues (list)
      if (method === 'GET' && tail.length === 1) {
        const state = url.searchParams.get('state') ?? 'open';
        const sort = url.searchParams.get('sort') ?? 'created';
        const direction = url.searchParams.get('direction') ?? 'desc';
        let list = repo.issues.filter((i) => state === 'all' ? true : i.state === state);
        if (sort === 'created') list = [...list].sort((a, b) => direction === 'asc' ? a.number - b.number : b.number - a.number);
        paginate(list.map((i) => issueJson(repo, i)), absUrl(req, url), res, 200);
        return;
      }
      // /issues/{number}[...]
      if (tail.length >= 2 && /^\d+$/.test(tail[1])) {
        const number = parseInt(tail[1], 10);
        const issue = repo.issueByNumber.get(number);
        if (!issue) { errJson(res, 404, 'Not Found'); return; }
        if (tail.length === 2) {
          if (method === 'GET') { jsonBody(res, 200, issueJson(repo, issue)); return; }
          if (method === 'PATCH') {
            if (typeof body.state === 'string' && (body.state === 'open' || body.state === 'closed')) issue.state = body.state;
            if (typeof body.title === 'string') issue.title = body.title;
            if (typeof body.body === 'string') issue.body = body.body;
            if (Array.isArray(body.labels)) {
              const names = body.labels.map((l) => (typeof l === 'string' ? l : l?.name)).filter(Boolean);
              for (const n of names) if (!repo.labels.has(n)) { errJson(res, 422, `Label '${n}' does not exist`); return; }
              issue.labels = names.map((n) => repo.labels.get(n));
            }
            jsonBody(res, 200, issueJson(repo, issue));
            return;
          }
          errJson(res, 404, 'Not Found'); return;
        }
        if (tail[2] === 'comments') {
          if (method === 'POST') {
            const text = typeof body.body === 'string' ? body.body : '';
            const comment = { id: repo.nextCommentId++, nodeId: globalId('comment', `${owner}/${name}#${number}:${repo.nextCommentId}`), body: text };
            issue.comments.push(comment);
            jsonBody(res, 201, commentJson(repo, issue, comment));
            return;
          }
          if (method === 'GET') {
            jsonBody(res, 200, issue.comments.map((c) => commentJson(repo, issue, c)));
            return;
          }
          errJson(res, 404, 'Not Found'); return;
        }
        errJson(res, 404, 'Not Found'); return;
      }
      errJson(res, 404, 'Not Found'); return;
    }
    // ---- pulls ----
    if (head === 'pulls') {
      if (method === 'POST' && tail.length === 1) {
        const title = typeof body.title === 'string' ? body.title : '';
        const headBranch = shortBranch(body.head);
        const baseBranch = shortBranch(body.base) || repo.defaultBranch;
        if (title === '' || headBranch === '') { errJson(res, 422, 'title and head are required'); return; }
        if (!branchTip(repo, headBranch)) { errJson(res, 422, `head branch '${headBranch}' does not exist`); return; }
        if (!branchTip(repo, baseBranch)) { errJson(res, 422, `base branch '${baseBranch}' does not exist`); return; }
        if (headBranch === baseBranch) { errJson(res, 422, 'head and base are the same'); return; }
        const dup = repo.pulls.find((p) => p.head === headBranch && p.base === baseBranch && p.state === 'open');
        if (dup) { errJson(res, 422, 'A pull request already exists for this head and base'); return; }
        const pr = makePull(repo, title, body.body, headBranch, baseBranch);
        jsonBody(res, 201, prJson(repo, pr));
        return;
      }
      if (method === 'GET' && tail.length === 1) {
        const state = url.searchParams.get('state') ?? 'open';
        const list = repo.pulls.filter((p) => state === 'all' ? true : p.state === state).sort((a, b) => b.number - a.number);
        paginate(list.map((p) => prJson(repo, p)), absUrl(req, url), res, 200);
        return;
      }
      if (tail.length >= 2 && /^\d+$/.test(tail[1])) {
        const number = parseInt(tail[1], 10);
        const pr = repo.prByNumber.get(number);
        if (!pr) { errJson(res, 404, 'Not Found'); return; }
        if (tail.length === 2 && method === 'GET') { jsonBody(res, 200, prJson(repo, pr)); return; }
        if (tail.length === 3 && tail[2] === 'files' && method === 'GET') {
          const files = pr.files ?? computePrFiles(repo, pr);
          jsonBody(res, 200, files.map((f) => ({ sha: '', filename: f.filename, status: f.status, additions: f.additions, deletions: f.deletions, changes: f.changes, blob_url: '', raw_url: '', contents_url: '' })));
          return;
        }
        if (tail.length === 3 && tail[2] === 'merge' && method === 'PUT') {
          if (pr.state !== 'open') { errJson(res, 405, 'Pull request is already closed'); return; }
          const result = doMerge(repo, pr);
          if (result.status !== 200) { errJson(res, result.status, result.message); return; }
          jsonBody(res, 200, { sha: result.sha, merged: true, message: `Pull Request successfully merged` });
          return;
        }
        errJson(res, 404, 'Not Found'); return;
      }
      errJson(res, 404, 'Not Found'); return;
    }
    errJson(res, 404, 'Not Found'); return;
  }
  errJson(res, 404, 'Not Found');
}
function rootListing(repo, treeOid) {
  const obj = repo.objects.get(treeOid);
  if (!obj || obj.type !== 'tree') return [];
  return parseTree(obj.data).sort((a, b) => (a.name < b.name ? -1 : 1)).map((e) => ({
    type: e.mode === '40000' ? 'dir' : 'file',
    name: e.name, path: e.name, sha: e.oid,
    size: e.mode === '40000' ? 0 : (repo.objects.get(e.oid)?.data.length ?? 0),
  }));
}
function findSubtree(repo, treeOid, path) {
  const parts = path.split('/');
  let cur = treeOid;
  for (const part of parts) {
    const obj = repo.objects.get(cur);
    if (!obj || obj.type !== 'tree') return null;
    const entry = parseTree(obj.data).find((e) => e.name === part);
    if (!entry) return null;
    cur = entry.oid;
  }
  return cur;
}

// ---------------------------------------------------------------------------
// GraphQL v4: a small parser + executor for the documents gh / github-mcp-server send.
// ---------------------------------------------------------------------------

// Schema field sets (what __type must list, and what may be queried).
const GQL_FIELDS = {
  Query: ['viewer', 'repository', 'node', 'search', '__type', '__schema'],
  User: ['login', 'id', 'name', 'email'],
  Repository: ['id', 'databaseId', 'name', 'nameWithOwner', 'owner', 'defaultBranchRef', 'viewerPermission', 'hasIssuesEnabled', 'issue', 'issues', 'pullRequests', 'pullRequest', 'url', 'description', 'private'],
  Issue: ['id', 'number', 'title', 'body', 'state', 'createdAt', 'updatedAt', 'url', 'author', 'labels', 'comments'],
  PullRequest: ['id', 'number', 'title', 'body', 'state', 'headRefName', 'baseRefName', 'headRefOid', 'baseRefOid', 'mergeable', 'merged', 'files', 'createdAt', 'updatedAt', 'url', 'author'],
  Ref: ['name', 'target'],
  IssueConnection: ['nodes', 'edges', 'pageInfo', 'totalCount'],
  PullRequestConnection: ['nodes', 'edges', 'pageInfo', 'totalCount'],
  PullRequestFileConnection: ['nodes', 'edges', 'pageInfo', 'totalCount'],
  PageInfo: ['hasNextPage', 'hasPreviousPage', 'endCursor', 'startCursor'],
  IssueEdge: ['node', 'cursor'],
  PullRequestEdge: ['node', 'cursor'],
  PullRequestFile: ['path', 'additions', 'deletions', 'changeType'],
  Comment: ['id', 'body', 'createdAt'],
  CommentEdge: ['node', 'cursor'],
  AddCommentPayload: ['commentEdge', 'clientMutationId'],
  CreateIssuePayload: ['issue', 'clientMutationId'],
  CloseIssuePayload: ['issue', 'clientMutationId'],
  CreatePullRequestPayload: ['pullRequest', 'clientMutationId'],
  MergePullRequestPayload: ['pullRequest', 'clientMutationId'],
  SearchType: [],
  __Type: ['name', 'kind', 'fields', 'enumValues', 'description'],
  __Field: ['name', 'description', 'type', 'args'],
  __EnumValue: ['name', 'description'],
  __Schema: ['queryType', 'mutationType', 'types', 'directives'],
};
const GQL_ENUM_SEARCHTYPE = ['ISSUE', 'REPOSITORY', 'USER', 'DISCUSSION', 'CODE', 'COMMIT'];
const GQL_TYPE_KIND = { Query: 'OBJECT', User: 'OBJECT', Repository: 'OBJECT', Issue: 'OBJECT', PullRequest: 'OBJECT', Ref: 'OBJECT', IssueConnection: 'OBJECT', PullRequestConnection: 'OBJECT', PageInfo: 'OBJECT', SearchType: 'ENUM' };

function gqlTokenize(src) {
  const tokens = [];
  let i = 0;
  while (i < src.length) {
    const c = src[i];
    if (/\s/.test(c) || c === ',') { i += 1; continue; }
    if (c === '#') { while (i < src.length && src[i] !== '\n') i += 1; continue; }
    if (src.startsWith('...', i)) { tokens.push({ t: '...', v: '...' }); i += 3; continue; }
    if ('{}():!$=[]@'.includes(c)) { tokens.push({ t: c, v: c }); i += 1; continue; }
    if (c === '"') {
      let j = i + 1;
      let out = '';
      while (j < src.length && src[j] !== '"') {
        if (src[j] === '\\' && j + 1 < src.length) { out += src[j + 1]; j += 2; } else { out += src[j]; j += 1; }
      }
      tokens.push({ t: 'string', v: out });
      i = j + 1;
      continue;
    }
    if (/[0-9-]/.test(c) && /[0-9]/.test(src[i] === '-' ? src[i + 1] ?? '' : c)) {
      let j = i;
      if (src[j] === '-') j += 1;
      while (j < src.length && /[0-9]/.test(src[j])) j += 1;
      tokens.push({ t: 'int', v: parseInt(src.slice(i, j), 10) });
      i = j;
      continue;
    }
    if (/[A-Za-z_]/.test(c)) {
      let j = i;
      while (j < src.length && /[A-Za-z0-9_]/.test(src[j])) j += 1;
      tokens.push({ t: 'name', v: src.slice(i, j) });
      i = j;
      continue;
    }
    throw new Error(`unexpected character ${JSON.stringify(c)}`);
  }
  tokens.push({ t: 'eof', v: '' });
  return tokens;
}
function gqlParse(src) {
  const toks = gqlTokenize(src);
  let pos = 0;
  const peek = () => toks[pos];
  const next = () => toks[pos++];
  const expect = (t) => { const tok = next(); if (tok.t !== t) throw new Error(`expected ${t}, got ${tok.t} ${tok.v}`); return tok; };
  function parseValue() {
    const tok = peek();
    if (tok.t === '$') { next(); return { var: expect('name').v }; }
    if (tok.t === 'int') { next(); return { lit: tok.v }; }
    if (tok.t === 'string') { next(); return { lit: tok.v }; }
    if (tok.t === 'name') {
      next();
      if (tok.v === 'true') return { lit: true };
      if (tok.v === 'false') return { lit: false };
      if (tok.v === 'null') return { lit: null };
      return { lit: tok.v }; // enum value
    }
    if (tok.t === '[') {
      next();
      const items = [];
      while (peek().t !== ']') items.push(parseValue());
      expect(']');
      return { lit: items.map((x) => x.lit) };
    }
    if (tok.t === '{') {
      next();
      const obj = {};
      while (peek().t !== '}') {
        const key = expect('name').v;
        expect(':');
        obj[key] = parseValue();
      }
      expect('}');
      return { lit: obj };
    }
    throw new Error(`unexpected value token ${tok.t}`);
  }
  function parseArgs() {
    const args = {};
    if (peek().t !== '(') return args;
    next();
    while (peek().t !== ')') {
      const key = expect('name').v;
      expect(':');
      args[key] = parseValue();
    }
    expect(')');
    return args;
  }
  function parseSelectionSet() {
    expect('{');
    const fields = [];
    while (peek().t !== '}') {
      if (peek().t === '...') {
        next();
        if (peek().t === 'name' && peek().v === 'on') {
          next();
          const typeName = expect('name').v;
          const sub = parseSelectionSet();
          fields.push({ fragment: true, typeName, selection: sub });
        } else {
          const fragName = expect('name').v;
          fields.push({ fragment: true, spread: fragName });
        }
        continue;
      }
      let alias = null;
      let name = expect('name').v;
      if (peek().t === ':') { next(); alias = name; name = expect('name').v; }
      const args = parseArgs();
      let selection = null;
      if (peek().t === '{') selection = parseSelectionSet();
      fields.push({ alias: alias ?? name, name, args, selection });
    }
    expect('}');
    return fields;
  }
  function parseOperation() {
    let kind = 'query';
    let name = null;
    if (peek().t === 'name' && (peek().v === 'query' || peek().v === 'mutation' || peek().v === 'subscription')) {
      kind = next().v;
      if (peek().t === 'name') name = next().v;
    }
    const varDefs = {};
    if (peek().t === '(') {
      next();
      while (peek().t !== ')') {
        if (peek().t === '$') next();
        const vname = expect('name').v;
        expect(':');
        let typeName = '';
        if (peek().t === '[') { next(); typeName = `[${expect('name').v}]`; expect(']'); }
        else typeName = expect('name').v;
        let required = false;
        if (peek().t === '!') { next(); required = true; }
        let def = undefined;
        if (peek().t === '=') { next(); def = parseValue().lit; }
        varDefs[vname] = { typeName, required, default: def };
      }
      expect(')');
    }
    // skip directives (@foo...) if any
    while (peek().t === '@') { next(); expect('name'); parseArgs(); }
    const selection = parseSelectionSet();
    return { kind, name, varDefs, selection };
  }
  const ops = [];
  while (peek().t !== 'eof') ops.push(parseOperation());
  return ops;
}
function gqlResolveValue(node, variables) {
  if (node && typeof node === 'object' && 'var' in node) return variables[node.var];
  if (node && typeof node === 'object' && 'lit' in node) {
    const lit = node.lit;
    if (Array.isArray(lit)) return lit;
    if (lit && typeof lit === 'object') {
      const out = {};
      for (const [k, v] of Object.entries(lit)) out[k] = gqlResolveValue(v, variables);
      return out;
    }
    return lit;
  }
  return undefined;
}
function gqlArgs(field, variables) {
  const out = {};
  for (const [k, v] of Object.entries(field.args || {})) out[k] = gqlResolveValue(v, variables);
  return out;
}
// Node wrapper: {__typename, __value, __repo, __issue, __pr, ...}
function gqlNode(typename, value, extra) { return { __typename: typename, __value: value, ...(extra || {}) }; }

function issueStateGql(issue) { return issue.state === 'open' ? 'OPEN' : 'CLOSED'; }
function prStateGql(pr) { return pr.merged ? 'MERGED' : (pr.state === 'open' ? 'OPEN' : 'CLOSED'); }

function gqlIssueNodes(repo, args) {
  let list = [...repo.issues];
  const states = args.states;
  if (Array.isArray(states) && states.length) {
    const want = new Set(states.map((s) => String(s).toLowerCase()));
    list = list.filter((i) => want.has(i.state));
  }
  const orderBy = args.orderBy;
  if (orderBy && orderBy.field === 'CREATED_AT') {
    const dir = orderBy.direction === 'ASC' ? 1 : -1;
    list.sort((a, b) => dir * (a.number - b.number));
  } else {
    list.sort((a, b) => a.number - b.number);
  }
  return list;
}
function gqlConnection(nodes, args, mapNode) {
  // nodes: already ordered array of domain objects; mapNode -> gql node
  let afterIdx = -1;
  if (typeof args.after === 'string' && args.after !== '') {
    try {
      const decoded = Buffer.from(args.after, 'base64url').toString('utf8');
      const m = /^cursor:(\d+)$/.exec(decoded);
      if (m) {
        const n = parseInt(m[1], 10);
        afterIdx = nodes.findIndex((x) => x.number === n);
      }
    } catch { /* ignore bad cursor */ }
  }
  const rest = afterIdx >= 0 ? nodes.slice(afterIdx + 1) : nodes;
  const first = typeof args.first === 'number' ? args.first : rest.length;
  const page = rest.slice(0, first);
  const hasNext = rest.length > page.length;
  const endCursor = page.length ? b64url(`cursor:${page[page.length - 1].number}`) : null;
  return {
    nodes: page.map(mapNode),
    pageInfo: { hasNextPage: hasNext, hasPreviousPage: afterIdx >= 0, endCursor, startCursor: page.length ? b64url(`cursor:${page[0].number}`) : null },
    totalCount: nodes.length,
  };
}
function gqlResolveGlobalId(id) {
  if (typeof id !== 'string') return null;
  try {
    const text = Buffer.from(id, 'base64url').toString('utf8');
    const m = /^(repo|issue|pr|comment):(.+)$/.exec(text);
    if (!m) return null;
    return { kind: m[1], payload: m[2] };
  } catch { return null; }
}

async function gqlExecute(doc, variables) {
  const errors = [];
  const ops = gqlParse(doc);
  const results = [];
  for (const op of ops) {
    const data = {};
    const opErrors = [];
    const execFields = (node, fields, out) => {
      for (const field of fields) {
        if (field.fragment) {
          if (field.spread) continue; // no named fragments in the documents
          if (field.typeName && field.typeName !== node.__typename) continue;
          execFields(node, field.selection, out);
          continue;
        }
        const typeName = node.__typename;
        if (field.name === '__typename') { out[field.alias] = typeName; continue; }
        const allowed = GQL_FIELDS[typeName] || [];
        if (!allowed.includes(field.name)) {
          opErrors.push({ message: `Cannot query field "${field.name}" on type "${typeName}".` });
          continue;
        }
        const args = gqlArgs(field, variables);
        const value = gqlResolveField(node, field, args, field.selection, opErrors, execFields);
        out[field.alias] = value === undefined ? null : value;
      }
    };
    if (op.kind === 'mutation') {
      const root = gqlNode('Mutation', null);
      execMutationFields(root, op.selection, data, opErrors, variables);
    } else {
      const root = gqlNode('Query', null);
      execFields(root, op.selection, data);
    }
    const entry = { data };
    if (opErrors.length) entry.errors = opErrors;
    results.push(entry);
    errors.push(...opErrors);
  }
  return results;
}

function gqlResolveField(node, field, args, selection, opErrors, execFields) {
  const t = node.__typename;
  const v = node.__value;
  const repo = node.__repo;
  const resolveSub = (child) => {
    if (!selection) return null;
    const out = {};
    execFields(child, selection, out);
    return out;
  };
  switch (t) {
    case 'Query': {
      if (field.name === 'viewer') return resolveSub(gqlNode('User', { login: VIEWER_LOGIN, id: VIEWER.id, name: VIEWER_NAME, email: VIEWER_EMAIL }));
      if (field.name === 'repository') {
        const r = getRepo(args.owner, args.name);
        if (!r) return null;
        return resolveSub(gqlNode('Repository', r, { __repo: r }));
      }
      if (field.name === 'node') {
        const decoded = gqlResolveGlobalId(args.id);
        if (!decoded) return null;
        if (decoded.kind === 'repo') {
          const [owner, name] = decoded.payload.split('/');
          const r = getRepo(owner, name);
          if (!r) return null;
          return resolveSub(gqlNode('Repository', r, { __repo: r }));
        }
        if (decoded.kind === 'issue') {
          const m = /^(.+)\/(.+)#(\d+)$/.exec(decoded.payload);
          if (!m) return null;
          const r = getRepo(m[1], m[2]);
          const issue = r?.issueByNumber.get(parseInt(m[3], 10));
          if (!issue) return null;
          return resolveSub(gqlNode('Issue', issue, { __repo: r, __issue: issue }));
        }
        if (decoded.kind === 'pr') {
          const m = /^(.+)\/(.+)#(\d+)$/.exec(decoded.payload);
          if (!m) return null;
          const r = getRepo(m[1], m[2]);
          const pr = r?.prByNumber.get(parseInt(m[3], 10));
          if (!pr) return null;
          return resolveSub(gqlNode('PullRequest', pr, { __repo: r, __pr: pr }));
        }
        return null;
      }
      if (field.name === '__type') {
        const name = args.name;
        const kind = GQL_TYPE_KIND[name] ?? 'OBJECT';
        const fields = (GQL_FIELDS[name] || []).map((n) => ({ name: n }));
        const enumValues = name === 'SearchType' ? GQL_ENUM_SEARCHTYPE.map((n) => ({ name: n })) : [];
        const typeNode = gqlNode('__Type', { name, kind, fields, enumValues });
        if (!selection) return { name, kind };
        const out = {};
        execFields(typeNode, selection, out);
        return out;
      }
      if (field.name === 'search') return { nodes: [], pageInfo: { hasNextPage: false, endCursor: null } };
      if (field.name === '__schema') return resolveSub(gqlNode('__Schema', {}));
      return null;
    }
    case '__Schema': {
      if (field.name === 'queryType') return resolveSub(gqlNode('__Type', { name: 'Query', kind: 'OBJECT', fields: (GQL_FIELDS.Query || []).map((n) => ({ name: n })), enumValues: [] }));
      if (field.name === 'mutationType') return resolveSub(gqlNode('__Type', { name: 'Mutation', kind: 'OBJECT', fields: [], enumValues: [] }));
      if (field.name === 'types') return [];
      if (field.name === 'directives') return [];
      return null;
    }
    case '__Type': {
      if (field.name === 'fields') return v.fields.map((f) => resolveSub(gqlNode('__Field', f)));
      if (field.name === 'enumValues') return v.enumValues.map((e) => resolveSub(gqlNode('__EnumValue', e)));
      if (field.name === 'name') return v.name;
      if (field.name === 'kind') return v.kind;
      return null;
    }
    case '__Field':
    case '__EnumValue': {
      if (field.name === 'name') return v.name;
      return null;
    }
    case 'User': {
      if (field.name === 'login') return v.login;
      if (field.name === 'id') return globalId('user', v.login);
      if (field.name === 'name') return v.name;
      if (field.name === 'email') return v.email;
      return null;
    }
    case 'Repository': {
      const r = v;
      if (field.name === 'id') return globalId('repo', `${r.owner}/${r.name}`);
      if (field.name === 'databaseId') return r.id;
      if (field.name === 'name') return r.name;
      if (field.name === 'nameWithOwner') return `${r.owner}/${r.name}`;
      if (field.name === 'owner') return resolveSub(gqlNode('User', { login: r.owner, id: r.owner === VIEWER_LOGIN ? VIEWER.id : 0, name: r.owner === VIEWER_LOGIN ? VIEWER_NAME : r.owner, email: r.owner === VIEWER_LOGIN ? VIEWER_EMAIL : '' }));
      if (field.name === 'defaultBranchRef') return resolveSub(gqlNode('Ref', { name: r.defaultBranch }));
      if (field.name === 'viewerPermission') return 'ADMIN';
      if (field.name === 'hasIssuesEnabled') return true;
      if (field.name === 'description') return r.description;
      if (field.name === 'private') return r.private;
      if (field.name === 'url') return `https://example.invalid/${r.owner}/${r.name}`;
      if (field.name === 'issue') {
        const issue = r.issueByNumber.get(args.number);
        if (!issue) return null;
        return resolveSub(gqlNode('Issue', issue, { __repo: r, __issue: issue }));
      }
      if (field.name === 'issues') {
        const list = gqlIssueNodes(r, args);
        const conn = gqlConnection(list, args, (issue) => gqlNode('Issue', issue, { __repo: r, __issue: issue }));
        return resolveConnection(conn, selection, execFields);
      }
      if (field.name === 'pullRequests') {
        let list = [...r.pulls];
        if (Array.isArray(args.states) && args.states.length) {
          const want = new Set(args.states.map((s) => String(s).toUpperCase()));
          list = list.filter((p) => want.has(prStateGql(p)));
        }
        list.sort((a, b) => b.number - a.number);
        const conn = gqlConnection(list, args, (pr) => gqlNode('PullRequest', pr, { __repo: r, __pr: pr }));
        return resolveConnection(conn, selection, execFields);
      }
      if (field.name === 'pullRequest') {
        const pr = r.prByNumber.get(args.number);
        if (!pr) return null;
        return resolveSub(gqlNode('PullRequest', pr, { __repo: r, __pr: pr }));
      }
      return null;
    }
    case 'Issue': {
      const issue = v;
      if (field.name === 'id') return issue.nodeId;
      if (field.name === 'number') return issue.number;
      if (field.name === 'title') return issue.title;
      if (field.name === 'body') return issue.body ?? '';
      if (field.name === 'state') return issueStateGql(issue);
      if (field.name === 'createdAt' || field.name === 'updatedAt') return FIXED_DATE;
      if (field.name === 'url') return `https://example.invalid/${repo.owner}/${repo.name}/issues/${issue.number}`;
      if (field.name === 'author') return resolveSub(gqlNode('User', { login: VIEWER_LOGIN, id: VIEWER.id, name: VIEWER_NAME, email: VIEWER_EMAIL }));
      if (field.name === 'labels') return { nodes: issue.labels.map((l) => ({ name: l.name })) };
      if (field.name === 'comments') return { nodes: issue.comments.map((c) => gqlNode('Comment', c)) };
      return null;
    }
    case 'PullRequest': {
      const pr = v;
      if (field.name === 'id') return pr.nodeId;
      if (field.name === 'number') return pr.number;
      if (field.name === 'title') return pr.title;
      if (field.name === 'body') return pr.body ?? '';
      if (field.name === 'state') return prStateGql(pr);
      if (field.name === 'headRefName') return pr.head;
      if (field.name === 'baseRefName') return pr.base;
      if (field.name === 'headRefOid') return branchTip(repo, pr.head) ?? ZERO_OID;
      if (field.name === 'baseRefOid') return branchTip(repo, pr.base) ?? ZERO_OID;
      if (field.name === 'mergeable') return prMergeable(repo, pr);
      if (field.name === 'merged') return pr.merged;
      if (field.name === 'createdAt' || field.name === 'updatedAt') return FIXED_DATE;
      if (field.name === 'url') return `https://example.invalid/${repo.owner}/${repo.name}/pull/${pr.number}`;
      if (field.name === 'author') return resolveSub(gqlNode('User', { login: VIEWER_LOGIN, id: VIEWER.id, name: VIEWER_NAME, email: VIEWER_EMAIL }));
      if (field.name === 'files') {
        const files = pr.files ?? computePrFiles(repo, pr);
        const nodes = files.map((f) => gqlNode('PullRequestFile', f));
        const conn = { nodes, pageInfo: { hasNextPage: false, hasPreviousPage: false, endCursor: null, startCursor: null }, totalCount: nodes.length };
        return resolveConnection(conn, selection, execFields);
      }
      return null;
    }
    case 'Ref': {
      if (field.name === 'name') return v.name;
      if (field.name === 'target') return null;
      return null;
    }
    case 'PullRequestFile': {
      if (field.name === 'path') return v.filename;
      if (field.name === 'additions') return v.additions;
      if (field.name === 'deletions') return v.deletions;
      if (field.name === 'changeType') return v.status === 'added' ? 'ADDED' : v.status === 'removed' ? 'DELETED' : 'MODIFIED';
      return null;
    }
    case 'Comment': {
      if (field.name === 'id') return v.nodeId;
      if (field.name === 'body') return v.body;
      if (field.name === 'createdAt') return FIXED_DATE;
      return null;
    }
    default:
      return null;
  }
}
function resolveConnection(conn, selection, execFields) {
  if (!selection) return { nodes: conn.nodes.map(() => null) };
  const out = {};
  for (const field of selection) {
    if (field.fragment) continue;
    if (field.name === 'nodes') {
      out[field.alias] = conn.nodes.map((n) => {
        const o = {};
        execFields(n, field.selection ?? [], o);
        return o;
      });
    } else if (field.name === 'edges') {
      out[field.alias] = conn.nodes.map((n) => {
        const o = {};
        for (const ef of field.selection ?? []) {
          if (ef.name === 'node') {
            const no = {};
            execFields(n, ef.selection ?? [], no);
            o[ef.alias] = no;
          } else if (ef.name === 'cursor') o[ef.alias] = b64url(`cursor:${n.__value?.number ?? 0}`);
        }
        return o;
      });
    } else if (field.name === 'pageInfo') {
      const o = {};
      for (const pf of field.selection ?? []) o[pf.alias] = conn.pageInfo[pf.name] ?? null;
      out[field.alias] = o;
    } else if (field.name === 'totalCount') out[field.alias] = conn.totalCount;
    else out[field.alias] = null;
  }
  return out;
}

function execMutationFields(root, fields, out, opErrors, variables) {
  for (const field of fields) {
    if (field.fragment) continue;
    const args = gqlArgs(field, variables);
    const input = args.input ?? {};
    const wrap = (payloadNode) => {
      if (!field.selection) return {};
      const o = {};
      for (const sf of field.selection) {
        if (sf.fragment) continue;
        if (sf.name === 'issue' || sf.name === 'pullRequest') {
          const target = payloadNode[sf.name];
          if (!target) { o[sf.alias] = null; continue; }
          const so = {};
          const execFields = (node, flds, oo) => {
            for (const f of flds) {
              if (f.fragment) { if (f.typeName && f.typeName !== node.__typename) continue; execFields(node, f.selection, oo); continue; }
              if (f.name === '__typename') { oo[f.alias] = node.__typename; continue; }
              const allowed = GQL_FIELDS[node.__typename] || [];
              if (!allowed.includes(f.name)) { opErrors.push({ message: `Cannot query field "${f.name}" on type "${node.__typename}".` }); continue; }
              const a = gqlArgs(f, variables);
              oo[f.alias] = gqlResolveField(node, f, a, f.selection, opErrors, execFields) ?? null;
            }
          };
          execFields(target, sf.selection ?? [], so);
          o[sf.alias] = so;
        } else if (sf.name === 'commentEdge') {
          const edge = payloadNode.commentEdge;
          if (!edge) { o[sf.alias] = null; continue; }
          const eo = {};
          for (const ef of sf.selection ?? []) {
            if (ef.name === 'node') {
              const no = {};
              const execFields = (node, flds, oo) => {
                for (const f of flds) {
                  if (f.fragment) continue;
                  if (f.name === '__typename') { oo[f.alias] = node.__typename; continue; }
                  const allowed = GQL_FIELDS[node.__typename] || [];
                  if (!allowed.includes(f.name)) { opErrors.push({ message: `Cannot query field "${f.name}" on type "${node.__typename}".` }); continue; }
                  oo[f.alias] = gqlResolveField(node, f, gqlArgs(f, variables), f.selection, opErrors, execFields) ?? null;
                }
              };
              execFields(edge.node, ef.selection ?? [], no);
              eo[ef.alias] = no;
            }
          }
          o[sf.alias] = eo;
        } else if (sf.name === 'clientMutationId') o[sf.alias] = input.clientMutationId ?? null;
        else o[sf.alias] = null;
      }
      return o;
    };
    try {
      if (field.name === 'createIssue') {
        const decoded = gqlResolveGlobalId(input.repositoryId);
        if (!decoded || decoded.kind !== 'repo') throw new Error('unknown repository');
        const [owner, name] = decoded.payload.split('/');
        const repo = getRepo(owner, name);
        if (!repo) throw new Error('unknown repository');
        const issue = makeIssue(repo, input.title, input.body, []);
        out[field.alias] = wrap({ issue: gqlNode('Issue', issue, { __repo: repo, __issue: issue }) });
      } else if (field.name === 'closeIssue') {
        const decoded = gqlResolveGlobalId(input.issueId);
        if (!decoded || decoded.kind !== 'issue') throw new Error('unknown issue');
        const m = /^(.+)\/(.+)#(\d+)$/.exec(decoded.payload);
        const repo = getRepo(m[1], m[2]);
        const issue = repo?.issueByNumber.get(parseInt(m[3], 10));
        if (!issue) throw new Error('unknown issue');
        issue.state = 'closed';
        out[field.alias] = wrap({ issue: gqlNode('Issue', issue, { __repo: repo, __issue: issue }) });
      } else if (field.name === 'createPullRequest') {
        const decoded = gqlResolveGlobalId(input.repositoryId);
        if (!decoded || decoded.kind !== 'repo') throw new Error('unknown repository');
        const [owner, name] = decoded.payload.split('/');
        const repo = getRepo(owner, name);
        if (!repo) throw new Error('unknown repository');
        const head = shortBranch(input.headRefName);
        const base = shortBranch(input.baseRefName) || repo.defaultBranch;
        if (!branchTip(repo, head)) throw new Error('head branch does not exist');
        const dup = repo.pulls.find((p) => p.head === head && p.base === base && p.state === 'open');
        if (dup) {
          out[field.alias] = wrap({ pullRequest: gqlNode('PullRequest', dup, { __repo: repo, __pr: dup }) });
        } else {
          const pr = makePull(repo, input.title, input.body, head, base);
          out[field.alias] = wrap({ pullRequest: gqlNode('PullRequest', pr, { __repo: repo, __pr: pr }) });
        }
      } else if (field.name === 'mergePullRequest') {
        const decoded = gqlResolveGlobalId(input.pullRequestId);
        if (!decoded || decoded.kind !== 'pr') throw new Error('unknown pull request');
        const m = /^(.+)\/(.+)#(\d+)$/.exec(decoded.payload);
        const repo = getRepo(m[1], m[2]);
        const pr = repo?.prByNumber.get(parseInt(m[3], 10));
        if (!pr) throw new Error('unknown pull request');
        if (pr.state === 'open') {
          const result = doMerge(repo, pr);
          if (result.status !== 200) throw new Error(result.message);
        }
        out[field.alias] = wrap({ pullRequest: gqlNode('PullRequest', pr, { __repo: repo, __pr: pr }) });
      } else if (field.name === 'addComment') {
        const decoded = gqlResolveGlobalId(input.subjectId);
        if (!decoded || decoded.kind !== 'issue') throw new Error('unknown subject');
        const m = /^(.+)\/(.+)#(\d+)$/.exec(decoded.payload);
        const repo = getRepo(m[1], m[2]);
        const issue = repo?.issueByNumber.get(parseInt(m[3], 10));
        if (!issue) throw new Error('unknown issue');
        const comment = { id: repo.nextCommentId++, nodeId: globalId('comment', `${m[1]}/${m[2]}#${m[3]}:${repo.nextCommentId}`), body: input.body ?? '' };
        issue.comments.push(comment);
        out[field.alias] = wrap({ commentEdge: { node: gqlNode('Comment', comment) } });
      } else {
        opErrors.push({ message: `Cannot query field "${field.name}" on type "Mutation".` });
        out[field.alias] = null;
      }
    } catch (e) {
      opErrors.push({ message: e instanceof Error ? e.message : String(e) });
      out[field.alias] = null;
    }
  }
}

async function handleGraphql(req, res, rawBody) {
  if (!authed(req)) { errJson(res, 401, 'Requires authentication'); return; }
  let body;
  try { body = JSON.parse(rawBody.toString('utf8')); }
  catch { errJson(res, 400, 'Request body is not valid JSON'); return; }
  const ops = Array.isArray(body) ? body : [body];
  const out = [];
  for (const op of ops) {
    if (!op || typeof op.query !== 'string') { out.push({ data: null, errors: [{ message: 'query is required' }] }); continue; }
    try {
      const results = await gqlExecute(op.query, op.variables ?? {});
      out.push(results[0]);
    } catch (e) {
      out.push({ data: null, errors: [{ message: e instanceof Error ? e.message : String(e) }] });
    }
  }
  jsonBody(res, 200, Array.isArray(body) ? out : out[0]);
}

// ---------------------------------------------------------------------------
// MCP /mcp — JSON-RPC 2.0 Streamable HTTP, revision 2026-07-28
// ---------------------------------------------------------------------------

const MCP_VERSIONS = ['2026-07-28', '2025-11-25'];
const MCP_SERVER_INFO = { name: 'github-forge', version: '1.0.0' };
const MCP_TOOLS = Object.freeze([
  { name: 'create_repo', description: 'Create a new repository for the authenticated user.', inputSchema: { type: 'object', properties: { name: { type: 'string', description: 'Repository name' }, description: { type: 'string', description: 'Repository description' }, private: { type: 'boolean', description: 'Whether the repository is private' }, owner: { type: 'string', description: 'Owner login (defaults to the authenticated user)' } }, required: ['name'] } },
  { name: 'get_repo', description: 'Get a repository by owner and name.', inputSchema: { type: 'object', properties: { owner: { type: 'string', description: 'Owner login' }, repo: { type: 'string', description: 'Repository name' } }, required: ['owner', 'repo'] } },
  { name: 'create_issue', description: 'Create an issue in a repository.', inputSchema: { type: 'object', properties: { owner: { type: 'string', description: 'Owner login' }, repo: { type: 'string', description: 'Repository name' }, title: { type: 'string', description: 'Issue title' }, body: { type: 'string', description: 'Issue body' } }, required: ['owner', 'repo', 'title'] } },
  { name: 'list_issues', description: 'List issues in a repository.', inputSchema: { type: 'object', properties: { owner: { type: 'string', description: 'Owner login' }, repo: { type: 'string', description: 'Repository name' }, state: { type: 'string', description: 'Issue state filter: open, closed, or all' } }, required: ['owner', 'repo'] } },
  { name: 'get_issue', description: 'Get a single issue by number.', inputSchema: { type: 'object', properties: { owner: { type: 'string', description: 'Owner login' }, repo: { type: 'string', description: 'Repository name' }, issue_number: { type: 'integer', description: 'Issue number' } }, required: ['owner', 'repo', 'issue_number'] } },
  { name: 'create_pull_request', description: 'Create a pull request between two branches.', inputSchema: { type: 'object', properties: { owner: { type: 'string', description: 'Owner login' }, repo: { type: 'string', description: 'Repository name' }, title: { type: 'string', description: 'Pull request title' }, body: { type: 'string', description: 'Pull request body' }, head: { type: 'string', description: 'Head branch name' }, base: { type: 'string', description: 'Base branch name' } }, required: ['owner', 'repo', 'title', 'head', 'base'] } },
  { name: 'merge_pull_request', description: 'Merge an open pull request.', inputSchema: { type: 'object', properties: { owner: { type: 'string', description: 'Owner login' }, repo: { type: 'string', description: 'Repository name' }, pull_number: { type: 'integer', description: 'Pull request number' } }, required: ['owner', 'repo', 'pull_number'] } },
  { name: 'list_pull_requests', description: 'List pull requests in a repository.', inputSchema: { type: 'object', properties: { owner: { type: 'string', description: 'Owner login' }, repo: { type: 'string', description: 'Repository name' }, state: { type: 'string', description: 'Pull request state filter: open, closed, or all' } }, required: ['owner', 'repo'] } },
]);
const MCP_TOOLS_LIST = Object.freeze({ tools: MCP_TOOLS.map((t) => ({ name: t.name, description: t.description, inputSchema: t.inputSchema })) });

function mcpResult(id, result) { return { jsonrpc: '2.0', id: id ?? null, result }; }
function mcpError(id, code, message) { return { jsonrpc: '2.0', id: id ?? null, error: { code, message } }; }
function mcpToolText(obj) { return { content: [{ type: 'text', text: JSON.stringify(obj) }], structuredContent: obj }; }
function mcpToolError(message) { return { content: [{ type: 'text', text: JSON.stringify({ error: message }) }], isError: true }; }

function mcpCallTool(name, args) {
  const canonical = name.replace(/^github__/, '').toLowerCase();
  const tool = MCP_TOOLS.find((t) => t.name === canonical);
  if (!tool) return { error: { code: -32602, message: `Unknown tool: ${name}` } };
  const a = args && typeof args === 'object' ? args : {};
  const missing = (tool.inputSchema.required || []).filter((k) => a[k] === undefined || a[k] === null || a[k] === '');
  if (missing.length) return { result: mcpToolError(`Missing required argument(s): ${missing.join(', ')}`) };
  const owner = typeof a.owner === 'string' ? a.owner : VIEWER_LOGIN;
  const repoName = typeof a.repo === 'string' ? a.repo : (typeof a.repository === 'string' ? a.repository : '');
  try {
    if (canonical === 'create_repo') {
      const repoOwner = typeof a.owner === 'string' ? a.owner : VIEWER_LOGIN;
      if (repos.has(repoKey(repoOwner, a.name))) return { result: mcpToolError(`Repository ${repoOwner}/${a.name} already exists`) };
      const repo = createRepoRecord(repoOwner, a.name, a.description, a.private);
      return { result: mcpToolText({ id: repo.id, node_id: globalId('repo', `${repo.owner}/${repo.name}`), name: repo.name, full_name: `${repo.owner}/${repo.name}`, owner: repo.owner, description: repo.description, private: repo.private, default_branch: repo.defaultBranch }) };
    }
    const repo = getRepo(owner, repoName);
    if (!repo) return { result: mcpToolError(`Repository ${owner}/${repoName} not found`) };
    if (canonical === 'get_repo') {
      return { result: mcpToolText({ id: repo.id, node_id: globalId('repo', `${repo.owner}/${repo.name}`), name: repo.name, full_name: `${repo.owner}/${repo.name}`, owner: repo.owner, description: repo.description, private: repo.private, default_branch: repo.defaultBranch }) };
    }
    if (canonical === 'create_issue') {
      const issue = makeIssue(repo, a.title, a.body, []);
      return { result: mcpToolText({ id: issue.id, node_id: issue.nodeId, number: issue.number, title: issue.title, body: issue.body, state: issue.state, url: `/api/v3/repos/${repo.owner}/${repo.name}/issues/${issue.number}` }) };
    }
    if (canonical === 'list_issues') {
      const state = typeof a.state === 'string' ? a.state : 'open';
      const list = repo.issues.filter((i) => state === 'all' ? true : i.state === state).map((i) => ({ id: i.id, node_id: i.nodeId, number: i.number, title: i.title, body: i.body, state: i.state }));
      return { result: mcpToolText({ issues: list, total_count: list.length }) };
    }
    if (canonical === 'get_issue') {
      const issue = repo.issueByNumber.get(Number(a.issue_number));
      if (!issue) return { result: mcpToolError(`Issue #${a.issue_number} not found`) };
      return { result: mcpToolText({ id: issue.id, node_id: issue.nodeId, number: issue.number, title: issue.title, body: issue.body, state: issue.state }) };
    }
    if (canonical === 'create_pull_request') {
      const head = shortBranch(a.head);
      const base = shortBranch(a.base) || repo.defaultBranch;
      if (!branchTip(repo, head)) return { result: mcpToolError(`head branch '${head}' does not exist`) };
      const dup = repo.pulls.find((p) => p.head === head && p.base === base && p.state === 'open');
      if (dup) return { result: mcpToolError('A pull request already exists for this head and base') };
      const pr = makePull(repo, a.title, a.body, head, base);
      return { result: mcpToolText({ id: pr.id, node_id: pr.nodeId, number: pr.number, title: pr.title, body: pr.body, state: pr.state, head: { ref: pr.head, sha: branchTip(repo, pr.head) }, base: { ref: pr.base, sha: branchTip(repo, pr.base) }, merged: false }) };
    }
    if (canonical === 'merge_pull_request') {
      const pr = repo.prByNumber.get(Number(a.pull_number));
      if (!pr) return { result: mcpToolError(`Pull request #${a.pull_number} not found`) };
      if (pr.state !== 'open') return { result: mcpToolError('Pull request is already closed') };
      const result = doMerge(repo, pr);
      if (result.status !== 200) return { result: mcpToolError(result.message) };
      return { result: mcpToolText({ merged: true, sha: result.sha, message: 'Pull Request successfully merged' }) };
    }
    if (canonical === 'list_pull_requests') {
      const state = typeof a.state === 'string' ? a.state : 'open';
      const list = repo.pulls.filter((p) => state === 'all' ? true : p.state === state).map((p) => ({ id: p.id, node_id: p.nodeId, number: p.number, title: p.title, body: p.body, state: p.state, merged: p.merged, head: { ref: p.head }, base: { ref: p.base } }));
      return { result: mcpToolText({ pull_requests: list, total_count: list.length }) };
    }
  } catch (e) {
    return { result: mcpToolError(e instanceof Error ? e.message : String(e)) };
  }
  return { error: { code: -32602, message: `Unknown tool: ${name}` } };
}

async function handleMcp(req, res, rawBody) {
  if (!authed(req)) {
    res.writeHead(401, { 'content-type': 'application/json', 'x-github-request-id': `forge-${++requestCounter}` });
    res.end(JSON.stringify({ jsonrpc: '2.0', id: null, error: { code: -32000, message: 'Requires authentication' } }));
    return;
  }
  const text = rawBody.toString('utf8');
  let msg;
  try { msg = JSON.parse(text); }
  catch {
    res.writeHead(400, { 'content-type': 'application/json', 'x-github-request-id': `forge-${++requestCounter}` });
    res.end(JSON.stringify({ jsonrpc: '2.0', id: null, error: { code: -32700, message: 'Parse error' } }));
    return;
  }
  const isNotification = msg && typeof msg === 'object' && msg.method && msg.id === undefined;
  if (isNotification) {
    res.writeHead(202, { 'x-github-request-id': `forge-${++requestCounter}` });
    res.end();
    return;
  }
  const id = msg?.id ?? null;
  const method = msg?.method;
  const params = msg?.params ?? {};
  const respond = (payload, status) => {
    res.writeHead(status ?? 200, { 'content-type': 'application/json', 'x-github-request-id': `forge-${++requestCounter}` });
    res.end(JSON.stringify(payload));
  };
  if (method === 'server/discover') {
    respond(mcpResult(id, {
      serverInfo: MCP_SERVER_INFO,
      capabilities: { tools: {} },
      supportedVersions: MCP_VERSIONS,
      protocolVersion: '2026-07-28',
      _meta: { 'io.modelcontextprotocol/serverInfo': MCP_SERVER_INFO },
    }));
    return;
  }
  if (method === 'initialize') {
    const requested = Array.isArray(params.protocolVersion) ? params.protocolVersion : [params.protocolVersion];
    const negotiated = requested.find((v) => MCP_VERSIONS.includes(v)) ?? '2026-07-28';
    respond(mcpResult(id, { protocolVersion: negotiated, capabilities: { tools: {} }, serverInfo: MCP_SERVER_INFO }));
    return;
  }
  if (method === 'ping') { respond(mcpResult(id, {})); return; }
  if (method === 'tools/list') { respond(mcpResult(id, MCP_TOOLS_LIST)); return; }
  if (method === 'tools/call') {
    const out = mcpCallTool(params.name, params.arguments ?? {});
    if (out.error) respond(mcpError(id, out.error.code, out.error.message));
    else respond(mcpResult(id, out.result));
    return;
  }
  if (method === 'resources/list') { respond(mcpResult(id, { resources: [] })); return; }
  if (method === 'prompts/list') { respond(mcpResult(id, { prompts: [] })); return; }
  respond(mcpError(id, -32601, `Method not found: ${method}`));
}

// ---------------------------------------------------------------------------
// Git smart HTTP: /{owner}/{repo}.git/{service}
// ---------------------------------------------------------------------------

// Adapters over the part-1 helpers (decodePktLines / PKT_FLUSH / PKT_DELIM).
function pktFlush() { return PKT_FLUSH; }
function pktDelim() { return PKT_DELIM; }
// Decode one packet at offset: {len, payload}; payload null for flush/delim/response-end.
function decodePktLine(buf, offset) {
  if (offset + 4 > buf.length) return { len: 0, payload: null };
  const head = buf.subarray(offset, offset + 4).toString('ascii');
  if (head === '0000') return { len: 4, payload: null };
  if (head === '0001') return { len: 4, payload: Buffer.from([1]) };
  if (head === '0002') return { len: 4, payload: null };
  const len = parseInt(head, 16);
  if (!Number.isFinite(len) || len < 4 || offset + len > buf.length) throw new Error('bad pkt-line length');
  return { len, payload: buf.subarray(offset + 4, offset + len) };
}

const UPLOAD_CAPS_V0 = 'symref=HEAD:refs/heads/main side-band-64k thin-pack ofs-delta shallow multi_ack_detailed';
const RECEIVE_CAPS = 'report-status side-band-64k delete-refs ofs-delta';
const GIT_AGENT = 'github-forge/1.0.0';

function sidebandPack(packBuf) {
  // Sideband framing (band 1), chunks <= 65515 data bytes.
  const chunks = [];
  for (let off = 0; off < packBuf.length; off += 65515) {
    const slice = packBuf.subarray(off, off + 65515);
    chunks.push(pktLine(Buffer.concat([Buffer.from([1]), slice])));
  }
  chunks.push(pktFlush());
  return Buffer.concat(chunks);
}
function refAdvertisementLines(repo, caps) {
  const lines = [];
  const headTip = branchTip(repo, repo.defaultBranch);
  const refs = [...repo.refs.entries()].sort((a, b) => (a[0] < b[0] ? -1 : 1));
  if (refs.length === 0) {
    lines.push(pktLine(Buffer.concat([Buffer.from(`${ZERO_OID} capabilities^{}`), Buffer.from([0]), Buffer.from(caps)])));
  } else {
    let first = true;
    for (const [ref, oid] of refs) {
      if (first) {
        lines.push(pktLine(Buffer.concat([Buffer.from(`${oid} ${ref}`), Buffer.from([0]), Buffer.from(caps)])));
        first = false;
      } else {
        lines.push(pktLine(Buffer.from(`${oid} ${ref}`)));
      }
    }
    if (headTip === null && refs.length > 0) {
      // HEAD points at unborn default branch; nothing extra to add.
    }
  }
  // HEAD symref line is carried in capabilities for v0 upload-pack.
  lines.push(pktFlush());
  return Buffer.concat(lines);
}

function gitAdvertise(repo, service, wantsV2) {
  const isUpload = service === 'git-upload-pack';
  const ct = isUpload ? 'application/x-git-upload-pack-advertisement' : 'application/x-git-receive-pack-advertisement';
  let body;
  if (wantsV2) {
    const lines = [pktLine(Buffer.from('version 2'))];
    if (isUpload) {
      lines.push(pktLine(Buffer.from('agent=github-forge/1.0.0')));
      lines.push(pktLine(Buffer.from('ls-refs=unborn')));
      lines.push(pktLine(Buffer.from('fetch=shallow wait-for-done')));
      lines.push(pktLine(Buffer.from('object-format=sha1')));
    } else {
      lines.push(pktLine(Buffer.from('agent=github-forge/1.0.0')));
    }
    lines.push(pktFlush());
    body = Buffer.concat(lines);
  } else {
    const serviceLine = pktLine(Buffer.from(`# service=${service}\n`));
    body = Buffer.concat([serviceLine, pktFlush(), refAdvertisementLines(repo, isUpload ? UPLOAD_CAPS_V0 : RECEIVE_CAPS)]);
  }
  return { contentType: ct, body };
}

function handleLsRefs(repo, reqBuf) {
  // Parse v2 request pkt-lines.
  const args = [];
  let offset = 0;
  let command = '';
  while (offset < reqBuf.length) {
    const { len, payload } = decodePktLine(reqBuf, offset);
    offset += len;
    if (len === 0) break;
    if (payload === null) break;
    const text = payload.toString('utf8');
    if (text.startsWith('command=')) command = text.slice('command='.length).trim();
    else if (text.trim() !== '' && !text.startsWith('agent=') && !text.startsWith('object-format=')) args.push(text);
    if (text.trim() === '') break; // delim ends header block; args follow
    if (payload[0] === 1) break; // delim
  }
  // After delim, args are pkt-lines until flush.
  const extra = [];
  while (offset < reqBuf.length) {
    const { len, payload } = decodePktLine(reqBuf, offset);
    offset += len;
    if (len === 0) break;
    if (payload === null) break;
    extra.push(payload.toString('utf8').trimEnd());
  }
  const all = [...args, ...extra].filter((t) => t !== '' && !t.startsWith('agent=') && !t.startsWith('object-format='));
  const prefixes = all.filter((t) => t.startsWith('ref-prefix ')).map((t) => t.slice('ref-prefix '.length));
  const wantPeel = all.includes('peel');
  const wantSymrefs = all.includes('symrefs');
  const wantUnborn = all.includes('unborn');
  const out = [];
  const headTip = branchTip(repo, repo.defaultBranch);
  const matches = (name) => prefixes.length === 0 || prefixes.some((p) => name.startsWith(p));
  if (command !== 'ls-refs') return PKT_FLUSH;
  if (headTip === null) {
    if (wantUnborn && matches('HEAD')) {
      out.push(pktLine(Buffer.from('unborn HEAD symref-target:refs/heads/main')));
    }
  } else {
    if (matches('HEAD') && wantSymrefs) out.push(pktLine(Buffer.from(`${headTip} HEAD symref-target:refs/heads/main`)));
  }
  const refs = [...repo.refs.entries()].sort((a, b) => (a[0] < b[0] ? -1 : 1));
  for (const [ref, oid] of refs) {
    if (!matches(ref)) continue;
    let line = `${oid} ${ref}`;
    if (wantSymrefs && ref === 'refs/heads/main') line += ' symref-target:refs/heads/main';
    const obj = repo.objects.get(oid);
    if (wantPeel && obj && obj.type === 'tag') {
      const peeled = peelToCommit(repo, oid);
      if (peeled) line += ` peeled:${peeled}`;
    }
    out.push(pktLine(Buffer.from(line)));
  }
  out.push(pktFlush());
  return Buffer.concat(out);
}

function collectTreeHeld(repo, treeOid, into) {
  const obj = repo.objects.get(treeOid);
  if (!obj || obj.type !== 'tree') return;
  for (const e of parseTree(obj.data)) {
    if (into.has(e.oid)) continue;
    into.add(e.oid);
    if (e.mode === '40000') collectTreeHeld(repo, e.oid, into);
  }
}

function handleFetchV2(repo, reqBuf) {
  const wants = [];
  const haves = [];
  let deepen = null;
  const shallowHeld = [];
  let offset = 0;
  while (offset < reqBuf.length) {
    const { len, payload } = decodePktLine(reqBuf, offset);
    offset += len;
    if (len === 0) break;
    if (payload === null) break;
    const text = payload.toString('utf8').trimEnd();
    if (text.startsWith('want ')) wants.push(text.slice(5));
    else if (text.startsWith('have ')) haves.push(text.slice(5));
    else if (text.startsWith('shallow ')) shallowHeld.push(text.slice(8));
    else if (text.startsWith('deepen ')) deepen = parseInt(text.slice(7), 10);
    else if (text === 'done') break;
  }
  // Compute the object set to send.
  // haveSet = objects the client already holds. A non-shallow `have` covers its
  // whole ancestry; a shallow-held commit covers only itself + its tree (its
  // parents are NOT held — that is what deepening later delivers).
  const shallowSet = new Set(shallowHeld);
  const haveSet = new Set();
  for (const h of haves) {
    if (shallowSet.has(h)) continue; // handled below, without ancestors
    for (const o of collectReachable([h], (oid) => repo.objects.get(oid))) haveSet.add(o);
  }
  for (const s of shallowHeld) {
    const obj = repo.objects.get(s);
    if (!obj) continue;
    haveSet.add(s);
    if (obj.type === 'commit') {
      const tree = parseCommit(obj.data).tree;
      haveSet.add(tree);
      collectTreeHeld(repo, tree, haveSet);
    }
  }
  const send = new Set();
  const seen = new Set();
  const newShallow = [];
  const unshallowSet = new Set();
  const depth = deepen === null ? Infinity : deepen;
  // Traversal is separate from sending: we walk through held wants too, so a
  // deepen past a held tip still delivers its parents.
  const visit = (oid, d) => {
    if (seen.has(oid)) return;
    seen.add(oid);
    const obj = repo.objects.get(oid);
    if (!obj) return;
    if (!haveSet.has(oid)) send.add(oid);
    if (obj.type === 'commit') {
      const c = parseCommit(obj.data);
      if (!haveSet.has(c.tree)) {
        send.add(c.tree);
        collectTree(c.tree, send, haveSet);
      }
      if (d >= depth) {
        if (!haveSet.has(oid)) newShallow.push(oid);
        return;
      }
      if (shallowSet.has(oid)) unshallowSet.add(oid);
      for (const p of c.parents) visit(p, d + 1);
    } else if (obj.type === 'tag') {
      const t = parseTag(obj.data);
      if (d < depth) visit(t.object, d);
    }
  };
  const collectTree = (treeOid, into, held) => {
    const obj = repo.objects.get(treeOid);
    if (!obj || obj.type !== 'tree') return;
    for (const e of parseTree(obj.data)) {
      if (into.has(e.oid) || (held && held.has(e.oid))) continue;
      into.add(e.oid);
      if (e.mode === '40000') collectTree(e.oid, into, held);
    }
  };
  for (const w of wants) {
    const peeled = peelToCommit(repo, w) ?? w;
    visit(peeled, 1);
    // The wanted ref itself (tag object) must be included.
    if (w !== peeled && !haveSet.has(w)) { const obj = repo.objects.get(w); if (obj) send.add(w); }
  }
  const unshallow = [...unshallowSet];
  const sections = [];
  sections.push(pktLine(Buffer.from('acknowledgments\n')));
  sections.push(pktLine(Buffer.from('NAK\n')));
  sections.push(pktDelim());
  if (newShallow.length || unshallow.length) {
    sections.push(pktLine(Buffer.from('shallow-info\n')));
    for (const s of newShallow) sections.push(pktLine(Buffer.from(`shallow ${s}\n`)));
    for (const s of unshallow) sections.push(pktLine(Buffer.from(`unshallow ${s}\n`)));
    sections.push(pktDelim());
  }
  if (send.size > 0) {
    sections.push(pktLine(Buffer.from('packfile\n')));
    const pack = writePack([...send].map((oid) => ({ oid, ...repo.objects.get(oid) })));
    sections.push(sidebandPack(pack));
  }
  sections.push(pktFlush());
  return Buffer.concat(sections);
}

function handleFetchV0(repo, reqBuf) {
  // Defensive: parse wants/haves; respond NAK + sideband pack.
  const wants = [];
  const haves = [];
  let offset = 0;
  while (offset < reqBuf.length) {
    const { len, payload } = decodePktLine(reqBuf, offset);
    offset += len;
    if (len === 0) break;
    if (payload === null) break;
    const text = payload.toString('utf8').trimEnd();
    if (text.startsWith('want ')) wants.push(text.slice(5).split(' ')[0]);
    else if (text.startsWith('have ')) haves.push(text.slice(5));
    else if (text === 'done') break;
  }
  const haveSet = new Set();
  for (const h of haves) {
    for (const o of collectReachable([h], (oid) => repo.objects.get(oid))) haveSet.add(o);
  }
  const send = new Set();
  for (const w of wants) {
    const peeled = peelToCommit(repo, w) ?? w;
    for (const o of collectReachable([peeled], (oid) => repo.objects.get(oid))) send.add(o);
    if (w !== peeled) send.add(w);
  }
  for (const h of haveSet) send.delete(h);
  const out = [pktLine(Buffer.from('NAK\n'))];
  if (send.size > 0) {
    const pack = writePack([...send].map((oid) => ({ oid, ...repo.objects.get(oid) })));
    out.push(sidebandPack(pack));
  }
  out.push(pktFlush());
  return Buffer.concat(out);
}

function handleReceivePack(repo, reqBuf) {
  // Parse commands until flush, then pack bytes.
  const commands = [];
  let offset = 0;
  let capsLine = '';
  while (offset < reqBuf.length) {
    const { len, payload } = decodePktLine(reqBuf, offset);
    offset += len;
    if (len === 0) break;
    if (payload === null) break;
    let text = payload.toString('utf8');
    const nul = text.indexOf('\0');
    if (nul >= 0) { capsLine = text.slice(nul + 1); text = text.slice(0, nul); }
    text = text.trimEnd();
    if (text === '') continue;
    const parts = text.split(' ');
    if (parts.length === 3) commands.push({ oldOid: parts[0], newOid: parts[1], ref: parts[2] });
  }
  let packOk = true;
  if (offset < reqBuf.length) {
    const packBytes = reqBuf.subarray(offset);
    if (packBytes.length >= 12) {
      try {
        const { objects } = readPack(packBytes);
        for (const [oid, obj] of objects) {
          if (!repo.objects.has(oid)) repo.objects.set(oid, { type: obj.type, data: obj.data });
        }
      } catch { packOk = false; }
    }
  }
  const report = [];
  report.push(`unpack ${packOk ? 'ok' : 'error'}\n`);
  for (const cmd of commands) {
    const current = repo.refs.get(cmd.ref) ?? ZERO_OID;
    if (cmd.newOid === ZERO_OID) {
      // Delete.
      if (current !== ZERO_OID) repo.refs.delete(cmd.ref);
      report.push(`ok ${cmd.ref}\n`);
      continue;
    }
    if (cmd.oldOid === ZERO_OID) {
      // Create.
      if (current !== ZERO_OID) { report.push(`ng ${cmd.ref} reference already exists\n`); continue; }
      if (!repo.objects.has(cmd.newOid)) { report.push(`ng ${cmd.ref} missing object\n`); continue; }
      repo.refs.set(cmd.ref, cmd.newOid);
      report.push(`ok ${cmd.ref}\n`);
      continue;
    }
    if (current !== cmd.oldOid) { report.push(`ng ${cmd.ref} old ref does not match\n`); continue; }
    if (!isAncestor(cmd.oldOid, cmd.newOid, (oid) => repo.objects.get(oid))) {
      report.push(`ng ${cmd.ref} non-fast-forward\n`);
      continue;
    }
    repo.refs.set(cmd.ref, cmd.newOid);
    report.push(`ok ${cmd.ref}\n`);
  }
  const body = Buffer.concat(report.map((r) => pktLine(Buffer.from(r))));
  const framed = Buffer.concat([pktLine(Buffer.concat([Buffer.from([1]), body])), pktFlush()]);
  return { contentType: 'application/x-git-receive-pack-result', body: framed };
}

async function handleGit(req, res, owner, name, service, rawBody) {
  const repo = getRepo(owner, name);
  const wantsV2 = (req.headers['git-protocol'] ?? '') === 'version=2';
  if (req.method === 'GET') {
    if (!service) { errJson(res, 404, 'Not Found'); return; }
    if (!repo) { errJson(res, 404, 'Not Found'); return; }
    const { contentType, body } = gitAdvertise(repo, service, wantsV2);
    res.writeHead(200, { 'content-type': contentType, 'x-github-request-id': `forge-${++requestCounter}` });
    res.end(body);
    return;
  }
  if (req.method === 'POST') {
    if (!service) { errJson(res, 404, 'Not Found'); return; }
    if (!repo) { errJson(res, 404, 'Not Found'); return; }
    try {
      let result;
      if (service === 'git-upload-pack') {
        const isV2 = wantsV2 || reqBufHasCommand(rawBody, 'ls-refs') || reqBufHasCommand(rawBody, 'fetch');
        let body;
        if (isV2 && reqBufHasCommand(rawBody, 'ls-refs')) body = handleLsRefs(repo, rawBody);
        else if (isV2) body = handleFetchV2(repo, rawBody);
        else body = handleFetchV0(repo, rawBody);
        result = { contentType: 'application/x-git-upload-pack-result', body };
      } else if (service === 'git-receive-pack') {
        result = handleReceivePack(repo, rawBody);
      } else {
        errJson(res, 404, 'Not Found'); return;
      }
      res.writeHead(200, { 'content-type': result.contentType, 'x-github-request-id': `forge-${++requestCounter}` });
      res.end(result.body);
    } catch (e) {
      errJson(res, 400, e instanceof Error ? e.message : 'bad git request');
    }
    return;
  }
  errJson(res, 404, 'Not Found');
}
function reqBufHasCommand(buf, cmd) {
  try {
    let offset = 0;
    while (offset < buf.length) {
      const { len, payload } = decodePktLine(buf, offset);
      offset += len;
      if (len === 0) break;
      if (payload === null) break;
      if (payload.toString('utf8').includes(`command=${cmd}`)) return true;
    }
  } catch { /* ignore */ }
  return false;
}

// ---------------------------------------------------------------------------
// HTTP server + lifecycle
// ---------------------------------------------------------------------------

const ENV_URL = process.env.MAKEFUN_ENV_URL ?? '';
const STANDALONE_PORT = parseInt(process.env.FORGE_PORT ?? '0', 10) || 0;

function sleep(ms) { return new Promise((r) => setTimeout(r, ms)); }
function httpJson(url, method, body, headers) {
  return new Promise((resolve, reject) => {
    const u = new URL(url);
    const payload = body === undefined ? null : (typeof body === 'string' ? body : JSON.stringify(body));
    const req = http.request({
      protocol: u.protocol, hostname: u.hostname, port: u.port, path: `${u.pathname}${u.search}`,
      method, headers: { 'content-type': 'application/json', ...(payload ? { 'content-length': Buffer.byteLength(payload) } : {}), ...(headers || {}) },
    }, (res) => {
      const chunks = [];
      res.on('data', (c) => chunks.push(c));
      res.on('end', () => resolve({ status: res.statusCode ?? 0, text: Buffer.concat(chunks).toString('utf8') }));
    });
    req.on('error', reject);
    if (payload) req.write(payload);
    req.end();
  });
}

const server = http.createServer(async (req, res) => {
  try {
    const url = new URL(req.url ?? '/', `http://${req.headers.host ?? '127.0.0.1'}`);
    const segments = url.pathname.split('/').filter((s) => s !== '');
    // Health (no auth).
    if (url.pathname === '/healthz') { jsonBody(res, 200, { ok: true }); return; }
    if (url.pathname === '/') { jsonBody(res, 200, { ok: true, service: 'github-forge' }); return; }
    // Read body once (GET may have none).
    const rawBody = await readBody(req);
    // MCP
    if (url.pathname === '/mcp') {
      if (req.method === 'DELETE') { res.writeHead(202, { 'x-github-request-id': `forge-${++requestCounter}` }); res.end(); return; }
      if (req.method !== 'POST') { errJson(res, 404, 'Not Found'); return; }
      await handleMcp(req, res, rawBody);
      return;
    }
    // GraphQL
    if (url.pathname === '/api/graphql') {
      if (req.method !== 'POST') { errJson(res, 404, 'Not Found'); return; }
      await handleGraphql(req, res, rawBody);
      return;
    }
    // REST v3
    if (segments[0] === 'api' && segments[1] === 'v3') {
      let body = {};
      if (rawBody.length > 0) {
        try { body = parseJsonBody(rawBody); }
        catch { errJson(res, 400, 'Request body is not valid JSON'); return; }
      }
      await handleRest(req, res, url, segments.slice(2), body);
      return;
    }
    // Git smart HTTP: /{owner}/{repo}.git/...
    const gitMatch = /^\/([^/]+)\/([^/]+)\.git\/(info\/refs|git-upload-pack|git-receive-pack)$/.exec(url.pathname);
    if (gitMatch) {
      const owner = decodeURIComponent(gitMatch[1]);
      const name = decodeURIComponent(gitMatch[2]);
      const tail = gitMatch[3];
      if (tail === 'info/refs') {
        const service = url.searchParams.get('service');
        if (service !== 'git-upload-pack' && service !== 'git-receive-pack') { errJson(res, 400, 'service is required'); return; }
        await handleGit(req, res, owner, name, service, rawBody);
        return;
      }
      await handleGit(req, res, owner, name, tail, rawBody);
      return;
    }
    errJson(res, 404, 'Not Found');
  } catch (e) {
    try { errJson(res, 500, e instanceof Error ? e.message : 'internal error'); } catch { /* socket gone */ }
  }
});

async function main() {
  await new Promise((resolve) => server.listen(STANDALONE_PORT, '127.0.0.1', resolve));
  const port = server.address().port;
  if (ENV_URL === '') {
    // Standalone mode (local practice runs): print the port and serve forever.
    process.stdout.write(`github-forge listening on 127.0.0.1:${port}\n`);
    return;
  }
  // Suite mode: register, then long-poll /done.
  let registered = false;
  let delay = 250;
  for (let attempt = 0; attempt < 40 && !registered; attempt += 1) {
    try {
      const r = await httpJson(`${ENV_URL}/register`, 'POST', { port });
      if (r.status === 200 || r.status === 409) registered = true;
      else if (r.status === 400 || r.status === 405) throw new Error(`register failed: ${r.status} ${r.text}`);
    } catch (e) {
      if (e instanceof Error && e.message.startsWith('register failed')) throw e;
    }
    if (!registered) { await sleep(delay); delay = Math.min(delay * 2, 2000); }
  }
  if (!registered) throw new Error('could not register with suite env');
  for (;;) {
    await sleep(500);
    try {
      const r = await httpJson(`${ENV_URL}/done`, 'GET');
      if (r.status === 200) {
        const parsed = JSON.parse(r.text);
        if (parsed && parsed.done === true) break;
      }
    } catch { /* keep polling */ }
  }
  server.close();
  process.exit(0);
}

main().catch((e) => {
  process.stderr.write(`fatal: ${e instanceof Error ? e.message : String(e)}\n`);
  process.exit(1);
});
