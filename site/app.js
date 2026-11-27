'use strict';
/* Progress site for the LeetCode Rust-to-Lean theorems.
   Data (built by tools/build_site.py): data/index.json (programs and their theorem statuses),
   data/theorems.json (one row per theorem), data/p/<task>.json (one program). */
(() => {
const $ = id => document.getElementById(id);
const DATASET = 'https://huggingface.co/datasets/Debargha/leetcode-rust-lean';
const DISCUSS = DATASET + '/discussions';
const REPO = 'https://github.com/DebarghaG/leetcode-rust-lean';
const CAT = {re: 'relational', ed: 'edge', bo: 'bounds', in: 'invariance', fu: 'functional',
             wi: 'witness', no: 'no_failure', sh: 'shape', mo: 'monotonicity'};
const DIFF = {E: 'Easy', M: 'Medium', H: 'Hard'};
const STATUS = {o: 'open', p: 'proved', r: 'refuted', x: 'conflict', s: 'superseded'};
let D = null, THMS = null, BY = {}, cur = null, mapState = {tag: '', split: '', q: '', by: 'topic'};

const esc = s => String(s ?? '').replace(/[&<>"]/g, c => ({'&': '&amp;', '<': '&lt;', '>': '&gt;', '"': '&quot;'}[c]));
const fmt = n => n.toLocaleString('en-US');
const PAPER = 'https://arxiv.org/abs/2610.38174';
const BIBTEX = `@misc{ganguly2026scalingleantheoremproving,
      title={Scaling Lean Theorem Proving for Real-World Code Verification},
      author={Debargha Ganguly and Divya Raghunathan and Dejan Jovanović and Vikash Singh and Soonho Kong and Aaron Tomb and Aman Goel and Ferhat Erata and Sam Bayless},
      year={2026},
      eprint={2610.38174},
      archivePrefix={arXiv},
      primaryClass={cs.CL},
      url={https://arxiv.org/abs/2610.38174},
}`;
function citeHtml() {
  return `<h2 id="cite">Citation</h2>
  <p class="hint">This is an unofficial reproduction of the methodology of
  <a href="${PAPER}"><i>Scaling Lean Theorem Proving for Real-World Code Verification</i></a>, made by the paper's first
  author. It is not an official release of the paper. If you use the dataset or the proofs, please cite the paper:</p>
  <div style="max-width:90ch">${pre(BIBTEX, BIBTEX, false)}</div>`;
}
const SMALL = new Set('a an and as at by for from in into of on or the to with'.split(' '));
const ROMAN = /^(i|ii|iii|iv|v|vi|vii|viii|ix|x)$/;
const title = t => t.split('-').map((w, i) => !w ? w : ROMAN.test(w) && i ? w.toUpperCase() : i && SMALL.has(w) ? w : w[0].toUpperCase() + w.slice(1)).join(' ');
const css = v => getComputedStyle(document.documentElement).getPropertyValue(v).trim();
const cats = p => (p.c.match(/../g) || []).map(c => CAT[c]);

async function json(url) { const r = await fetch(url); if (!r.ok) throw new Error(url + ': ' + r.status); return r.json(); }
async function theorems() { return THMS || (THMS = await json('data/theorems.json')); }

/* ---------- code: highlighting, and names linked to their definitions ---------- */
const KW = new Set(('def theorem lemma by have show from fun let in if then else match with do return open namespace end section ' +
  'noncomputable structure inductive instance where abbrev private protected import sorry exact intro intros apply simp omega ' +
  'cases induction rfl calc obtain refine constructor unfold rw decide exists use at pub fn mut while for loop break continue ' +
  'struct enum impl true false Some None mod as Type Prop public').split(' '));
const TY = new Set('Result Std I64 I32 U8 U32 U64 Usize Isize Bool Nat Int List Slice Vec alloc Option ok fail i64 usize u8 bool ℕ ℤ'.split(' '));
const AENEAS_SRC = () => `https://github.com/AeneasVerif/aeneas/blob/${D.pins.aeneas}/backends/lean/`;
const DOCS = 'https://leanprover-community.github.io/mathlib4_docs/find/?pattern=';
let LINKS = null;
async function links() { return LINKS || (LINKS = await json('data/links.json').catch(() => ({}))); }

function localDefs(p) {                                // name -> [tab, line] for this program's own Lean
  const m = new Map();
  const scan = (text, tab) => (text || '').split('\n').forEach((l, i) => {
    const d = l.match(/^\s*(?:@\[[^\]]*\]\s*)?(?:(?:private|protected|noncomputable|partial|public)\s+)*(?:def|theorem|lemma|abbrev|structure|inductive|class)\s+([^\s:(\[{]+)/);
    if (d) { const n = d[1].split('.').pop(); if (!m.has(n)) m.set(n, [tab, i + 1]); }
  });
  scan(p.lean_funs, 'lean'); scan(p.lean_types, 'lean'); scan(p.lean_funs_external, 'lean'); scan(p.specs_file, 'specs');
  return m;
}
function ident(w, ctx) {
  const base = w.split('.').pop();
  const cls = KW.has(w) ? 'kw' : TY.has(base) || TY.has(w) ? 'ty' : '';
  if (!ctx || KW.has(w)) return cls ? `<span class="${cls}">${w}</span>` : w;
  const loc = ctx.local && (ctx.local.get(w) || (w.includes('.') && ctx.local.get(base)));
  if (loc) return `<a class="lk loc${cls ? ' ' + cls : ''}" href="#" data-go="${loc[0]}:${loc[1]}" title="Definition in this program">${w}</a>`;
  const aen = LINKS && LINKS[w];
  if (aen) return `<a class="lk aen${cls ? ' ' + cls : ''}" href="${AENEAS_SRC()}${aen}" target="_blank" rel="noopener" title="Defined in Aeneas: ${aen.replace('#L', ', line ')}">${w}</a>`;
  if (w.includes('.') && /^[A-Z]/.test(w) && !/^Aeneas\b|^Aegis\b|^AegisSpec\b/.test(w))
    return `<a class="lk ml${cls ? ' ' + cls : ''}" href="${DOCS}${encodeURIComponent(w)}" target="_blank" rel="noopener" title="Look up in the Mathlib documentation">${w}</a>`;
  return cls ? `<span class="${cls}">${w}</span>` : w;
}
function hl(src, ctx) {
  let depth = 0;                                       // inside /- ... -/ (they nest in Lean)
  return String(src ?? '').split('\n').map((line, i) => {
    let out = '', k = 0;
    while (k < line.length) {
      if (depth) {
        const o = line.indexOf('/-', k), c = line.indexOf('-/', k);
        if (c < 0 && o < 0) { out += `<span class="cm">${esc(line.slice(k))}</span>`; k = line.length; break; }
        if (o >= 0 && (c < 0 || o < c)) { out += `<span class="cm">${esc(line.slice(k, o + 2))}</span>`; depth++; k = o + 2; }
        else { out += `<span class="cm">${esc(line.slice(k, c + 2))}</span>`; depth--; k = c + 2; }
        continue;
      }
      const rest = line.slice(k);
      let m;
      if (rest.startsWith('/-')) { out += '<span class="cm">/-</span>'; depth = 1; k += 2; }
      else if (rest.startsWith('--') || rest.startsWith('//')) { out += `<span class="cm">${esc(rest)}</span>`; k = line.length; }
      else if ((m = rest.match(/^"(?:[^"\\]|\\.)*"?/))) { out += `<span class="sr">${esc(m[0])}</span>`; k += m[0].length; }
      else if ((m = rest.match(/^[A-Za-z_Ͱ-Ͽἀ-῿][\w'Ͱ-Ͽ.₀-₉]*/))) { const w = m[0].replace(/\.$/, ''); const defining = /\b(def|theorem|lemma|abbrev|structure|inductive|class|instance|fn|struct|enum)\s+$/.test(line.slice(0, k));
        out += defining ? `<span class="dn">${esc(w)}</span>` : ident(w, ctx); k += w.length; }
      else { out += esc(rest[0]); k += 1; }
    }
    return `<span class="ln" data-l="${i + 1}">${out}</span>`;
  }).join('\n');
}
const pre = (code, plain, ctx) => `<div class="prewrap"><button class="cp" data-copy="${esc(plain ?? code)}">copy</button><pre>${ctx === false ? esc(code) : hl(code, ctx)}</pre></div>`;
function toast(msg) { let t = $('toast'); if (!t) { t = document.createElement('div'); t.id = 'toast'; document.body.append(t); }
  t.textContent = msg; t.hidden = false; clearTimeout(t._h); t._h = setTimeout(() => t.hidden = true, 1600); }
document.addEventListener('click', e => {
  const go = e.target.closest('[data-go]');
  if (go && go.dataset.go.startsWith('proof')) {      // a lemma defined in the proof: its line in the proof
    e.preventDefault(); const [tab, line] = go.dataset.go.split(':');
    const det = document.querySelector(`#thm${tab.slice(5)} details.prooftext`); if (!det) return; det.open = true;
    const el = det.querySelector(`.ln[data-l="${line}"]`), sd = $('side');
    if (el) { sd.scrollTop = Math.max(0, el.getBoundingClientRect().top - sd.getBoundingClientRect().top + sd.scrollTop - 80);
      el.classList.add('flash'); setTimeout(() => el.classList.remove('flash'), 1600); }
    return;
  }
  if (go) {                                           // a name defined in this program: show its definition
    e.preventDefault(); const [tab, line] = go.dataset.go.split(':');
    renderProgram(tab, 0);
    const el = $('insp').querySelector(`.prewrap pre .ln[data-l="${line}"]`);
    if (el) { const sd = $('side'); sd.scrollTop = Math.max(0, el.getBoundingClientRect().top - sd.getBoundingClientRect().top + sd.scrollTop - 80);
      el.classList.add('flash'); setTimeout(() => el.classList.remove('flash'), 1600); }
    return;
  }
  const b = e.target.closest('[data-copy]'); if (!b) return;
  e.preventDefault(); e.stopPropagation();
  navigator.clipboard.writeText(b.dataset.copy).then(() => { if (b.classList.contains('cp')) { b.textContent = 'copied'; b.classList.add('done');
    setTimeout(() => { b.textContent = 'copy'; b.classList.remove('done'); }, 1400); } else toast('Link copied'); });
});

/* ---------- routing ---------- */
function route() {
  const h = location.hash.replace(/^#\/?/, '');
  const [path, qs] = h.split('?'); const parts = path.split('/').filter(Boolean);
  const q = new URLSearchParams(qs || '');
  const view = ['theorems', 'contribute', 'leaderboard'].includes(parts[0]) ? parts[0] : 'map';
  document.querySelectorAll('nav a').forEach(a => a.classList.toggle('on', a.dataset.v === view));
  if (parts[0] === 'p') { if (!$('view').dataset.v) renderMap(); openProgram(decodeURIComponent(parts[1]), +parts[2] || 0); return; }
  closeSide(false);
  document.title = {theorems: 'Theorems', contribute: 'Contribute', leaderboard: 'Leaderboard', map: 'Proof progress'}[view] + ' · LeetCode Rust-to-Lean';
  if (view === 'theorems') renderTheorems(q); else if (view === 'contribute') renderContribute();
  else if (view === 'leaderboard') renderLeaderboard(q); else renderMap(q);
}

/* ---------- topics: one per program, the first group (in this order) that one of its tags belongs to ---------- */
const TOPICS = [
  ['Dynamic programming', ['Dynamic Programming', 'Memoization']],
  ['Trees and linked lists', ['Tree', 'Binary Tree', 'Binary Search Tree', 'Linked List', 'Trie', 'Segment Tree', 'Binary Indexed Tree']],
  ['Graphs', ['Graph', 'Breadth-First Search', 'Depth-First Search', 'Union Find', 'Shortest Path', 'Topological Sort',
              'Minimum Spanning Tree', 'Strongly Connected Component', 'Eulerian Circuit']],
  ['Strings', ['String', 'String Matching', 'Rolling Hash', 'Hash Function', 'Suffix Array']],
  ['Math', ['Math', 'Number Theory', 'Combinatorics', 'Geometry', 'Bit Manipulation', 'Game Theory', 'Brainteaser']],
  ['Backtracking and enumeration', ['Backtracking', 'Recursion', 'Bitmask', 'Enumeration']],
  ['Stacks and queues', ['Stack', 'Monotonic Stack', 'Queue', 'Monotonic Queue']],
  ['Greedy', ['Greedy']],
  ['Searching and sorting', ['Binary Search', 'Sorting', 'Two Pointers', 'Sliding Window', 'Heap (Priority Queue)', 'Merge Sort',
    'Counting Sort', 'Quickselect', 'Bucket Sort', 'Radix Sort', 'Ordered Set', 'Line Sweep', 'Divide and Conquer']],
  ['Arrays and simulation', ['Array', 'Matrix', 'Prefix Sum', 'Simulation', 'Counting', 'Hash Table']],
];
const topicOf = p => p._topic || (p._topic = (TOPICS.find(([, tags]) => p.g.some(g => tags.includes(g))) || ['Arrays and simulation'])[0]);
const DORD = {E: 0, M: 1, H: 2};

/* ---------- map ---------- */
function resolvedOf(p) { return (p.st.match(/[pr]/g) || []).length; }
function nextUp() {                                    // one open theorem to suggest, changing daily
  const day = Math.floor(Date.now() / 864e5), pool = [];
  for (const p of D.programs) if (p.d === 'E') (p.c.match(/../g) || []).forEach((c, i) => {
    if (p.st[i] === 'o' && (c === 'no' || c === 'bo')) pool.push([p, i + 1, CAT[c]]); });
  return pool.length ? pool[(day * 2654435761 % 4294967296) % pool.length] : null;
}
function pins() {
  const P = D.pins || {};
  return `Lean <a href="https://github.com/leanprover/lean4/releases/tag/${P.lean}">${P.lean}</a> ·
    Mathlib <a href="https://github.com/leanprover-community/mathlib4/tree/${P.mathlib}"><code>${(P.mathlib || '').slice(0, 8)}</code></a> ·
    Aeneas <a href="https://github.com/AeneasVerif/aeneas/tree/${P.aeneas}"><code>${(P.aeneas || '').slice(0, 8)}</code></a> ·
    Charon <a href="https://github.com/AeneasVerif/charon/tree/${P.charon}"><code>${P.charon}</code></a> ·
    checked with <a href="https://github.com/leanprover/lean4/releases/tag/${P.lean}"><code>lake comparator</code></a>, with Lean's kernel and nanoda`;
}
function recentGroups() {                             // consecutive proofs of one program, as one line
  const out = [];
  for (const r of D.recent) { const g = out.find(x => x.t === r.t && x.by === r.by); if (g) g.ids.push(r.id); else out.push({t: r.t, by: r.by, ids: [r.id]}); }
  out.forEach(g => g.ids.sort((a, b) => a - b)); return out;
}
function rows(items, max) {                            // [label, done, total, href]
  return items.map(([l, d, n, href]) => `<a class="row" href="${href}"><span class="nm">${esc(l)}</span>
    <span class="num">${fmt(d)} / ${fmt(n)}</span><span class="rbar"><i style="width:${n ? Math.max(d ? 2 : 0, 100 * d / n) : 0}%"></i></span></a>`).join('');
}
function renderMap(q = new URLSearchParams()) {
  const v = $('view'); v.dataset.v = 'map';
  mapState.tag = q.get('tag') || ''; mapState.split = q.get('split') || ''; mapState.by = q.get('by') || 'topic';
  const T = D.totals, done = T.proved + T.refuted, pct = 100 * done / T.theorems;
  const progs = D.programs.filter(p => p.st.length);
  const mainsDone = progs.filter(p => 'pr'.includes(p.st[p.m - 1])).length;
  const full = progs.filter(p => resolvedOf(p) === p.st.length).length;
  const tags = [...new Set(D.programs.flatMap(p => p.g))].sort();
  const by = (keyOf) => { const m = new Map(); for (const p of progs) for (const [k, d, n] of keyOf(p)) { const a = m.get(k) || [0, 0]; a[0] += d; a[1] += n; m.set(k, a); } return m; };
  const byD = by(p => [[p.d, resolvedOf(p), p.st.length]]);
  const byTp = by(p => [[topicOf(p), resolvedOf(p), p.st.length]]);
  const byC = by(p => (p.c.match(/../g) || []).map((c, i) => [c, 'pr'.includes(p.st[i]) ? 1 : 0, 1]));
  const byT = by(p => p.g.map(g => [g, resolvedOf(p), p.st.length]));
  const nu = nextUp();
  v.innerHTML = `
  <div class="paperline">Unofficial reproduction of the methodology of <a href="${PAPER}"><i>Scaling Lean Theorem Proving for Real-World
    Code Verification</i></a> (<a href="${PAPER}">arXiv 2610.38174</a>), made by the paper's first author. <a href="#/" data-cite>How to cite</a></div>
  <div class="hero">
    <div>
      <div class="big">${fmt(done)} <small>of ${fmt(T.theorems)} theorems resolved</small></div>
      <div class="bar" title="${pct.toFixed(2)}% resolved"><i style="width:${100 * T.proved / T.theorems}%;background:var(--proved)"></i><i style="width:${100 * T.refuted / T.theorems}%;background:var(--refuted)"></i></div>
      <div class="figs">
        <a class="fig" href="#/theorems?status=proved"><b>${fmt(T.proved)}</b><span>proved</span></a>
        <a class="fig" href="#/theorems?status=refuted"><b>${fmt(T.refuted)}</b><span>refuted</span></a>
        <a class="fig" href="#/theorems?status=open"><b>${fmt(T.theorems - done)}</b><span>open</span></a>
        <a class="fig" href="#/theorems?status=proved&main=1"><b>${fmt(mainsDone)}</b><span>main theorems resolved</span></a>
        <div class="fig"><b>${fmt(full)}</b><span>programs fully resolved</span></div>
        <a class="fig" href="#/leaderboard"><b>${fmt(standings('team').length)}</b><span>teams on the leaderboard</span></a>
      </div>
    </div>
    <div class="lede">
      <p>Theorem provers are now very good at competition mathematics, and the benchmarks for it are close to saturated.
      Proving that real code is correct is a different and much harder problem, and it is the one that matters for software.</p>
      <p>These are ${fmt(D.programs.length)} programs and ${fmt(T.theorems)} theorems about them. Each program is a Rust solution to a LeetCode problem that passes
      every test case, translated to Lean 4 by <a href="https://github.com/AeneasVerif/aeneas">Aeneas</a>. Each theorem states one
      property of one program. A theorem is resolved when Lean's <code>lake comparator</code> accepts a proof of it, or of its negation.</p>
    </div>
  </div>
  <div class="cards">
    <div class="card"><span class="kicker">Leaderboard</span>${standings('team').slice(0, 5).map((r, i) =>
      `<a class="row" href="#/leaderboard"><span class="nm">${i + 1}. ${esc(r.name)}</span><span class="num">${fmt(r.points)} points · ${fmt(r.proved + r.refuted)} theorems</span></a>`).join('') || '<p class="sub">No proofs yet.</p>'}
      <p class="sub" style="margin:10px 0 0">Companies, labs and individuals: every proof you contribute puts your name on this board,
      ranked by points, with main theorems of Hard programs worth the most.</p>
      <a class="more" href="#/leaderboard">Full leaderboard and how points work →</a></div>
    ${nu ? `<a class="card next" href="#/p/${nu[0].t}/${nu[1]}"><span class="kicker">Next up</span>
      <b>${esc(title(nu[0].t))}, spec_${nu[1]}</b>
      <span>A ${nu[2] === 'no_failure' ? 'no-failure' : 'bounds'} theorem about an Easy program, with no proof yet: a good first proof.</span>
      <span class="go">Open it →</span></a>` : ''}
    <div class="card"><span class="kicker">Recently proved</span>${recentGroups().slice(0, 7).map(g =>
      `<a class="row" href="#/p/${g.t}/${g.ids[0]}"><span class="nm">${esc(title(g.t))}</span><span class="num">${g.ids.length === 1 ? 'spec_' + g.ids[0] : g.ids.length + ' theorems'} · ${esc(g.by)}</span></a>`).join('') || '<p class="sub">No proofs yet.</p>'}
      <a class="more" href="#/theorems?status=proved">All resolved theorems →</a></div>
  </div>
  <div class="cards two">
    <div class="card"><span class="kicker">By topic</span>${rows(TOPICS.map(([t]) => [t, ...(byTp.get(t) || [0, 0]), `#/theorems?topic=${encodeURIComponent(t)}`]))}
      <span class="kicker" style="margin-top:10px">By difficulty</span>${rows('EMH'.split('').map(d => [DIFF[d], ...(byD.get(d) || [0, 0]), `#/theorems?difficulty=${d}`]))}</div>
    <div class="card"><span class="kicker">By category</span>${rows([...byC].sort((a, b) => b[1][1] - a[1][1]).map(([c, [d, n]]) => [CAT[c], d, n, `#/theorems?category=${CAT[c]}`]))}</div>
  </div>
  ${(D.mains || []).length ? `<h2>Main theorems resolved <span class="h2n">the full correctness statement of a program, with a checked proof</span></h2>
  <div class="mains">${D.mains.map(m => `<div class="mainc"><div class="hd"><a href="#/p/${m.t}/${m.id}"><b>${esc(title(m.t))}</b></a>
    <span>${m.status} by ${esc(m.by)} · proof of ${fmt(m.lines)} lines</span></div><pre>${hl(m.stmt, {})}</pre></div>`).join('')}</div>` : ''}
  <div class="mapctl">
    <span class="legend" style="margin:0"><span><i style="background:var(--open)"></i>open</span><span><i style="background:var(--open-main)"></i>open main theorem</span>
      <span><i style="background:var(--proved)"></i>proved</span><span><i style="background:var(--refuted)"></i>refuted</span>
      <span title="The line under a block"><i class="dl" style="background:#2e9e5b"></i>Easy <i class="dl" style="background:#d99a2b"></i>Medium <i class="dl" style="background:#d23c3c"></i>Hard</span></span>
    <span style="margin-left:auto">Group by <select id="mBy"><option value="topic"${mapState.by === 'topic' ? ' selected' : ''}>topic</option><option value="difficulty"${mapState.by === 'difficulty' ? ' selected' : ''}>difficulty</option></select></span>
    <span>Tag <select id="mTag"><option value="">all</option>${tags.map(t => `<option${t === mapState.tag ? ' selected' : ''}>${esc(t)}</option>`).join('')}</select></span>
    <span>Split <select id="mSplit"><option value="">all</option><option value="te"${mapState.split === 'te' ? ' selected' : ''}>test</option><option value="tr"${mapState.split === 'tr' ? ' selected' : ''}>train</option></select></span>
  </div>
  <div id="maps"></div>
  <h2>LeetCode tags <span class="h2n">a program has several; click one to show its programs on the map</span></h2>
  <div class="topics">${rows([...byT].sort((a, b) => b[1][1] - a[1][1]).map(([g, [d, n]]) => [g, d, n, `#/?tag=${encodeURIComponent(g)}`]))}</div>
  ${citeHtml()}
  <h2>Reading the map</h2>
  <p class="hint">One square per theorem, one block per program. Programs are grouped by topic, each in the first topic (in the order
  shown) that one of its LeetCode tags belongs to, and within a topic ordered from Easy to Hard; the darker square of a
  block is the program's main theorem. Hover a block for its name and click it to open the program. <kbd>/</kbd> search · <kbd>m</kbd> map ·
  <kbd>t</kbd> theorems · <kbd>c</kbd> contribute · in a program, <kbd>j</kbd> <kbd>k</kbd> next and previous theorem,
  <kbd>[</kbd> <kbd>]</kbd> previous and next program · <kbd>Esc</kbd> close.</p>
  <div class="foot">${pins()}<br>Built ${esc(D.built)} from commit <code>${esc(D.commit || '')}</code> ·
    Data: <a href="${DATASET}">Hugging Face</a> · Paper: <a href="https://arxiv.org/abs/2610.38174">arXiv 2610.38174</a> (unofficial reproduction).</div>`;
  const setQ = () => { const n = new URLSearchParams(); if (mapState.tag) n.set('tag', mapState.tag); if (mapState.split) n.set('split', mapState.split);
    if (mapState.by !== 'topic') n.set('by', mapState.by);
    history.replaceState(null, '', '#/' + (String(n) ? '?' + n : '')); drawMaps(); };
  $('mTag').onchange = e => { mapState.tag = e.target.value; setQ(); };
  $('mSplit').onchange = e => { mapState.split = e.target.value; setQ(); };
  $('mBy').onchange = e => { mapState.by = e.target.value; setQ(); };
  drawMaps();
  v.querySelector('[data-cite]').onclick = e => { e.preventDefault(); $('cite').scrollIntoView({behavior: 'smooth', block: 'start'}); };
  if (mapState.tag) $('maps').scrollIntoView({block: 'start'});
}

let maps = [];
function drawMaps() {
  const box = $('maps'); if (!box) return;
  box.innerHTML = ''; maps = [];
  const groups = mapState.by === 'difficulty'
    ? 'EMH'.split('').map(d => [DIFF[d], D.programs.filter(p => p.d === d && p.st.length)])
    : TOPICS.map(([t]) => [t, D.programs.filter(p => p.st.length && topicOf(p) === t).sort((a, b) => DORD[a.d] - DORD[b.d] || (a.t < b.t ? -1 : 1))]);
  for (const [name, ps] of groups) {
    if (!ps.length) continue;
    const n = ps.reduce((a, p) => a + p.st.length, 0), dn = ps.reduce((a, p) => a + resolvedOf(p), 0);
    const h = document.createElement('h2'); h.textContent = `${name}  ·  ${fmt(ps.length)} programs  ·  ${fmt(dn)} of ${fmt(n)} resolved`;
    if (mapState.by === 'topic') h.title = 'Programs whose tags include: ' + TOPICS.find(x => x[0] === name)[1].join(', ') + ' (each program is in one topic: the first in this order that one of its tags belongs to)';
    const c = document.createElement('canvas'); c.className = 'map'; c.setAttribute('role', 'img');
    c.setAttribute('aria-label', `Map of the ${name} programs: ${fmt(dn)} of ${fmt(n)} theorems resolved. The theorem list gives the same information as text.`);
    box.append(h, c); maps.push({c, ps}); layout(maps[maps.length - 1]);
  }
}
function matches(p) {
  return (!mapState.tag || p.g.includes(mapState.tag)) && (!mapState.split || p.s === mapState.split) &&
         (!mapState.q || p.t.includes(mapState.q));
}
function layout(m) {
  const W = m.c.parentElement.clientWidth, S = 6, G = 1, PAD = 4, dpr = window.devicePixelRatio || 1;
  let x = 0, y = 0, rowH = 0; m.rects = [];
  for (const p of m.ps) {
    const k = p.st.length, w = Math.ceil(Math.sqrt(k)), hgt = Math.ceil(k / w);
    const bw = w * (S + G), bh = hgt * (S + G);
    if (x + bw > W) { x = 0; y += rowH + PAD; rowH = 0; }
    m.rects.push({p, x, y, w, bw, bh}); x += bw + PAD; rowH = Math.max(rowH, bh);
  }
  const H = y + rowH + 2;
  m.c.width = W * dpr; m.c.height = H * dpr; m.c.style.height = H + 'px';
  const g = m.c.getContext('2d'); g.scale(dpr, dpr);
  const col = {o: css('--open'), om: css('--open-main'), p: css('--proved'), r: css('--refuted'), x: css('--conflict')};
  for (const r of m.rects) {
    g.globalAlpha = matches(r.p) ? 1 : 0.18;
    for (let i = 0; i < r.p.st.length; i++) {
      const s = r.p.st[i];
      g.fillStyle = s === 'o' && i === r.p.m - 1 ? col.om : col[s];
      g.fillRect(r.x + (i % r.w) * (S + G), r.y + Math.floor(i / r.w) * (S + G), S, S);
    }
    g.globalAlpha = matches(r.p) ? 0.75 : 0.15;                 // difficulty, as a line under the block
    g.fillStyle = {E: '#2e9e5b', M: '#d99a2b', H: '#d23c3c'}[r.p.d]; g.fillRect(r.x, r.y + r.bh, r.bw - G, 1.5);
    if (cur && cur.task_id === r.p.t) { g.globalAlpha = 1; g.strokeStyle = css('--accent'); g.lineWidth = 2; g.strokeRect(r.x - 2, r.y - 2, r.bw + 3, r.bh + 3); }
  }
  m.c.onmousemove = e => { const r = hit(m, e); const tip = $('tip'), hb = hoverBox(m);
    if (!r) { tip.hidden = true; hb.hidden = true; m.c.style.cursor = 'default'; return; }
    m.c.style.cursor = 'pointer';
    hb.hidden = false; hb.style.left = (r.x - 2) + 'px'; hb.style.top = (m.c.offsetTop + r.y - 2) + 'px';
    hb.style.width = (r.bw + 3) + 'px'; hb.style.height = (r.bh + 3) + 'px';
    const n = r.p.st.length, dn = resolvedOf(r.p), i = cellAt(m, r, e);
    const cell = i >= 0 ? `<br>spec_${i + 1} · ${CAT[r.p.c.substr(2 * i, 2)]}${i === r.p.m - 1 ? ' · main' : ''} · ${STATUS[r.p.st[i]]}` : '';
    tip.innerHTML = `<b>${esc(title(r.p.t))}</b><br><small>#${r.p.q} · ${dn} of ${n} resolved${cell}</small>`;
    tip.hidden = false; tip.style.left = Math.min(e.clientX + 14, innerWidth - 370) + 'px'; tip.style.top = e.clientY + 14 + 'px'; };
  m.c.onmouseleave = () => { $('tip').hidden = true; hoverBox(m).hidden = true; };
  m.c.onclick = e => { const r = hit(m, e); if (!r) return; const i = cellAt(m, r, e); location.hash = '#/p/' + r.p.t + (i >= 0 ? '/' + (i + 1) : ''); };
}
const CELL = 7;                                        // square plus gap, as in layout()
function cellAt(m, r, e) {
  const b = m.c.getBoundingClientRect(), x = e.clientX - b.left - r.x, y = e.clientY - b.top - r.y;
  if (x < 0 || y < 0) return -1;
  const i = Math.floor(y / CELL) * r.w + Math.floor(x / CELL);
  return Math.floor(x / CELL) < r.w && i < r.p.st.length ? i : -1;
}
function hoverBox(m) {
  if (!m.hb) { m.hb = document.createElement('div'); m.hb.className = 'hoverbox'; m.hb.hidden = true; m.c.parentElement.append(m.hb); }
  return m.hb;
}
function hit(m, e) {
  const b = m.c.getBoundingClientRect(), x = e.clientX - b.left, y = e.clientY - b.top;
  return m.rects.find(r => x >= r.x - 2 && x <= r.x + r.bw + 2 && y >= r.y - 2 && y <= r.y + r.bh + 2);
}
window.addEventListener('resize', () => maps.forEach(layout));

/* ---------- program structure: declarations and how they depend on each other ---------- */
const DECL_RE = /^\s*(?:@\[[^\]]*\]\s*)?(?:(?:private|protected|noncomputable|partial|public)\s+)*(def|theorem|lemma|abbrev|structure|inductive|class|instance)\s+([^\s:(\[{]+)/;
function structure(p) {                              // declarations of the program's Lean, with references
  if (p._st) return p._st;
  const decls = [];
  const scan = (text, file, tab) => {
    const lines = (text || '').split('\n'); let open = null;
    lines.forEach((l, i) => {
      const m = l.match(DECL_RE);
      if (m && /^\s*(?:@|private|protected|noncomputable|partial|public|def|theorem|lemma|abbrev|structure|inductive|class|instance)/.test(l) && (l.length - l.trimStart().length) <= 2) {
        if (open) open.end = i;
        const name = m[2].replace(/^(Aegis|AegisSpec)\.[A-Za-z0-9_]+\./, '');
        if (/_neg$/.test(name)) { open = null; return; }
        open = {name, full: m[2], kind: m[1], file, tab, line: i + 1, end: lines.length};
        decls.push(open);
      } else if (open && /^\s*(?:namespace|end|section|open|set_option|\/-!)\b/.test(l) && !/^\s{4}/.test(l)) { open.end = i; open = null; }
    });
    decls.filter(d => d.file === file).forEach(d => {   // without the next declaration's docstring or attributes
      d.text = lines.slice(d.line - 1, d.end).join('\n').replace(/(\n\s*(\/--(?:(?!-\/)[\s\S])*-\/|@\[[^\]]*\]|--[^\n]*)?)+\s*$/, ''); });
  };
  scan(p.lean_types, 'Types.lean', 'lean'); scan(p.lean_funs, 'Funs.lean', 'lean');
  scan(p.lean_funs_external, 'FunsExternal.lean', 'lean'); scan(p.specs_file, 'Specs.lean', 'specs');
  const byName = new Map(), last = {};
  decls.forEach((d, i) => { byName.set(d.name, i); byName.set(d.full, i); const l = d.name.split('.').pop(); last[l] = last[l] === undefined ? i : -1; });
  Object.entries(last).forEach(([l, i]) => { if (i >= 0 && !byName.has(l)) byName.set(l, i); });
  const find = w => { const parts = w.split('.'); for (let k = 0; k < parts.length; k++) { const j = byName.get(parts.slice(k).join('.')); if (j !== undefined) return j; } };
  decls.forEach((d, i) => {
    d.role = d.file === 'Specs.lean' ? (/^spec_\d+$/.test(d.name) ? 'theorem' : 'helper') : d.file === 'FunsExternal.lean' ? 'external' : 'program';
    if (d.role === 'theorem') d.thm = p.theorems.find(t => `spec_${t.id}` === d.name);
    const body = d.text.replace(/--[^\n]*|\/-[\s\S]*?-\//g, '');
    d.uses = [...new Set((body.match(/[A-Za-z_][\w'.]*[\w']/g) || []).map(find).filter(j => j !== undefined && j !== i))];
  });
  decls.forEach((d, i) => d.usedBy = decls.map((e, j) => e.uses.includes(i) ? j : -1).filter(j => j >= 0));
  return (p._st = decls);
}
function closure(decls, i, key) {                    // everything reachable along `uses` or `usedBy`
  const seen = new Set(), stack = [...decls[i][key]];
  while (stack.length) { const j = stack.pop(); if (!seen.has(j) && j !== i) { seen.add(j); stack.push(...decls[j][key]); } }
  return seen;
}
let stSel = -1, stTrans = true;
const ROLE = {program: 'program code', external: 'library model', helper: 'helper definition', theorem: 'theorem'};
function renderStructure(p) {
  const ds = structure(p);
  const lines = t => (t || '').split('\n').length;
  const nTh = ds.filter(d => d.role === 'theorem').length, nHelp = ds.filter(d => d.role === 'helper').length;
  const nFun = ds.filter(d => d.role === 'program' && d.file === 'Funs.lean').length;
  const sel = stSel >= 0 && stSel < ds.length ? stSel : -1;
  const dep1 = new Set(sel >= 0 ? ds[sel].uses : []), use1 = new Set(sel >= 0 ? ds[sel].usedBy : []);
  const depT = sel >= 0 && stTrans ? closure(ds, sel, 'uses') : new Set(), useT = sel >= 0 && stTrans ? closure(ds, sel, 'usedBy') : new Set();
  const rel = j => j === sel ? 'r-sel' : dep1.has(j) ? 'r-dep' : use1.has(j) ? 'r-use' : depT.has(j) ? 'r-dep2' : useT.has(j) ? 'r-use2' : '';
  const dot = d => d.role === 'theorem' ? `k-${d.thm ? d.thm.status : 'open'}` : `k-${d.role}`;
  let h = `<div class="stats">${[[lines(p.rust), 'lines of Rust'], [lines(p.lean_funs), 'lines of Lean'], [nFun, 'functions'],
    [nHelp, 'helper definitions'], [nTh, 'theorems'], [p.num_test_cases, 'test cases']].map(([n, l]) => `<div><b>${fmt(n)}</b><span>${l}</span></div>`).join('')}</div>
    <div class="slegend"><span><i class="k-program"></i>program code</span><span><i class="k-helper"></i>helper definition</span>
      <span><i class="k-open"></i>theorem</span><span><i class="k-proved"></i>proved</span>${sel >= 0 ? `<span class="sep"></span>
      <span><i class="r-dep"></i>it depends on</span><span><i class="r-dep2"></i>… indirectly</span><span><i class="r-use"></i>depends on it</span><span><i class="r-use2"></i>… indirectly</span>` : ''}
      <label class="tr" title="Also shade what is reached through other declarations"><input type="checkbox" id="stTrans"${stTrans ? ' checked' : ''}> transitive</label></div>`;
  if (sel >= 0) {
    const d = ds[sel];
    h += `<div class="ssel"><div class="hd"><span class="kdot ${dot(d)}"></span><b>${esc(d.full)}</b><span>${d.file}:${d.line} · ${ROLE[d.role]}${d.thm ? ' · ' + d.thm.status : ''}</span></div>
      <div class="sub">depends on ${fmt(dep1.size)}${stTrans ? ` (${fmt(depT.size)} in all)` : ''} · used by ${fmt(use1.size)}${stTrans ? ` (${fmt(useT.size)} in all)` : ''}
        ${d.thm ? ` · <a href="#/p/${p.task_id}/${d.thm.id}">open the theorem</a>` : ''}</div>
      ${pre(d.text, null, {local: localDefs(p)})}</div>`;
  } else h += `<p class="hint">Select a declaration to see what it depends on and what depends on it. A theorem depends on the functions
    and definitions its statement mentions; a function on the functions it calls.</p>`;
  let file = '';
  h += '<div class="decls">';
  ds.forEach((d, j) => {
    if (d.file !== file) { file = d.file; h += `<div class="fhd">${file}</div>`; }
    h += `<a href="#" class="drow ${rel(j)}" data-d="${j}"><span class="kdot ${dot(d)}"></span><span class="nm">${esc(d.name)}</span>
      <span class="wh">${d.role === 'theorem' && d.thm ? esc(d.thm.category) + (d.thm.main ? ' · main' : '') : d.kind}</span><span class="num">${d.line}</span></a>`;
  });
  return h + '</div>';
}
function bindStructure() {
  $('insp').querySelectorAll('.drow').forEach(a => a.onclick = e => { e.preventDefault(); const j = +a.dataset.d; stSel = stSel === j ? -1 : j; renderProgram('structure', 0); });
  const t = $('stTrans'); if (t) t.onchange = () => { stTrans = t.checked; renderProgram('structure', 0); };
}
function usesLine(p, t) {                            // the declarations a theorem's statement mentions
  const ds = structure(p), i = ds.findIndex(d => d.name === `spec_${t.id}`);
  if (i < 0 || !ds[i].uses.length) return '';
  return `<p class="uses">Uses ${ds[i].uses.map(j => `<a href="#" class="usechip" data-sd="${j}"><span class="kdot k-${ds[j].role}"></span>${esc(ds[j].name)}</a>`).join(' ')}</p>`;
}

/* ---------- program inspector ---------- */
async function openProgram(task, n) {
  const side = $('side'); side.hidden = false; $('main').classList.add('split');
  if (!cur || cur.task_id !== task) {
    if (!BY[task]) { cur = null; $('insp').innerHTML = `<h1>No such program</h1><p class="sub"><code>${esc(task)}</code> is not one of the programs. Try the search box.</p>`; return; }
    $('insp').innerHTML = '<p class="sub">Loading…</p>'; side.dataset.tab = 'theorems'; tfilt = 'all'; stSel = -1;
    [cur] = await Promise.all([json(`data/p/${encodeURIComponent(task)}.json`), links()]); side.scrollTop = 0; }
  document.title = `${title(task)} · LeetCode Rust-to-Lean`;
  maps.forEach(layout);
  const tab = n ? 'theorems' : (side.dataset.tab || 'theorems');
  renderProgram(tab, n);
}
function closeSide(push = true) { $('side').hidden = true; $('main').classList.remove('split'); cur = null; maps.forEach(layout); if (push && location.hash.startsWith('#/p/')) history.replaceState(null, '', '#/'); }
let tfilt = 'all';
function neighbours(task) {
  const ps = D.programs.filter(p => p.st.length), i = ps.findIndex(p => p.t === task);
  return [ps[(i - 1 + ps.length) % ps.length].t, ps[(i + 1) % ps.length].t];
}
function renderProgram(tab, sel) {
  const p = cur, side = $('side'); side.dataset.tab = tab; side.dataset.sel = sel || '';
  const done = p.theorems.filter(t => t.status === 'proved' || t.status === 'refuted').length;
  const tabs = [['theorems', `Theorems (${p.theorems.length})`], ['structure', 'Structure'], ['problem', 'Problem'], ['rust', 'Rust'], ['lean', 'Lean'], ['specs', 'Specs.lean']];
  const [prv, nxt] = neighbours(p.task_id);
  let body = '';
  const ctx = {local: localDefs(p)};
  if (tab === 'theorems') {
    const shown = p.theorems.filter(t => tfilt === 'all' || (tfilt === 'open' ? t.status === 'open' : t.status !== 'open'));
    body = !p.theorems.length ? '<p class="sub">This program has no theorems yet.</p>' :
      `<div class="tfilter">${[['all', 'All', p.theorems.length], ['open', 'Open', p.theorems.length - done], ['done', 'Resolved', done]]
        .map(([k, l, n]) => `<button data-f="${k}" class="${k === tfilt ? 'on' : ''}">${l} ${n}</button>`).join('')}</div>` +
      (shown.map(t => thmCard(p, t, t.id === sel, ctx)).join('') || '<p class="sub">None.</p>');
  }
  if (tab === 'structure') body = renderStructure(p);
  if (tab === 'problem') body = `<div class="desc">${esc(p.description)}</div><p class="sub">Signature: <code>${esc(p.rust_signature)}</code> · ${p.num_test_cases} test cases</p>`;
  if (tab === 'rust') body = pre(p.rust);
  if (tab === 'lean') body = `<p class="sub">The Aeneas translation (<code>Funs.lean</code>). Names link to their definitions:
      <span class="lk loc">in this program</span>, <span class="lk aen">in Aeneas</span>, <span class="lk ml">in Mathlib and Lean</span>.</p>${pre(p.lean_funs, null, ctx)}
    <details open><summary>Types.lean</summary>${pre(p.lean_types, null, ctx)}</details>` +
    (p.lean_funs_external ? `<details open><summary>FunsExternal.lean (trusted models of Rust library functions)</summary>${pre(p.lean_funs_external, null, ctx)}</details>` : '');
  if (tab === 'specs') body = `<p class="sub">The challenge file: every theorem and its negation, each with <code>sorry</code>. <a href="${REPO}/blob/main/programs/${p.task_id}/Specs.lean">On GitHub</a>.</p>${pre(p.specs_file, null, ctx)}`;
  $('insp').innerHTML = `
    <div class="pnav"><a href="#/p/${prv}" title="Previous program ( [ )">‹ previous</a><a href="#/p/${nxt}" title="Next program ( ] )">next ›</a></div>
    <h1>${esc(title(p.task_id))}</h1>
    <div class="sub"><a class="chip topic" href="#/theorems?topic=${encodeURIComponent(topicOf(BY[p.task_id]))}">${esc(topicOf(BY[p.task_id]))}</a><span class="chip ${p.difficulty[0]}">${p.difficulty}</span><span class="chip">#${p.question_id}</span><span class="chip">${p.split}</span>
      ${p.tags.map(t => `<a class="chip" href="#/?tag=${encodeURIComponent(t)}">${esc(t)}</a>`).join('')}
      <br>${done} of ${p.theorems.length} theorems resolved · <a href="https://leetcode.com/problems/${p.task_id}/">LeetCode</a> · <a href="${REPO}/tree/main/programs/${p.task_id}"><code>programs/${esc(p.task_id)}</code></a></div>
    <div class="tabs">${tabs.map(([k, l]) => `<a href="#" data-tab="${k}" class="${k === tab ? 'on' : ''}">${l}</a>`).join('')}</div>
    ${body}`;
  $('insp').querySelectorAll('.tabs a').forEach(a => a.onclick = e => { e.preventDefault(); renderProgram(a.dataset.tab, 0); });
  if (tab === 'structure') bindStructure();
  $('insp').querySelectorAll('[data-pl]').forEach(a => a.onclick = e => { e.preventDefault();
    const card = document.getElementById('thm' + a.dataset.t), det = card.querySelector('details.prooftext'); det.open = true;
    const el = det.querySelector(`.ln[data-l="${a.dataset.pl}"]`), sd = $('side');
    if (el) { sd.scrollTop = Math.max(0, el.getBoundingClientRect().top - sd.getBoundingClientRect().top + sd.scrollTop - 80);
      el.classList.add('flash'); setTimeout(() => el.classList.remove('flash'), 1600); } });
  $('insp').querySelectorAll('.usechip').forEach(a => a.onclick = e => { e.preventDefault(); stSel = +a.dataset.sd; renderProgram('structure', 0); });
  $('insp').querySelectorAll('.tfilter button').forEach(b => b.onclick = () => { tfilt = b.dataset.f; renderProgram('theorems', sel); });
  if (sel) { const el = document.getElementById('thm' + sel), sd = $('side');
    if (el) sd.scrollTop = Math.max(0, el.offsetTop - sd.clientHeight / 3); }
}
function proofCtx(t, ctx) {                           // names a proof defines link to their line in the proof
  const local = new Map(ctx ? ctx.local : []);
  t.proof.text.split('\n').forEach((l, i) => { const m = l.match(DECL_RE);
    if (m) local.set(m[2].split('.').pop(), ['proof' + t.id, i + 1]); });
  return {local};
}
function proofOutline(p, t) {                         // the lemmas a proof adds, and which of them each one uses
  const known = new Set(structure(p).map(d => d.name));
  const lines = t.proof.text.split('\n'), decls = [];
  lines.forEach((l, i) => { const m = l.match(DECL_RE);
    if (m && (l.length - l.trimStart().length) <= 2) { const name = m[2].replace(/^(Aegis|AegisSpec)\.[A-Za-z0-9_]+\./, '');
      if (decls.length) decls[decls.length - 1].end = i;
      decls.push({name, kind: m[1], line: i + 1, end: lines.length}); } });
  const own = decls.filter(d => !known.has(d.name) && !/^spec_\d+(_neg)?$/.test(d.name) && d.name !== 'draft_placeholder');
  if (own.length < 2) return '';
  const names = new Map(own.map((d, i) => [d.name.split('.').pop(), i]));
  own.forEach(d => { const body = lines.slice(d.line, d.end).join('\n');
    d.uses = [...new Set((body.match(/[A-Za-z_][\w'.]*/g) || []).map(w => names.get(w.split('.').pop())))].filter(j => j !== undefined && own[j] !== d); });
  const usedBy = own.map((_, j) => own.filter(d => d.uses.includes(j)).length);
  return `<details><summary>Proof outline: ${own.length} lemmas and definitions</summary>
    <p class="hint">In the order of the proof file; the theorem itself comes last. Click a name to see it in the proof.</p>
    <div class="decls">${own.map((d, j) => `<a href="#" class="drow" data-pl="${d.line}" data-t="${t.id}"><span class="kdot k-${d.kind === 'def' || d.kind === 'abbrev' ? 'helper' : 'proved'}"></span>
      <span class="nm">${esc(d.name)}</span><span class="wh">${d.end - d.line + 1} lines${d.uses.length ? ` · uses ${d.uses.length}` : ''}${usedBy[j] ? ` · used by ${usedBy[j]}` : ''}</span><span class="num">${d.line}</span></a>`).join('')}</div></details>`;
}
function thmCard(p, t, sel, ctx) {
  const task = p.task_id, f = `programs/${task}/Proofs/spec_${t.id}.lean`;
  const link = location.href.split('#')[0] + `#/p/${task}/${t.id}`;
  const cmds = `python3 tools/new_proof.py ${task} ${t.id}        # add --negation to refute it\n# prove spec_${t.id} in ${f}, then\npython3 tools/check.py proof ${f}`;
  const proof = t.proof ? `<p class="sub">${t.status === 'refuted' ? 'Refuted' : 'Proved'} by <b>${esc(t.proof.by)}</b>, checked by <code>lake comparator</code> on ${esc(t.proof.checked)} · <a href="${REPO}/blob/main/${t.proof.file}">on GitHub</a></p>
      ${proofOutline(p, t)}
      <details class="prooftext"><summary>Show the proof (${t.proof.text.split('\n').length} lines)</summary>${pre(t.proof.text, null, proofCtx(t, ctx))}</details>` :
    `<details><summary>Work on this theorem</summary>${pre(cmds, null, false)}</details>`;
  const lean = (p.specs_file.match(new RegExp(`theorem spec_${t.id} [\\s\\S]*?:= by\\s*\\n\\s*sorry`)) || [''])[0];
  const neg = (p.specs_file.match(new RegExp(`theorem spec_${t.id}_neg [\\s\\S]*?:= by\\s*\\n\\s*sorry`)) || [''])[0];
  return `<div class="thm${sel ? ' sel' : ''}" id="thm${t.id}" data-n="${t.id}">
    <div class="hd"><b>spec_${t.id}</b><span>${t.category}</span>${t.main ? '<span class="chip">main</span>' : ''}
      <button class="lnk" data-copy="${esc(link)}" title="Copy a link to this theorem">#</button><span class="st ${t.status}">${t.status}</span></div>
    <p>${esc(t.statement)}</p>${t.preconditions ? `<p class="pre">Preconditions: ${esc(t.preconditions)}</p>` : ''}
    ${usesLine(p, t)}
    <details${sel ? ' open' : ''}><summary>Lean statement</summary>${pre(lean, null, ctx)}</details>
    <details><summary>Negation</summary>${pre(neg, null, ctx)}</details>
    ${proof}</div>`;
}
$('close').onclick = () => closeSide();
document.addEventListener('keydown', e => {
  if (e.target.tagName === 'INPUT' || e.target.tagName === 'SELECT' || e.metaKey || e.ctrlKey || e.altKey) return;
  const open = !$('side').hidden && cur;
  if (e.key === 'Escape' && open) closeSide();
  else if (e.key === '/') { e.preventDefault(); $('search').focus(); $('search').select(); }
  else if (e.key === 'm') location.hash = '#/';
  else if (e.key === 't') location.hash = '#/theorems';
  else if (e.key === 'c') location.hash = '#/contribute';
  else if (e.key === 'l') location.hash = '#/leaderboard';
  else if (open && (e.key === '[' || e.key === ']')) { const [a, b] = neighbours(cur.task_id); location.hash = '#/p/' + (e.key === '[' ? a : b); }
  else if (open && (e.key === 'j' || e.key === 'k')) {
    const ids = [...$('insp').querySelectorAll('.thm')].map(x => +x.dataset.n); if (!ids.length) return;
    const i = ids.indexOf(+$('side').dataset.sel || 0), n = ids[e.key === 'j' ? Math.min(ids.length - 1, i + 1) : Math.max(0, i - 1)];
    history.replaceState(null, '', `#/p/${cur.task_id}/${n}`); renderProgram('theorems', n);
  }
});

/* ---------- theorem list ---------- */
async function renderTheorems(q) {
  const v = $('view'); v.dataset.v = 'theorems'; v.innerHTML = '<p class="sub">Loading…</p>';
  const rows = await theorems();
  const f = {st: q.get('status') || '', d: q.get('difficulty') || '', c: q.get('category') || '', main: q.get('main') || '',
             s: q.get('split') || '', tp: q.get('topic') || '', text: q.get('q') || '', page: +q.get('page') || 0};
  const out = rows.filter(r => { const p = BY[r[0]];
    return (!f.st || STATUS[r[4]] === f.st) && (!f.d || p.d === f.d) && (!f.c || CAT[r[2]] === f.c) && (!f.main || r[3]) &&
           (!f.s || p.s === f.s) && (!f.tp || topicOf(p) === f.tp) && (!f.text || (r[0] + ' ' + r[5]).toLowerCase().includes(f.text.toLowerCase())); });
  const per = 100, pages = Math.max(1, Math.ceil(out.length / per)), pg = Math.min(f.page, pages - 1);
  const sel = (k, opts, val) => `<select data-k="${k}"><option value="">${k}: all</option>${opts.map(([a, b]) => `<option value="${a}"${a === val ? ' selected' : ''}>${b}</option>`).join('')}</select>`;
  v.innerHTML = `<div class="filters">
      ${sel('status', [['open', 'open'], ['proved', 'proved'], ['refuted', 'refuted']], f.st)}
      ${sel('topic', TOPICS.map(([t]) => [t, t]), f.tp)}
      ${sel('difficulty', [['E', 'Easy'], ['M', 'Medium'], ['H', 'Hard']], f.d)}
      ${sel('category', Object.values(CAT).map(c => [c, c]), f.c)}
      ${sel('split', [['te', 'test'], ['tr', 'train']], f.s)}
      <label><input type="checkbox" data-k="main"${f.main ? ' checked' : ''}> main theorems only</label>
      <input type="search" data-k="q" placeholder="filter text" value="${esc(f.text)}">
      <span style="color:var(--muted)">${fmt(out.length)} theorems</span></div>
    <div class="tw"><table class="list"><thead><tr><th>Program</th><th>Theorem</th><th>Statement</th><th>Status</th></tr></thead><tbody>
    ${out.slice(pg * per, pg * per + per).map(r => `<tr data-t="${r[0]}" data-n="${r[1]}"><td><a href="#/p/${r[0]}/${r[1]}">${esc(title(r[0]))}</a><br><span class="chip ${BY[r[0]].d}">${DIFF[BY[r[0]].d]}</span></td>
      <td class="n">spec_${r[1]}<br><small style="color:var(--muted)">${CAT[r[2]]}${r[3] ? ' · main' : ''}</small></td>
      <td>${esc(r[5])}</td><td><span class="st ${STATUS[r[4]]}">${STATUS[r[4]]}</span>${r[6] ? `<br><small style="color:var(--muted)">${esc(r[6])}</small>` : ''}</td></tr>`).join('')}
    </tbody></table></div>
    <div class="pager"><button id="prev"${pg ? '' : ' disabled'}>‹ prev</button> page ${pg + 1} of ${pages} <button id="next"${pg < pages - 1 ? '' : ' disabled'}>next ›</button></div>`;
  const go = (k, val) => { const n = new URLSearchParams(q); if (val) n.set(k, val); else n.delete(k); if (k !== 'page') n.delete('page'); location.hash = '#/theorems?' + n; };
  v.querySelectorAll('select').forEach(s => s.onchange = () => go(s.dataset.k, s.value));
  v.querySelector('input[data-k=main]').onchange = e => go('main', e.target.checked ? '1' : '');
  v.querySelector('input[data-k=q]').onchange = e => go('q', e.target.value);
  $('prev').onclick = () => go('page', pg - 1); $('next').onclick = () => go('page', pg + 1);
  v.querySelectorAll('tbody tr').forEach(tr => tr.onclick = () => { location.hash = `#/p/${tr.dataset.t}/${tr.dataset.n}`; });
}

/* ---------- leaderboard ---------- */
const BOARDS = {team: ['Teams', c => c.org || c.by, 'An organization, or the contributor when a proof names none'],
                contributor: ['Contributors', c => c.by, 'The person or account credited in the proof'],
                system: ['Systems', c => c.system || null, 'The prover or model that found the proof, when the proof names one']};
function standings(key) {
  const m = new Map();
  for (const c of D.credits || []) {
    const k = BOARDS[key][1](c); if (!k) continue;
    const r = m.get(k) || {name: k, points: 0, proved: 0, refuted: 0, main: 0, E: 0, M: 0, H: 0, first: c.date, last: c.date, orgs: new Set()};
    r.points += c.points; r[c.kind] += 1; r.main += c.main ? 1 : 0; r[c.d] += 1;
    if (c.date < r.first) r.first = c.date; if (c.date > r.last) r.last = c.date;
    if (c.org) r.orgs.add(c.org);
    m.set(k, r);
  }
  return [...m.values()].sort((a, b) => b.points - a.points || b.main - a.main || (a.first < b.first ? -1 : 1));
}
function lbChart(rows, key) {                         // cumulative points over time for the leaders
  const top = rows.slice(0, 6).map(r => r.name), dates = [...new Set((D.credits || []).map(c => c.date))].sort();
  if (dates.length < 2 || !top.length) return '';
  const W = 860, H = 220, P = 34, R = 150, xs = d => P + (W - P - R) * dates.indexOf(d) / (dates.length - 1);
  const series = top.map(n => { let acc = 0; return dates.map(d => (acc += (D.credits || []).filter(c => c.date === d && BOARDS[key][1](c) === n).reduce((a, c) => a + c.points, 0))); });
  const max = Math.max(1, ...series.flat()), ys = v => H - P - (H - 2 * P) * v / max;
  const COL = ['#2f6fd8', '#2e9e5b', '#d99a2b', '#d23c3c', '#7b5cd6', '#2a9db0'];
  return `<svg class="lbchart" viewBox="0 0 ${W} ${H}" role="img" aria-label="Points over time for the leaders">
    <line x1="${P}" y1="${H - P}" x2="${W - R}" y2="${H - P}" class="ax"/><text x="${P}" y="${H - 10}" class="tk">${dates[0]}</text>
    <text x="${W - R}" y="${H - 10}" class="tk" text-anchor="end">${dates[dates.length - 1]}</text><text x="${P - 6}" y="${P}" class="tk" text-anchor="end">${fmt(max)}</text>
    ${series.map((v, i) => `<polyline fill="none" stroke="${COL[i]}" stroke-width="2" points="${v.map((y, j) => `${xs(dates[j])},${ys(y)}`).join(' ')}"/>
      <text x="${W - R + 6}" y="${ys(v[v.length - 1]) + 4}" class="tk" fill="${COL[i]}">${esc(top[i].length > 22 ? top[i].slice(0, 21) + '…' : top[i])}</text>`).join('')}</svg>`;
}
function orgMark(r, key) {                           // confirmed organizations get a check and a link
  const v = (D.verified_orgs || {})[r.name];
  if (key !== 'team' || ![...(D.credits || [])].some(c => c.org === r.name)) return '';
  return v ? ` <a class="vmark" href="${esc(v.url || '#')}" title="Confirmed by a maintainer">✓</a>` : ' <small class="muted" title="Organization names are self-reported until confirmed">self-reported</small>';
}
function renderLeaderboard(q) {
  const v = $('view'); v.dataset.v = 'leaderboard';
  const key = BOARDS[q.get('by')] ? q.get('by') : 'team', rows = standings(key);
  const total = rows.reduce((a, r) => a + r.points, 0) || 1;
  v.innerHTML = `<div class="prose wide">
    <h1>Leaderboard</h1>
    <p>Every theorem resolved here was accepted by <code>lake comparator</code>: same statement, no <code>sorry</code>, standard axioms only,
    checked by Lean's kernel and nanoda. Each theorem is credited once, to the first proof of it, and the credit stays.</p>
    <div class="tabs">${Object.entries(BOARDS).map(([k, [l]]) => `<a href="#/leaderboard?by=${k}" class="${k === key ? 'on' : ''}">${l}</a>`).join('')}</div>
    <p class="hint">${BOARDS[key][2]}.</p>
    ${rows.length ? `<div class="tw"><table class="list lb"><thead><tr><th>#</th><th>${BOARDS[key][0].replace(/s$/, '')}</th><th>Points</th><th>Resolved</th>
      <th>Main theorems</th><th>Easy · Medium · Hard</th><th>First · latest</th><th style="width:22%">Share of points</th></tr></thead><tbody>
      ${rows.map((r, i) => `<tr class="${i < 3 ? 'podium p' + (i + 1) : ''}"><td class="rk">${i + 1}</td><td><b>${esc(r.name)}</b>${orgMark(r, key)}${i === 0 ? ' <span class="star" title="First place">★</span>' : ''}${key !== 'team' && r.orgs.size ? `<br><small class="muted">${esc([...r.orgs].join(', '))}</small>` : ''}</td>
        <td class="n"><b>${fmt(r.points)}</b></td><td class="n">${fmt(r.proved + r.refuted)}${r.refuted ? ` <small class="muted">(${r.refuted} refuted)</small>` : ''}</td>
        <td class="n">${fmt(r.main)}</td><td class="n">${r.E} · ${r.M} · ${r.H}</td><td class="n"><small>${esc(r.first)} · ${esc(r.last)}</small></td>
        <td><span class="rbar"><i style="width:${100 * r.points / total}%"></i></span></td></tr>`).join('')}
      </tbody></table></div>${lbChart(rows, key)}` : `<p class="sub">No proofs name a ${key} yet.</p>`}
    <h3>How points work</h3>
    <p>A resolved theorem is worth 1, 2 or 3 points for an Easy, Medium or Hard program, and three times as much if it is the program's
    main theorem, the full correctness statement. Proving a theorem and proving its negation count the same. Ties go to more main theorems,
    then to whoever got there first.</p>
    <h3>Organizations</h3>
    <p>Organization names in proof headers are self-reported. An organization a maintainer has confirmed gets a ✓ and a link: open an issue
    from an account of the organization to be confirmed. The list is <a href="${REPO}/blob/main/organizations.json"><code>organizations.json</code></a>.</p>
    <h3>Get on the leaderboard</h3>
    ${pre(`python3 tools/new_proof.py <task> <n> --name "Your Name" --org "Your Lab" --system "YourProver v2"`, null, false)}
    <p>The header of the proof file carries the credit (<code>Contributor:</code>, and optionally <code>Organization:</code> and
    <code>System:</code>). Open a pull request; once CI accepts the proof it is merged and counted here. Machine-found proofs are welcome:
    name the system that found them. See the <a href="#/contribute">Contribute</a> page to start.</p>
    <div class="foot">${pins()}</div></div>`;
}

/* ---------- contribute ---------- */
async function renderContribute() {
  const v = $('view'); v.dataset.v = 'contribute';
  const first = D.first || [];
  v.innerHTML = `<div class="prose">
    <h1>Contribute</h1>
    <p>Fork <a href="${REPO}">the repository</a> and open a pull request. Every contribution is checked by the same script that runs in CI,
    <code>tools/check.py</code>; a pull request that only adds proofs is merged once CI accepts them.</p>
    <div class="tracks">
      <div class="track"><b>Proofs</b><p>Prove a theorem or its negation. A proof is accepted when <code>lake comparator</code> accepts it: the statement is unchanged, there is no <code>sorry</code>, and only the axioms <code>propext</code>, <code>Quot.sound</code> and <code>Classical.choice</code> are used.</p></div>
      <div class="track"><b>Specifications</b><p>Add a theorem to a program, in natural language and in Lean, or a better version of an existing one. Released statements are frozen: an improvement is added as a new theorem.</p></div>
      <div class="track"><b>Programs</b><p>Add a program for a LeetCode problem that is not covered yet, or fix a translation. A program passes every test case and its Lean code is the output of the pinned Charon and Aeneas.</p></div>
    </div>
    <h3>Proving a theorem</h3>
    ${pre(`lake exe cache get && lake build Aeneas   # once, at the repository root (Linux)
python3 tools/new_proof.py <task> <n> --name "Your Name" --org "Your Lab"   # copies Specs.lean to Proofs/spec_<n>.lean
# replace the sorry of spec_<n> with a proof; add lemmas before it if you need them
python3 tools/check.py proof programs/<task>/Proofs/spec_<n>.lean`, null, false)}
    <p>New to this? <a href="${REPO}/blob/main/docs/first-proof.md">Your first proof</a> walks through one complete proof, from the open theorem to the merged pull request.
    To refute a theorem, use <code>--negation</code> and prove <code>spec_&lt;n&gt;_neg</code> instead. Then open a pull request; CI runs the same check.</p>
    <h3>How a proof is checked</h3>
    <p>A proof may add any definitions and lemmas it needs, and imports from the same Lean, Mathlib and Aeneas versions. It may not change
    the statement. It must not use <code>sorry</code>, and it may only use the standard axioms <code>propext</code>, <code>Quot.sound</code> and
    <code>Classical.choice</code>. This rules out <code>native_decide</code>, which adds an axiom of its own. Lean's built-in <code>lake comparator</code>
    compares the proof with the original statement, checks the axioms, and replays the proof in the Lean kernel. Nothing is graded by hand or by a model.</p>
    <h3>Good first theorems</h3>
    <div class="tw"><table class="list"><tbody>${first.map(r => `<tr data-t="${r[0]}" data-n="${r[1]}"><td><a href="#/p/${r[0]}/${r[1]}">${esc(title(r[0]))}</a></td><td class="n">spec_${r[1]} · ${CAT[r[2]]}</td><td>${esc(r[5])}</td></tr>`).join('')}</tbody></table></div>
    <h3>Contributors</h3>
    <div class="tw"><table class="list"><thead><tr><th>Contributor</th><th>Proved</th><th>Refuted</th><th>Share of resolved theorems</th></tr></thead><tbody>
    ${D.contributors.map(c => `<tr><td>${esc(c.name)}</td><td>${c.proved}</td><td>${c.refuted}</td><td style="width:40%"><span class="rbar"><i style="width:${100 * (c.proved + c.refuted) / Math.max(1, D.totals.proved + D.totals.refuted)}%"></i></span></td></tr>`).join('') || '<tr><td colspan="4">No proofs yet.</td></tr>'}</tbody></table></div>
  </div>`;
  v.querySelectorAll('tbody tr[data-t]').forEach(tr => tr.onclick = () => { location.hash = `#/p/${tr.dataset.t}/${tr.dataset.n}`; });
}

/* ---------- search ---------- */
function setupSearch() {
  const inp = $('search'), res = $('results'); let hits = [], k = 0;
  const show = () => { res.hidden = !hits.length; res.innerHTML = hits.map((p, i) => `<a href="#/p/${p.t}" class="${i === k ? 'sel' : ''}">${esc(title(p.t))} <small>#${p.q} · ${DIFF[p.d]} · ${p.st.length ? `${resolvedOf(p)} of ${p.st.length} resolved` : 'no theorems yet'}</small></a>`).join(''); };
  inp.oninput = () => { const q = inp.value.trim().toLowerCase(); k = 0;
    mapState.q = q.length > 1 ? q.replace(/\s+/g, '-') : ''; if ($('view').dataset.v === 'map') maps.forEach(layout);
    const qs = q.replace(/\s+/g, '-');
    const score = p => p.t === qs || String(p.q) === q ? 0 : p.t.startsWith(qs) ? 1 : p.t.includes(qs) ? 2 : p.g.some(g => g.toLowerCase() === q) ? 3 : p.g.some(g => g.toLowerCase().includes(q)) ? 4 : 9;
    hits = q ? D.programs.map(p => [score(p), p]).filter(x => x[0] < 9).sort((a, b) => a[0] - b[0] || b[1].st.length - a[1].st.length).slice(0, 40).map(x => x[1]) : [];
    show(); if (q && !hits.length) { res.hidden = false; res.innerHTML = '<a><small>No program matches.</small></a>'; } };
  inp.onkeydown = e => {
    if (e.key === 'ArrowDown') { k = Math.min(k + 1, hits.length - 1); show(); e.preventDefault(); }
    if (e.key === 'ArrowUp') { k = Math.max(k - 1, 0); show(); e.preventDefault(); }
    if (e.key === 'Enter' && hits[k]) { location.hash = '#/p/' + hits[k].t; res.hidden = true; inp.blur(); }
    if (e.key === 'Escape') { res.hidden = true; inp.blur(); }
  };
  res.onclick = () => { res.hidden = true; };
  document.addEventListener('click', e => { if (!$('searchwrap').contains(e.target)) res.hidden = true; });
}

$('theme').onclick = () => {
  const dark = document.documentElement.dataset.theme === 'dark' || (!document.documentElement.dataset.theme && matchMedia('(prefers-color-scheme: dark)').matches);
  document.documentElement.dataset.theme = dark ? 'light' : 'dark';
  try { localStorage.setItem('theme', document.documentElement.dataset.theme); } catch (e) {}
  maps.forEach(layout);
};

(async () => {
  try { D = await json('data/index.json'); await links(); } catch (e) { $('view').innerHTML = `<p>Could not load the data: ${esc(e.message)}</p>`; return; }
  D.programs.forEach(p => BY[p.t] = p);
  setupSearch(); window.addEventListener('hashchange', route); route();
})();
})();
