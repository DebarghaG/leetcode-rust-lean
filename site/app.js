'use strict';
/* Progress site for the LeetCode Rust-to-Lean theorems.
   Data (built by tools/build_site.py): data/index.json (programs and their theorem statuses),
   data/theorems.json (one row per theorem), data/p/<task>.json (one program). */
(() => {
const $ = id => document.getElementById(id);
const DATASET = 'https://huggingface.co/datasets/Debargha/leetcode-rust-lean';
const DISCUSS = DATASET + '/discussions';
const CAT = {re: 'relational', ed: 'edge', bo: 'bounds', in: 'invariance', fu: 'functional',
             wi: 'witness', no: 'no_failure', sh: 'shape', mo: 'monotonicity'};
const DIFF = {E: 'Easy', M: 'Medium', H: 'Hard'};
const STATUS = {o: 'open', p: 'proved', r: 'refuted', x: 'conflict', s: 'superseded'};
let D = null, THMS = null, BY = {}, cur = null, mapState = {tag: '', split: '', q: ''};

const esc = s => String(s ?? '').replace(/[&<>"]/g, c => ({'&': '&amp;', '<': '&lt;', '>': '&gt;', '"': '&quot;'}[c]));
const fmt = n => n.toLocaleString('en-US');
const SMALL = new Set('a an and as at by for from in into of on or the to with'.split(' '));
const ROMAN = /^(i|ii|iii|iv|v|vi|vii|viii|ix|x)$/;
const title = t => t.split('-').map((w, i) => !w ? w : ROMAN.test(w) && i ? w.toUpperCase() : i && SMALL.has(w) ? w : w[0].toUpperCase() + w.slice(1)).join(' ');
const css = v => getComputedStyle(document.documentElement).getPropertyValue(v).trim();
const cats = p => (p.c.match(/../g) || []).map(c => CAT[c]);

async function json(url) { const r = await fetch(url); if (!r.ok) throw new Error(url + ': ' + r.status); return r.json(); }
async function theorems() { return THMS || (THMS = await json('data/theorems.json')); }

/* ---------- code highlighting (enough for Lean and Rust) ---------- */
const KW = new Set(('def theorem lemma by have show from fun let in if then else match with do return open namespace end section ' +
  'noncomputable structure inductive instance where abbrev private protected import sorry exact intro intros apply simp omega ' +
  'cases induction rfl calc obtain refine constructor unfold rw decide exists use at pub fn mut while for loop break continue ' +
  'struct enum impl true false Some None mod as Type Prop').split(' '));
const TY = new Set('Result Std I64 I32 U8 U32 U64 Usize Isize Bool Nat Int List Slice Vec alloc Option ok fail i64 usize u8 bool ℕ ℤ'.split(' '));
const pre = (code, plain) => `<div class="prewrap"><button class="cp" data-copy="${esc(plain ?? code)}">copy</button><pre>${hl(code)}</pre></div>`;
function toast(msg) { let t = $('toast'); if (!t) { t = document.createElement('div'); t.id = 'toast'; document.body.append(t); }
  t.textContent = msg; t.hidden = false; clearTimeout(t._h); t._h = setTimeout(() => t.hidden = true, 1600); }
document.addEventListener('click', e => {
  const b = e.target.closest('[data-copy]'); if (!b) return;
  e.preventDefault(); e.stopPropagation();
  navigator.clipboard.writeText(b.dataset.copy).then(() => { if (b.classList.contains('cp')) { b.textContent = 'copied'; b.classList.add('done');
    setTimeout(() => { b.textContent = 'copy'; b.classList.remove('done'); }, 1400); } else toast('Link copied'); });
});
function hl(src) {
  return esc(src).replace(/(--[^\n]*|\/\/[^\n]*)|(\/-[\s\S]*?-\/)|(&quot;[^\n]*?&quot;)|([A-Za-z_][\w'.]*)/g, (m, c1, c2, s, w) => {
    if (c1 || c2) return `<span class="cm">${m}</span>`;
    if (s) return `<span class="sr">${m}</span>`;
    const base = w.split('.').pop();
    return KW.has(w) ? `<span class="kw">${w}</span>` : TY.has(base) || TY.has(w) ? `<span class="ty">${w}</span>` : w;
  });
}

/* ---------- routing ---------- */
function route() {
  const h = location.hash.replace(/^#\/?/, '');
  const [path, qs] = h.split('?'); const parts = path.split('/').filter(Boolean);
  const q = new URLSearchParams(qs || '');
  const view = parts[0] === 'theorems' ? 'theorems' : parts[0] === 'contribute' ? 'contribute' : 'map';
  document.querySelectorAll('nav a').forEach(a => a.classList.toggle('on', a.dataset.v === view));
  if (parts[0] === 'p') { if (!$('view').dataset.v) renderMap(); openProgram(decodeURIComponent(parts[1]), +parts[2] || 0); return; }
  closeSide(false);
  document.title = {theorems: 'Theorems', contribute: 'Contribute', map: 'Proof progress'}[view] + ' · LeetCode Rust-to-Lean';
  if (view === 'theorems') renderTheorems(q); else if (view === 'contribute') renderContribute(); else renderMap(q);
}

/* ---------- map ---------- */
function resolvedOf(p) { return (p.st.match(/[pr]/g) || []).length; }
function nextUp() {                                    // one open theorem to suggest, changing daily
  const day = Math.floor(Date.now() / 864e5), pool = [];
  for (const p of D.programs) if (p.d === 'E') (p.c.match(/../g) || []).forEach((c, i) => {
    if (p.st[i] === 'o' && (c === 'no' || c === 'bo')) pool.push([p, i + 1, CAT[c]]); });
  return pool.length ? pool[(day * 2654435761 % 4294967296) % pool.length] : null;
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
  mapState.tag = q.get('tag') || ''; mapState.split = q.get('split') || '';
  const T = D.totals, done = T.proved + T.refuted, pct = 100 * done / T.theorems;
  const progs = D.programs.filter(p => p.st.length);
  const mainsDone = progs.filter(p => 'pr'.includes(p.st[p.m - 1])).length;
  const full = progs.filter(p => resolvedOf(p) === p.st.length).length;
  const tags = [...new Set(D.programs.flatMap(p => p.g))].sort();
  const by = (keyOf) => { const m = new Map(); for (const p of progs) for (const [k, d, n] of keyOf(p)) { const a = m.get(k) || [0, 0]; a[0] += d; a[1] += n; m.set(k, a); } return m; };
  const byD = by(p => [[p.d, resolvedOf(p), p.st.length]]);
  const byC = by(p => (p.c.match(/../g) || []).map((c, i) => [c, 'pr'.includes(p.st[i]) ? 1 : 0, 1]));
  const byT = by(p => p.g.map(g => [g, resolvedOf(p), p.st.length]));
  const nu = nextUp();
  v.innerHTML = `
  <div class="hero">
    <div>
      <div class="big">${fmt(done)} <small>of ${fmt(T.theorems)} theorems resolved</small></div>
      <div class="bar" title="${pct.toFixed(2)}% resolved"><i style="width:${100 * T.proved / T.theorems}%;background:var(--proved)"></i><i style="width:${100 * T.refuted / T.theorems}%;background:var(--refuted)"></i></div>
      <div class="figs">
        <div class="fig"><b>${fmt(T.proved)}</b><span>proved</span></div>
        <div class="fig"><b>${fmt(T.refuted)}</b><span>refuted</span></div>
        <div class="fig"><b>${fmt(T.theorems - done)}</b><span>open</span></div>
        <div class="fig"><b>${fmt(mainsDone)}</b><span>main theorems resolved</span></div>
        <div class="fig"><b>${fmt(full)}</b><span>programs fully resolved</span></div>
        <a class="fig" href="#/contribute"><b>${fmt(D.contributors.length)}</b><span>contributors</span></a>
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
    ${nu ? `<a class="card next" href="#/p/${nu[0].t}/${nu[1]}"><span class="kicker">Next up</span>
      <b>${esc(title(nu[0].t))}, spec_${nu[1]}</b>
      <span>A ${nu[2] === 'no_failure' ? 'no-failure' : 'bounds'} theorem about an Easy program, with no proof yet: a good first proof.</span>
      <span class="go">Open it →</span></a>` : ''}
    <div class="card"><span class="kicker">By difficulty</span>${rows('EMH'.split('').map(d => [DIFF[d], ...(byD.get(d) || [0, 0]), `#/theorems?difficulty=${d}`]))}</div>
    <div class="card"><span class="kicker">By category</span>${rows([...byC].sort((a, b) => b[1][1] - a[1][1]).map(([c, [d, n]]) => [CAT[c], d, n, `#/theorems?category=${CAT[c]}`]))}</div>
    <div class="card"><span class="kicker">Recently proved</span>${recentGroups().slice(0, 7).map(g =>
      `<a class="row" href="#/p/${g.t}/${g.ids[0]}"><span class="nm">${esc(title(g.t))}</span><span class="num">${g.ids.length === 1 ? 'spec_' + g.ids[0] : g.ids.length + ' theorems'} · ${esc(g.by)}</span></a>`).join('') || '<p class="sub">No proofs yet.</p>'}
      <a class="more" href="#/theorems?status=proved">All resolved theorems →</a></div>
  </div>
  <div class="mapctl">
    <span class="legend" style="margin:0"><span><i style="background:var(--open)"></i>open</span><span><i style="background:var(--open-main)"></i>open main theorem</span>
      <span><i style="background:var(--proved)"></i>proved</span><span><i style="background:var(--refuted)"></i>refuted</span></span>
    <span style="margin-left:auto">Topic <select id="mTag"><option value="">all</option>${tags.map(t => `<option${t === mapState.tag ? ' selected' : ''}>${esc(t)}</option>`).join('')}</select></span>
    <span>Split <select id="mSplit"><option value="">all</option><option value="te"${mapState.split === 'te' ? ' selected' : ''}>test</option><option value="tr"${mapState.split === 'tr' ? ' selected' : ''}>train</option></select></span>
  </div>
  <div id="maps"></div>
  <h2>Topics</h2>
  <div class="topics">${rows([...byT].sort((a, b) => b[1][1] - a[1][1]).map(([g, [d, n]]) => [g, d, n, `#/?tag=${encodeURIComponent(g)}`]))}</div>
  <h2>Reading the map</h2>
  <p class="hint">One square per theorem, one block per program, grouped by difficulty; the darker square of a block is the program's
  main theorem. Hover a block for its name and click it to open the program. <kbd>/</kbd> search · <kbd>m</kbd> map ·
  <kbd>t</kbd> theorems · <kbd>c</kbd> contribute · in a program, <kbd>j</kbd> <kbd>k</kbd> next and previous theorem,
  <kbd>[</kbd> <kbd>]</kbd> previous and next program · <kbd>Esc</kbd> close.</p>
  <div class="foot">Built ${esc(D.built)} from commit <code>${esc(D.commit || '')}</code> ·
    Data: <a href="${DATASET}">Hugging Face</a> · Paper: <a href="https://arxiv.org/abs/2610.38174">arXiv 2610.38174</a> (unofficial reproduction).</div>`;
  const setQ = () => { const n = new URLSearchParams(); if (mapState.tag) n.set('tag', mapState.tag); if (mapState.split) n.set('split', mapState.split);
    history.replaceState(null, '', '#/' + (String(n) ? '?' + n : '')); drawMaps(); };
  $('mTag').onchange = e => { mapState.tag = e.target.value; setQ(); };
  $('mSplit').onchange = e => { mapState.split = e.target.value; setQ(); };
  drawMaps();
  if (mapState.tag) $('maps').scrollIntoView({block: 'start'});
}

let maps = [];
function drawMaps() {
  const box = $('maps'); if (!box) return;
  box.innerHTML = ''; maps = [];
  for (const d of 'EMH') {
    const ps = D.programs.filter(p => p.d === d && p.st.length);
    const n = ps.reduce((a, p) => a + p.st.length, 0), dn = ps.reduce((a, p) => a + (p.st.match(/[pr]/g) || []).length, 0);
    const h = document.createElement('h2'); h.textContent = `${DIFF[d]}  ·  ${fmt(ps.length)} programs  ·  ${fmt(dn)} of ${fmt(n)} resolved`;
    const c = document.createElement('canvas'); c.className = 'map'; c.setAttribute('role', 'img');
    c.setAttribute('aria-label', `Map of the ${DIFF[d]} programs: ${fmt(dn)} of ${fmt(n)} theorems resolved. The theorem list gives the same information as text.`);
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
    if (cur && cur.task_id === r.p.t) { g.globalAlpha = 1; g.strokeStyle = css('--accent'); g.lineWidth = 2; g.strokeRect(r.x - 2, r.y - 2, r.bw + 3, r.bh + 3); }
  }
  m.c.onmousemove = e => { const r = hit(m, e); const tip = $('tip');
    if (!r) { tip.hidden = true; return; }
    const n = r.p.st.length, dn = (r.p.st.match(/[pr]/g) || []).length;
    tip.innerHTML = `<b>${esc(title(r.p.t))}</b><br><small>#${r.p.q} · ${dn} of ${n} resolved · main theorem ${STATUS[r.p.st[r.p.m - 1]]}</small>`;
    tip.hidden = false; tip.style.left = Math.min(e.clientX + 14, innerWidth - 370) + 'px'; tip.style.top = e.clientY + 14 + 'px'; };
  m.c.onmouseleave = () => { $('tip').hidden = true; };
  m.c.onclick = e => { const r = hit(m, e); if (r) location.hash = '#/p/' + r.p.t; };
}
function hit(m, e) {
  const b = m.c.getBoundingClientRect(), x = e.clientX - b.left, y = e.clientY - b.top;
  return m.rects.find(r => x >= r.x - 2 && x <= r.x + r.bw + 2 && y >= r.y - 2 && y <= r.y + r.bh + 2);
}
window.addEventListener('resize', () => maps.forEach(layout));

/* ---------- program inspector ---------- */
async function openProgram(task, n) {
  const side = $('side'); side.hidden = false; $('main').classList.add('split');
  if (!cur || cur.task_id !== task) {
    if (!BY[task]) { cur = null; $('insp').innerHTML = `<h1>No such program</h1><p class="sub"><code>${esc(task)}</code> is not one of the programs. Try the search box.</p>`; return; }
    $('insp').innerHTML = '<p class="sub">Loading…</p>'; side.dataset.tab = 'theorems'; tfilt = 'all';
    cur = await json(`data/p/${encodeURIComponent(task)}.json`); side.scrollTop = 0; }
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
  const tabs = [['theorems', `Theorems (${p.theorems.length})`], ['problem', 'Problem'], ['rust', 'Rust'], ['lean', 'Lean'], ['specs', 'Specs.lean']];
  const [prv, nxt] = neighbours(p.task_id);
  let body = '';
  if (tab === 'theorems') {
    const shown = p.theorems.filter(t => tfilt === 'all' || (tfilt === 'open' ? t.status === 'open' : t.status !== 'open'));
    body = !p.theorems.length ? '<p class="sub">This program has no theorems yet.</p>' :
      `<div class="tfilter">${[['all', 'All', p.theorems.length], ['open', 'Open', p.theorems.length - done], ['done', 'Resolved', done]]
        .map(([k, l, n]) => `<button data-f="${k}" class="${k === tfilt ? 'on' : ''}">${l} ${n}</button>`).join('')}</div>` +
      (shown.map(t => thmCard(p, t, t.id === sel)).join('') || '<p class="sub">None.</p>');
  }
  if (tab === 'problem') body = `<div class="desc">${esc(p.description)}</div><p class="sub">Signature: <code>${esc(p.rust_signature)}</code> · ${p.num_test_cases} test cases</p>`;
  if (tab === 'rust') body = pre(p.rust);
  if (tab === 'lean') body = `<p class="sub">The Aeneas translation (<code>Funs.lean</code>).</p>${pre(p.lean_funs)}
    <details><summary>Types.lean</summary>${pre(p.lean_types)}</details>` +
    (p.lean_funs_external ? `<details><summary>FunsExternal.lean (trusted models of Rust library functions)</summary>${pre(p.lean_funs_external)}</details>` : '');
  if (tab === 'specs') body = `<p class="sub">The challenge file: every theorem and its negation, each with <code>sorry</code>.</p>${pre(p.specs_file)}`;
  $('insp').innerHTML = `
    <div class="pnav"><a href="#/p/${prv}" title="Previous program ( [ )">‹ previous</a><a href="#/p/${nxt}" title="Next program ( ] )">next ›</a></div>
    <h1>${esc(title(p.task_id))}</h1>
    <div class="sub"><span class="chip ${p.difficulty[0]}">${p.difficulty}</span><span class="chip">#${p.question_id}</span><span class="chip">${p.split}</span>
      ${p.tags.map(t => `<a class="chip" href="#/?tag=${encodeURIComponent(t)}">${esc(t)}</a>`).join('')}
      <br>${done} of ${p.theorems.length} theorems resolved · <a href="https://leetcode.com/problems/${p.task_id}/">LeetCode</a> · <code>programs/${esc(p.task_id)}</code></div>
    <div class="tabs">${tabs.map(([k, l]) => `<a href="#" data-tab="${k}" class="${k === tab ? 'on' : ''}">${l}</a>`).join('')}</div>
    ${body}`;
  $('insp').querySelectorAll('.tabs a').forEach(a => a.onclick = e => { e.preventDefault(); renderProgram(a.dataset.tab, 0); });
  $('insp').querySelectorAll('.tfilter button').forEach(b => b.onclick = () => { tfilt = b.dataset.f; renderProgram('theorems', sel); });
  if (sel) { const el = document.getElementById('thm' + sel), sd = $('side');
    if (el) sd.scrollTop = Math.max(0, el.offsetTop - sd.clientHeight / 3); }
}
function thmCard(p, t, sel) {
  const task = p.task_id, f = `programs/${task}/Proofs/spec_${t.id}.lean`;
  const link = location.href.split('#')[0] + `#/p/${task}/${t.id}`;
  const cmds = `python3 tools/new_proof.py ${task} ${t.id}        # add --negation to refute it\n# prove spec_${t.id} in ${f}, then\npython3 tools/check.py proof ${f}`;
  const proof = t.proof ? `<p class="sub">${t.status === 'refuted' ? 'Refuted' : 'Proved'} by <b>${esc(t.proof.by)}</b>, checked by <code>lake comparator</code> on ${esc(t.proof.checked)}.</p>
      <details><summary>Show the proof (${t.proof.text.split('\n').length} lines)</summary>${pre(t.proof.text)}</details>` :
    `<details><summary>Work on this theorem</summary>${pre(cmds)}</details>`;
  const lean = (p.specs_file.match(new RegExp(`theorem spec_${t.id} [\\s\\S]*?:= by\\s*\\n\\s*sorry`)) || [''])[0];
  const neg = (p.specs_file.match(new RegExp(`theorem spec_${t.id}_neg [\\s\\S]*?:= by\\s*\\n\\s*sorry`)) || [''])[0];
  return `<div class="thm${sel ? ' sel' : ''}" id="thm${t.id}" data-n="${t.id}">
    <div class="hd"><b>spec_${t.id}</b><span>${t.category}</span>${t.main ? '<span class="chip">main</span>' : ''}
      <button class="lnk" data-copy="${esc(link)}" title="Copy a link to this theorem">#</button><span class="st ${t.status}">${t.status}</span></div>
    <p>${esc(t.statement)}</p>${t.preconditions ? `<p class="pre">Preconditions: ${esc(t.preconditions)}</p>` : ''}
    <details${sel ? ' open' : ''}><summary>Lean statement</summary>${pre(lean)}</details>
    <details><summary>Negation</summary>${pre(neg)}</details>
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
             s: q.get('split') || '', text: q.get('q') || '', page: +q.get('page') || 0};
  const out = rows.filter(r => { const p = BY[r[0]];
    return (!f.st || STATUS[r[4]] === f.st) && (!f.d || p.d === f.d) && (!f.c || CAT[r[2]] === f.c) && (!f.main || r[3]) &&
           (!f.s || p.s === f.s) && (!f.text || (r[0] + ' ' + r[5]).toLowerCase().includes(f.text.toLowerCase())); });
  const per = 100, pages = Math.max(1, Math.ceil(out.length / per)), pg = Math.min(f.page, pages - 1);
  const sel = (k, opts, val) => `<select data-k="${k}"><option value="">${k}: all</option>${opts.map(([a, b]) => `<option value="${a}"${a === val ? ' selected' : ''}>${b}</option>`).join('')}</select>`;
  v.innerHTML = `<div class="filters">
      ${sel('status', [['open', 'open'], ['proved', 'proved'], ['refuted', 'refuted']], f.st)}
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

/* ---------- contribute ---------- */
async function renderContribute() {
  const v = $('view'); v.dataset.v = 'contribute';
  const first = D.first || [];
  v.innerHTML = `<div class="prose">
    <h1>Contribute</h1>
    <p>The repository is private for now. To contribute, ask for access on the <a href="${DISCUSS}">Hugging Face discussion page</a>.
    Every contribution comes in as a pull request and is checked by the same script that runs in CI, <code>tools/check.py</code>.</p>
    <div class="tracks">
      <div class="track"><b>Proofs</b><p>Prove a theorem or its negation. A proof is accepted when <code>lake comparator</code> accepts it: the statement is unchanged, there is no <code>sorry</code>, and only the axioms <code>propext</code>, <code>Quot.sound</code> and <code>Classical.choice</code> are used.</p></div>
      <div class="track"><b>Specifications</b><p>Add a theorem to a program, in natural language and in Lean, or a better version of an existing one. Released statements are frozen: an improvement is added as a new theorem.</p></div>
      <div class="track"><b>Programs</b><p>Add a program for a LeetCode problem that is not covered yet, or fix a translation. A program passes every test case and its Lean code is the output of the pinned Charon and Aeneas.</p></div>
    </div>
    <h3>Proving a theorem</h3>
    ${pre(`lake update && lake exe cache get        # once, at the repository root
python3 tools/new_proof.py <task> <n>       # copies Specs.lean to programs/<task>/Proofs/spec_<n>.lean
# replace the sorry of spec_<n> with a proof; add lemmas before it if you need them
python3 tools/check.py proof programs/<task>/Proofs/spec_<n>.lean`)}
    <p>To refute a theorem, use <code>--negation</code> and prove <code>spec_&lt;n&gt;_neg</code> instead. Then open a pull request; CI runs the same check.</p>
    <h3>How a proof is checked</h3>
    <p>A proof may add any definitions and lemmas it needs, and imports from the same Lean, Mathlib and Aeneas versions. It may not change
    the statement. It must not use <code>sorry</code>, and it may only use the standard axioms <code>propext</code>, <code>Quot.sound</code> and
    <code>Classical.choice</code>. This rules out <code>native_decide</code>, which adds an axiom of its own. Lean's built-in <code>lake comparator</code>
    compares the proof with the original statement, checks the axioms, and replays the proof in the Lean kernel. Nothing is graded by hand or by a model.</p>
    <h3>Good first theorems</h3>
    <div class="tw"><table class="list"><tbody>${first.map(r => `<tr data-t="${r[0]}" data-n="${r[1]}"><td><a href="#/p/${r[0]}/${r[1]}">${esc(title(r[0]))}</a></td><td class="n">spec_${r[1]} · ${CAT[r[2]]}</td><td>${esc(r[5])}</td></tr>`).join('')}</tbody></table></div>
    <h3>Contributors</h3>
    <table class="list"><thead><tr><th>Contributor</th><th>Proved</th><th>Refuted</th><th>Share of resolved theorems</th></tr></thead><tbody>
    ${D.contributors.map(c => `<tr><td>${esc(c.name)}</td><td>${c.proved}</td><td>${c.refuted}</td><td style="width:40%"><span class="rbar"><i style="width:${100 * (c.proved + c.refuted) / Math.max(1, D.totals.proved + D.totals.refuted)}%"></i></span></td></tr>`).join('') || '<tr><td colspan="4">No proofs yet.</td></tr>'}</tbody></table>
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
  try { D = await json('data/index.json'); } catch (e) { $('view').innerHTML = `<p>Could not load the data: ${esc(e.message)}</p>`; return; }
  D.programs.forEach(p => BY[p.t] = p);
  setupSearch(); window.addEventListener('hashchange', route); route();
})();
})();
