// JS ↔ Lean 전수 대조의 JS 쪽 (Claude, 2026-10-21 — 와우SRD 1.0.0)
//   1) deno run --allow-read --allow-write tools/lean/cross_check.js input <입력.txt> <js출력.txt>
//        앱의 js 파일(rng · ltass · protocol · staircase · analysis)을 화면 없이 올려, 입력 줄과 같은 꼴의 기대 출력을 같은 순서로 씀
//   2) (tools/lean 에서) .lake/build/bin/crosscheck.exe <입력.txt> <lean출력.txt>
//   3) deno run --allow-read tools/lean/cross_check.js check <js출력.txt> <lean출력.txt>
//        한 줄씩 비교 → 종류마다 같은 줄 수 · 다른 줄 (처음 30개) · 변조 시험(종류마다 한 줄을 일부러 바꾼 출력은 반드시 다르게 나와야 함)
//        마지막 줄 ‘판정: 통과/실패’ — 다른 줄이 있거나, 비교한 종류가 비거나, 변조를 못 잡으면 종료 코드 1
const root = new URL('../../', import.meta.url);
const files = ['js/rng.js', 'js/ltass.js', 'js/protocol.js', 'js/staircase.js', 'js/analysis.js'];
let code = '';
for (const f of files) code += `\n// ── ${f} ──\n` + Deno.readTextFileSync(new URL(f, root));
code += '\n;globalThis.__A = { Rng, TrialPlan, ConstPlan, Exact, Stats, ConstRun, Analysis, Stair, PROTOCOLS, DENS_MILLI, TARGET_P };\n';
(0, eval)(code);
const { Rng, TrialPlan, ConstPlan, Exact, Stats, ConstRun, Analysis, Stair, PROTOCOLS, DENS_MILLI, TARGET_P } = globalThis.__A;
const CFG = Stair.cfgFrom(PROTOCOLS.won2007), CCFG = ConstRun.cfgFrom(PROTOCOLS.drennan2014);
const csv = a => a.length ? a.join(',') : '-';
const b01 = x => x ? '1' : '0';

// ── 줄마다 js 기대 출력 ──
function feedStair(seq) {
  let st = Stair.init(CFG);
  const trs = [];
  for (let i = 0; i < seq.length; i++) {
    if (st.status !== 'running') break;
    const ch = seq[i];
    const r = Stair.step(st, CFG, { trialId: 't' + i, presentedK: st.k, valid: ch !== 'X', correct: ch === 'C', reason: ch === 'X' ? 'technical' : null });
    trs.push(r.tr); st = r.state;
  }
  return { st, trs };
}
const MOVE = { MOVE: 'M', STAY: 'S', BLOCKED_ZERO_MOVE: 'B', INVALID_NO_CHANGE: 'X' };
const BND = v => v === 'easy' ? 1 : v === 'hard' ? 2 : 0;
function jsLine(ln) {
  const p = ln.split(' ');
  switch (p[0]) {
    case 'RNG': {
      const r = Rng.fromHex(p[1]); const out = [];
      for (let i = 0; i < +p[2]; i++) out.push(r.u32());
      return [`RNG ${p[1]} ${csv(out)} ${r.hex()}`];
    }
    case 'INT': {
      const r = Rng.fromHex(p[1]);
      const out = p[2].split(',').map(n => r.int(+n));
      return [`INT ${p[1]} ${csv(out)} ${r.hex()}`];
    }
    case 'PLAN': {
      const r = Rng.fromHex(p[1]); const out = [];
      for (let i = 0; i < +p[2]; i++) { const d = TrialPlan.draw(r); out.push(`PLAN ${p[1]} ${i} ${d.targetPos} ${d.thetaU} ${d.seeds.join(',')} ${d.roves.join(',')} ${d.rngAfter}`); }
      return out;
    }
    case 'ORDER': {
      const r = Rng.fromHex(p[1]);
      const o = ConstPlan.order(r, CCFG.densIdx, CCFG.per);
      return [`ORDER ${p[1]} ${csv(o)} ${r.hex()}`];
    }
    case 'STAIR': {
      const { st, trs } = feedStair(p[2]);
      const th = Stair.threshold(st, CFG);
      return [`STAIR ${p[1]} ${st.status} ${st.k} ${st.correctStreak} ${st.lastDir === null ? 0 : st.lastDir} ${st.validCount} ${st.technicalCount} ${st.attemptCount} ${st.moves} ` +
        `${csv(st.reversals.map(r => r.k))} ${csv(st.reversals.map(r => r.validNo))} ${csv(st.reversals.map(r => BND(r.atBound)))} ${th ? th.sumMilli + '/' + th.count : '-'} ` +
        `${trs.map(t => MOVE[t.move]).join('')} ${trs.map(t => BND(t.blockedAt)).join('')}`];
    }
    case 'CLASS': {
      const { st, trs } = feedStair(p[2]);
      const trials = trs.map((tr, i) => {
        const tp = 1 + (i % 3);
        return { id: 't' + i, valid: tr.valid, correct: tr.correct, k: tr.presentedK, tr, targetPos: tp, response: tr.valid ? (tr.correct ? tp : (tp % 3) + 1) : null };
      });
      const run = { kind: 'adaptive', state: st, trials, seed: '0123456789abcdef0123456789abcdef' };
      const x = Analysis.classifyAdaptive(run, CFG), b = x.bound, f = x.flags;
      const bs = b ? [b.nWin, b.easyBlocksWin, b.hardBlocksWin, b.easyBlocksBefore, b01(b.touchedEasy), b01(b.touchedHard), b.easyWin.n, b.easyWin.k, b.harderWin.n, b.harderWin.k, b.hardWin.n, b.hardWin.k].join(',') : '-';
      return [`CLASS ${p[1]} ${x.status} ${x.reason || '-'} ${b01(f.includes('near_easy_end'))} ${b01(f.includes('near_hard_end'))} ${b01(f.includes('early_easy_errors'))} ${b01(f.includes('track_not_above_chance'))} ` +
        `${x.status === 'complete_in_range' ? x.sumMilli + '/' + x.count : '-'} ${bs} ${b01(b && b.sigEasyWorse)} ${b01(b && b.easyWin.n && b.easyWin.pBelowTarget < 0.05)} ${b01(b && b.hardWin.n && b.hardWin.pAboveTarget < 0.05)}`];
    }
    case 'CLIN': {
      const order = ConstPlan.order(Rng.fromHex(p[2]), CCFG.densIdx, CCFG.per);
      let st = ConstRun.init(CCFG, order); const trs = [];
      for (let i = 0; i < p[3].length; i++) {
        if (st.status !== 'running') break;
        const ch = p[3][i];
        const r = ConstRun.step(st, CCFG, order, { trialId: 'c' + i, presentedK: st.k, valid: ch !== 'X', correct: ch === 'C', reason: ch === 'X' ? 'technical' : null });
        trs.push(r.tr); st = r.state;
      }
      return [`CLIN ${p[1]} ${st.status} ${st.slot} ${st.validCount} ${st.technicalCount} ${st.attemptCount} ${csv(trs.filter(t => t.valid).map(t => t.presentedK))}`];
    }
    case 'SUM': {
      const ST = { below: 'threshold_below_range', easy: 'threshold_near_easy_end', above: 'threshold_above_range', hard: 'threshold_near_hard_end', none: 'technical_failure' };
      const runs = p[2].split(',').map((kd, i) => {
        const q = kd.split(':');
        const result = q[0] === 'n' ? { status: 'complete_in_range', flags: [], thr: +q[1] / (1000 * +q[2]), thrRaw: +q[1] / (1000 * +q[2]), sumMilli: +q[1], count: +q[2] }
          : { status: ST[q[0]], flags: [] };
        return { id: 'r' + i, kind: 'adaptive', practice: false, order: i, result };
      });
      const s = Analysis.wonSummary(runs, 6);
      return [`SUM ${p[1]} ${s.state} ${s.exact ? s.exact.num + '/' + s.exact.den : '-'}`];
    }
    case 'BTAB': {
      const out = [];
      for (let n = 1; n <= +p[1]; n++) for (let k = 0; k <= n; k++) { const q = Exact.binomGeThird(k, n); out.push(`B ${n} ${k} ${q.num} ${q.den} ${b01(Exact.lt05(q))}`); }
      return out;
    }
    case 'FONE': {   // 표 하나 (합 41–150 — 앱의 분석 구간 크기)
      const [a, b, c, d] = p.slice(1, 5).map(Number), q = Exact.fisherGreater(a, b, c, d);
      return [`F ${a} ${b} ${c} ${d} ${q.num} ${q.den} ${b01(Exact.lt05(q))}`];
    }
    case 'FTAB': {
      const out = [], N = +p[1];
      for (let n = 0; n <= N; n++) for (let a = 0; a <= n; a++) for (let b = 0; b <= n - a; b++) for (let c = 0; c <= n - a - b; c++) {
        const d = n - a - b - c, q = Exact.fisherGreater(a, b, c, d);
        out.push(`F ${a} ${b} ${c} ${d} ${q.num} ${q.den} ${b01(Exact.lt05(q))}`);
      }
      return out;
    }
    case 'TTAB': {
      const out = [];
      for (let n = 1; n <= +p[1]; n++) for (let k = 0; k <= n; k++) out.push(`T ${n} ${k} ${b01(Stats.le(k, n, TARGET_P) < 0.05)} ${b01(Stats.ge(k, n, TARGET_P) < 0.05)}`);
      return out;
    }
    case 'TSUM': {
      const out = [];
      for (let n = 0; n <= +p[1]; n++) out.push(`TSUM ${n} ${2n ** BigInt(n)} 0`);
      return out;
    }
  }
  return [`? ${ln}`];
}

// ── 입력 만들기 ──
function mulberry32(a) { return () => { a |= 0; a = a + 0x6D2B79F5 | 0; let t = Math.imul(a ^ a >>> 15, 1 | a); t = t + Math.imul(t ^ t >>> 7, 61 | t) ^ t; return ((t ^ t >>> 14) >>> 0) / 4294967296; }; }
function makeInput() {
  const rnd = mulberry32(20261021);
  const hex32 = () => Array.from({ length: 4 }, () => Math.floor(rnd() * 4294967296).toString(16).padStart(8, '0')).join('');
  const seeds = ['00000001000000020000000300000004', '00000000000000000000000000000001', 'ffffffffffffffffffffffffffffffff', 'a3c59ac2f1e0477d9b8e3d1c5f7a2b64', '80000000000000000000000000000000'];
  while (seeds.length < 220) seeds.push(hex32());
  const L = [];
  for (const s of seeds.slice(0, 40)) L.push(`RNG ${s} 25`);
  const ns = [1, 2, 3, 5, 9, 12, 72, 1000, 65537, 2147483648, 4294967295, 4294967296, 3, 9, 7, 13, 3221225473, 2863311531, 2147483649];   // 끝의 셋은 다시 뽑기가 자주 일어나는 n
  for (const s of seeds.slice(0, 40)) L.push(`INT ${s} ${ns.join(',')}`);
  for (const s of seeds.slice(0, 40)) L.push(`PLAN ${s} 12`);
  for (const s of seeds) L.push(`ORDER ${s}`);
  // 적응 응답 순서: 모의 응답자 (참 역치 log2 rpo −4 … 4.5 · 기울기 · 실수율 · 기술적 실패 3 %) + 늘 찍음 · 늘 맞힘 · 늘 틀림 + 손 계산 · 극단 순서
  const seqs = ['CCCCWCCWWCWWCC', 'CCW'.repeat(60), 'C'.repeat(400), 'W'.repeat(400), 'X'.repeat(12), 'WWCC'.repeat(60), 'CX'.repeat(100), 'WX'.repeat(100), 'CCWX'.repeat(60), ''];
  // 두 끝을 오가는 응답 (분석 구간에서 두 끝 다 막힘 → 신뢰성 부족)
  for (const [u, d] of [[30, 20], [34, 18], [40, 25], [28, 16]]) seqs.push(('C'.repeat(u) + 'W'.repeat(d)).repeat(8));
  for (let i = 0; i < 3000; i++) {
    const model = i % 10;
    const mu = -4 + rnd() * 8.5, s = [0.3, 0.5, 0.8][i % 3], lapse = [0, 0.02, 0.1][(i >> 2) % 3], pX = [0, 0.03, 0.2][(i >> 4) % 3];
    let st = Stair.init(CFG), seq = '';
    while (st.status === 'running' && seq.length < 400) {
      const R = DENS_MILLI[st.k] / 1000;
      // model 3: 거꾸로 된 응답자 (촘촘할수록 잘 맞힘 — 0.125 정답률이 더 촘촘한 칸보다 낮음 → Fisher 신뢰성 부족)
    const pc = model === 0 ? 1 / 3 : model === 1 ? 1 : model === 2 ? 0 : model === 3 ? 0.15 + 0.8 / (1 + Math.exp(-(Math.log2(R) + 2.5) / 0.6))
      : 1 / 3 + (2 / 3 - lapse) * (1 - 1 / (1 + Math.exp(-(Math.log2(R) - mu) / s)));
      const ch = rnd() < pX ? 'X' : rnd() < pc ? 'C' : 'W';
      seq += ch;
      st = Stair.step(st, CFG, { trialId: 'g' + seq.length, presentedK: st.k, valid: ch !== 'X', correct: ch === 'C' }).state;
    }
    seqs.push(seq);
  }
  seqs.forEach((q, i) => L.push(`STAIR ${i} ${q || 'C'}`));
  seqs.forEach((q, i) => L.push(`CLASS ${i} ${q || 'C'}`));
  // 임상: 씨앗 + 응답 (정답 확률 0.4 … 0.95, 기술적 실패 0 · 3 · 20 %)
  for (let i = 0; i < 300; i++) {
    const pc = 0.4 + 0.55 * rnd(), pX = [0, 0.03, 0.2][i % 3];
    let q = ''; for (let j = 0; j < 100; j++) q += rnd() < pX ? 'X' : rnd() < pc ? 'C' : 'W';
    L.push(`CLIN ${i} ${seeds[i % seeds.length]} ${q}`);
  }
  // 회기 요약: 결과 종류 4 … 10 개 (숫자 · 끝 쪽 · 결정 안 됨)
  for (let i = 0; i < 3000; i++) {
    const n = 4 + Math.floor(rnd() * 7), mode = i % 5, out = [];
    for (let j = 0; j < n; j++) {
      const u = rnd();
      const kd = mode === 0 ? (u < 0.85 ? 'n' : 'none') : mode === 1 ? (u < 0.5 ? 'below' : u < 0.9 ? 'easy' : 'none') : mode === 2 ? (u < 0.5 ? 'above' : u < 0.9 ? 'hard' : 'none')
        : mode === 3 ? ['n', 'below', 'easy', 'above', 'hard', 'none'][Math.floor(u * 6)] : (u < 0.7 ? 'n' : 'below');
      out.push(kd === 'n' ? `n:${8 * 125 + Math.floor(rnd() * (8 * 11314 - 8 * 125 + 1))}:8` : kd);
    }
    L.push(`SUM ${i} ${out.join(',')}`);
  }
  L.push('BTAB 150', 'FTAB 40', 'TTAB 150', 'TSUM 150');
  // Fisher 한쪽 큰 표: 앱은 분석 구간 유효 시행(≤ 150)으로 표를 만듦 — 합 41–150 은 다 셀 수 없어(≈ 2,100만) 골라서
  const fr = mulberry32(20261022), fone = new Set();
  const addF = (a, b, c, d) => { if (a >= 0 && b >= 0 && c >= 0 && d >= 0) fone.add(`${a} ${b} ${c} ${d}`); };
  for (let n = 41; n <= 150; n++) {
    for (let r = 0; r < 60; r++) {   // 앱 꼴: fisherGreater(kh, H − kh, k0, A0 − k0) — 촘촘한 칸 H 시행 중 kh 맞음, 0.125 칸 A0 시행 중 k0 맞음
      const H = 1 + Math.floor(fr() * (n - 1)), A0 = n - H, kh = Math.floor(fr() * (H + 1)), k0 = Math.floor(fr() * (A0 + 1));
      addF(kh, H - kh, k0, A0 - k0);
    }
    for (let r = 0; r < 20; r++) { const a = Math.floor(fr() * (n + 1)), b = Math.floor(fr() * (n - a + 1)), c = Math.floor(fr() * (n - a - b + 1)); addF(a, b, c, n - a - b - c); }   // 아무 꼴
  }
  for (const n of [41, 64, 100, 128, 149, 150]) {   // 끝 표: 한 칸에 몰림 · 한 줄이 0 · 모두 맞음/틀림 · 반반 · 네 칸 고름
    const h = n >> 1, q = n >> 2;
    [[n, 0, 0, 0], [0, n, 0, 0], [0, 0, n, 0], [0, 0, 0, n], [h, n - h, 0, 0], [0, 0, h, n - h], [h, 0, 0, n - h], [0, h, n - h, 0],
      [n - 1, 0, 0, 1], [1, 0, 0, n - 1], [h, 0, n - h, 0], [0, h, 0, n - h], [q, q, q, n - 3 * q]].forEach(t => addF(...t));
  }
  for (const t of fone) L.push(`FONE ${t}`);
  return L;
}

// ── 비교 ──
function compare(js, lean) {
  const byType = {}, diffs = [];
  const n = Math.max(js.length, lean.length);
  for (let i = 0; i < n; i++) {
    const a = js[i], b = lean[i];
    const t = (a || b || '?').split(' ')[0];
    byType[t] = byType[t] || { same: 0, diff: 0 };
    if (a === b) byType[t].same++;
    else { byType[t].diff++; if (diffs.length < 30) diffs.push({ i, js: a, lean: b }); }
  }
  return { byType, diffs, nDiff: Object.values(byType).reduce((s, v) => s + v.diff, 0) };
}

const mode = Deno.args[0];
if (mode === 'input') {
  const L = makeInput();
  Deno.writeTextFileSync(Deno.args[1], L.join('\n') + '\n');
  const out = L.flatMap(jsLine);
  Deno.writeTextFileSync(Deno.args[2], out.join('\n') + '\n');
  console.log(`입력 ${L.length}줄 → js 기대 출력 ${out.length}줄`);
} else if (mode === 'check') {
  const rd = p => Deno.readTextFileSync(p).replace(/\r/g, '').split('\n').filter(x => x.length);
  const js = rd(Deno.args[1]), lean = rd(Deno.args[2]);
  const r = compare(js, lean);
  console.log(`js ${js.length}줄 · lean ${lean.length}줄`);
  for (const [t, v] of Object.entries(r.byType)) console.log(`  ${t.padEnd(6)} 같음 ${v.same} · 다름 ${v.diff}`);
  for (const d of r.diffs) console.log(`  다름 #${d.i}\n    js   ${String(d.js).slice(0, 300)}\n    lean ${String(d.lean).slice(0, 300)}`);
  // 변조 시험: 종류마다 첫 줄의 마지막 글자를 바꾼 lean 출력은 반드시 다르게 잡혀야 함
  const types = Object.keys(r.byType);
  let caught = 0;
  for (const t of types) {
    const i = lean.findIndex(x => x.startsWith(t + ' '));
    if (i < 0) continue;
    const m = lean.slice();
    const last = m[i].slice(-1);
    m[i] = m[i].slice(0, -1) + (last === '0' ? '1' : '0');
    if (compare(js, m).nDiff > r.nDiff) caught++;
  }
  const need = ['RNG', 'INT', 'PLAN', 'ORDER', 'STAIR', 'CLASS', 'CLIN', 'SUM', 'B', 'F', 'T', 'TSUM'];
  const missing = need.filter(t => !(r.byType[t] && r.byType[t].same + r.byType[t].diff > 0));
  console.log(`변조 시험: ${types.length}종 중 ${caught}종 잡음${missing.length ? ' · 비교 안 된 종류: ' + missing.join(' ') : ''}`);
  const ok = r.nDiff === 0 && js.length === lean.length && caught === types.length && !missing.length;
  console.log(`판정: ${ok ? '통과' : '실패'}`);
  Deno.exit(ok ? 0 : 1);
} else {
  console.log('사용: cross_check.js input <입력> <js출력> | check <js출력> <lean출력>');
  Deno.exit(2);
}
