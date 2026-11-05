// JS ↔ Lean 전수 대조의 JS 쪽 (Claude, 2026-10-31 — 와우SMD 1.1.0, 와우SRD tools/lean/cross_check.js 의 틀)
//   1) deno run --allow-read --allow-write tools/lean/cross_check.js input <입력.txt> <js출력.txt>
//        앱의 js 파일(rng · official · protocol · staircase · analysis)을 화면 없이 올려, 입력 줄과 같은 꼴의 기대 출력을 같은 순서로 씀
//        (자리 순열 검정은 비교하지 않으므로 이 대조 안에서만 PERM_B 를 2000 → 20 으로 줄여 빨리 돌림 — 앱 파일은 그대로)
//   2) (tools/lean 에서) .lake/build/bin/crosscheck.exe <입력.txt> <lean출력.txt>
//   3) deno run --allow-read tools/lean/cross_check.js check <js출력.txt> <lean출력.txt>
//        한 줄씩 비교 → 종류마다 같은 줄 수 · 다른 줄 (처음 30개) · 변조 시험(종류마다 한 줄을 일부러 바꾼 출력은 반드시 다르게 나와야 함)
//        마지막 줄 ‘판정: 통과/실패’ — 다른 줄이 있거나, 비교한 종류가 비거나, 변조를 못 잡으면 종료 코드 1
//   4) deno run --allow-read tools/lean/cross_check.js mutants <입력.txt> <lean출력.txt>
//        검산기 검증: 앱 js 에 일부러 결함을 하나씩 넣은 판(메모리 안에서만 — 파일은 그대로)으로 기대 출력을 다시 만들어 lean 출력과 맞댐 →
//        결함마다 기대한 종류의 줄이 달라져야(또는 예외) ‘잡음’. 하나라도 못 잡으면 종료 코드 1
const root = new URL('../../', import.meta.url);
const files = ['js/rng.js', 'js/official.js', 'js/protocol.js', 'js/staircase.js', 'js/analysis.js'];
const SRC = Object.fromEntries(files.map(f => [f, Deno.readTextFileSync(new URL(f, root))]));
const PERM_SRC = 'const PERM_B = 2000;';
// 앱 js 를 한 범위에 올림 (mut: 한 파일의 한 곳을 바꾼 판 — 정확히 한 번 나와야 함). 간접 eval 이라 판마다 따로 범위가 생김
function load(mut) {
  const src = { ...SRC };
  if (mut) {
    const parts = src[mut.file].split(mut.from);
    if (parts.length !== 2) throw new Error(`결함 ${mut.id}: ${mut.file} 에서 바꿀 곳을 정확히 한 번 찾지 못함 (${parts.length - 1}번)`);
    src[mut.file] = parts.join(mut.to);
  }
  const parts = src['js/analysis.js'].split(PERM_SRC);
  if (parts.length !== 2) throw new Error('analysis.js 의 PERM_B 줄을 찾지 못함 — 대조 틀을 고칠 것');
  src['js/analysis.js'] = parts.join('const PERM_B = 20;');
  let code = '';
  for (const f of files) code += `\n// ── ${f} ──\n` + src[f];
  code += '\n;globalThis.__A = { Rng, TrialPlan, ConstPlan, Exact, Stats, ConstRun, Analysis, Stair, PROTOCOLS, OFFICIAL, qsmdCell, TARGET_P };\n';
  (0, eval)(code);
  return globalThis.__A;
}
let Rng, TrialPlan, ConstPlan, Exact, Stats, ConstRun, Analysis, Stair, PROTOCOLS, OFFICIAL, qsmdCell, TARGET_P, PW, PQ, CFG, CCFG;
function use(A) {
  ({ Rng, TrialPlan, ConstPlan, Exact, Stats, ConstRun, Analysis, Stair, PROTOCOLS, OFFICIAL, qsmdCell, TARGET_P } = A);
  PW = PROTOCOLS.won2015; PQ = PROTOCOLS.qsmd;
  CFG = Stair.cfgFrom(PW); CCFG = ConstRun.cfgFrom(PQ);
}
use(load(null));
// 일부러 넣는 결함 (검산기 검증용) — 기대: 그 결함이 바꾸는 종류의 줄
const MUTANTS = [
  { id: 'M1', file: 'js/analysis.js', from: 'third = Q.cmp(dq, Q.int(3)) > 0', to: 'third = Q.cmp(dq, Q.int(3)) >= 0', expect: ['SUM'], what: '회기 요약: 3 dB 경계 > → ≥' },
  { id: 'M2', file: 'js/analysis.js', from: '(!lastDrop || t.tr.validNo > lastDrop.validNo)', to: '(!lastDrop || t.tr.validNo >= lastDrop.validNo)', expect: ['CLASS'], what: '분석 구간이 4번째 반전 시행부터 (한 시행 앞)' },
  { id: 'M3', file: 'js/staircase.js', from: 'revCount < cfg.switchFrom ? cfg.coarseH : cfg.fineH', to: 'revCount <= cfg.switchFrom ? cfg.coarseH : cfg.fineH', expect: ['STAIR', 'CLASS'], what: '0.5 dB step 을 반전 한 번 늦게' },
  { id: 'M4', file: 'js/analysis.js', from: "if (next.technicalCount >= cfg.maxTechnical) next.status = 'technical_failure';", to: "if (next.technicalCount > cfg.maxTechnical) next.status = 'technical_failure';", expect: ['CONST'], what: 'QSMD 기술적 실패 상한 10 → 11' },
  { id: 'M5', file: 'js/analysis.js', from: 'const z = valid.filter(t => t.h === 0)', to: 'const z = valid.filter(t => t.h <= 1)', expect: ['CLASS'], what: '0 dB 검정에 0.5 dB 시행이 섞임' },
  { id: 'M6', file: 'js/analysis.js', from: 'const same = a.kind === b.kind || (UP.has(a.kind) && UP.has(b.kind));', to: 'const same = a.kind === b.kind;', expect: ['SUM'], what: '회기 요약: 높은 쪽(above · ceil · up) 묶음 규칙 빠짐' },
  { id: 'M7', file: 'js/analysis.js', from: 'bound.ceilWin.pBelowTarget < 0.05', to: 'bound.ceilWin.pBelowTarget < 0.1', expect: ['CLASS'], what: '위 끝 정답률 아래 확인 기준 .05 → .1' },
  { id: 'M8', file: 'js/analysis.js', from: '{ const j = rng.int(i + 1); const t = a[i]; a[i] = a[j]; a[j] = t; }', to: '{ const j = rng.int(i); const t = a[i]; a[i] = a[j]; a[j] = t; }', expect: ['ORDER', 'CONST'], what: 'QSMD 순서 섞기 j = int(i) (Sattolo)' },
  { id: 'M9', file: 'js/analysis.js', from: 'bound.win.n && bound.win.pBelowTarget < 0.05', to: 'bound.win.n && bound.win.pBelowTarget < 0.01', expect: ['CLASS'], what: '수렴 점검 기준 p < .05 → .01' },
  { id: 'M10', file: 'js/analysis.js', from: 'const roves = [0, 1, 2].map(() => rng.int(5) - 2);', to: 'const roves = [0, 1, 2].map(() => rng.int(5) - 3);', expect: ['PLAN'], what: '크기 흔들기 −2…+2 → −3…+1' },
];
const csv = a => a.length ? a.join(',') : '-';
const b01 = x => x ? '1' : '0';

// ── 줄마다 js 기대 출력 ──
function feedStair(seq) {
  let st = Stair.init(CFG);
  const trs = [];
  for (let i = 0; i < seq.length; i++) {
    if (st.status !== 'running') break;
    const ch = seq[i];
    const r = Stair.step(st, CFG, { trialId: 't' + i, presentedH: st.h, valid: ch !== 'X', correct: ch === 'C', reason: ch === 'X' ? 'technical' : null });
    trs.push(r.tr); st = r.state;
  }
  return { st, trs };
}
const MOVE = { MOVE: 'M', STAY: 'S', BLOCKED_ZERO_MOVE: 'B', INVALID_NO_CHANGE: 'X' };
const BND = v => v === 'ceiling' ? 1 : v === 'floor' ? 2 : 0;
const DIR = d => d < 0 ? '-' : d > 0 ? '+' : '0';
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
      for (let i = 0; i < +p[2]; i++) { const d = TrialPlan.draw(r); out.push(`PLAN ${p[1]} ${i} ${d.targetPos} ${d.phiU} ${d.seeds.join(',')} ${d.roves.join(',')} ${d.rngAfter}`); }
      return out;
    }
    case 'ORDER': {
      const r = Rng.fromHex(p[1]);
      const o = ConstPlan.order(r, CCFG.cells, CCFG.per);
      return [`ORDER ${p[1]} ${csv(o)} ${r.hex()}`];
    }
    case 'QTAB': {
      const it = OFFICIAL.items.map((_, i) => qsmdCell(PQ, i));   // qsmdCell 이 목록 · 절차 일관성을 확인 (어긋나면 예외)
      return [`QTAB ${csv(it.map(x => x.cell))} ${csv(it.map(x => x.answer))} ${csv(it.map(x => x.h))}`];
    }
    case 'STAIR': {
      const { st, trs } = feedStair(p[2]);
      const th = Stair.threshold(st, CFG);
      return [`STAIR ${p[1]} ${st.status} ${st.h} ${st.correctStreak} ${st.lastDir === null ? 0 : st.lastDir} ${st.validCount} ${st.technicalCount} ${st.attemptCount} ${st.moves} ` +
        `${csv(st.reversals.map(r => r.h))} ${csv(st.reversals.map(r => r.validNo))} ${csv(st.reversals.map(r => BND(r.atBound)))} ${th ? th.sumH + '/' + th.count : '-'} ` +
        `${trs.map(t => MOVE[t.move]).join('')} ${trs.map(t => BND(t.blockedAt)).join('')} ${trs.map(t => DIR(t.requestedDir)).join('')} ` +
        `${trs.map(t => t.requestedStepH).join('')} ${trs.map(t => t.effectiveStepH).join('')} ${trs.filter(t => t.clamped).length} ${trs.map(t => t.postStreak).join('')}`];
    }
    case 'CLASS': {
      const { st, trs } = feedStair(p[2]);
      const trials = trs.map((tr, i) => {
        const tp = 1 + (i % 3);
        return { id: 't' + i, valid: tr.valid, correct: tr.correct, h: tr.presentedH, cond: 'd1', tr, targetPos: tp, response: tr.valid ? (tr.correct ? tp : (tp % 3) + 1) : null };
      });
      const run = { kind: 'adaptive', state: st, trials, seed: '0123456789abcdef0123456789abcdef' };
      const x = Analysis.classifyAdaptive(run, CFG), b = x.bound, f = x.flags;
      const bs = b ? [b.nWin, b.win.k, b.ceilBlocksWin, b.floorBlocksWin, b.ceilBlocksBefore, b01(b.touchedCeil), b01(b.touchedFloor), b.ceilWin.n, b.ceilWin.k, b.lowerWin.n, b.lowerWin.k].join(',') : '-';
      return [`CLASS ${p[1]} ${x.status} ${x.reason || '-'} ${b01(f.includes('near_ceiling'))} ${b01(f.includes('near_floor'))} ${b01(f.includes('early_ceiling_errors'))} ${b01(f.includes('zero_above_chance'))} ` +
        `${b01(f.includes('track_not_above_chance'))} ${x.status === 'complete_in_range' ? x.sumH + '/' + x.count : '-'} ${bs} ${b01(b && b.sigCeilWorse)} ` +
        `${b01(b && b.ceilWin.n && b.ceilWin.pBelowTarget < 0.05)} ${b01(b && b.win.n && b.win.pBelowTarget < 0.05)} ${x.zero.n} ${x.zero.k}`];
    }
    case 'CONST': {
      const order = ConstPlan.order(Rng.fromHex(p[2]), CCFG.cells, CCFG.per);
      let st = ConstRun.init(CCFG, order); const trs = [];
      for (let i = 0; i < p[3].length; i++) {
        if (st.status !== 'running') break;
        const ch = p[3][i];
        const r = ConstRun.step(st, CCFG, order, { trialId: 'c' + i, presentedCell: st.cell, valid: ch !== 'X', correct: ch === 'C', reason: ch === 'X' ? 'technical' : null });
        trs.push(r.tr); st = r.state;
      }
      const trials = trs.map((tr, i) => {
        const c = qsmdCell(PQ, tr.presentedCell);
        return { id: 'c' + i, valid: tr.valid, correct: tr.correct, cell: tr.presentedCell, h: c.h, cond: c.cond, tr, targetPos: c.answer,
          response: tr.valid ? (tr.correct ? c.answer : (c.answer % 3) + 1) : null };
      });
      const x = Analysis.classifyConstant({ kind: 'constant', state: st, trials, seed: p[2] }, PQ);
      return [`CONST ${p[1]} ${st.status} ${st.slot} ${st.validCount} ${st.technicalCount} ${st.attemptCount} ${st.cell === null ? '-' : st.cell} ` +
        `${csv(trs.map(t => t.slot))} ${csv(trs.map(t => t.presentedCell))} ${csv(trs.filter(t => t.valid).map(t => t.presentedCell))} ${x.status} ` +
        `${x.pc === null ? '-' : x.nCorrect + '/' + x.nValid} ${b01(x.notAboveChance)}`];
    }
    case 'SUM': {
      const ST = { above: 'threshold_above_range', ceil: 'threshold_near_ceiling', up: 'threshold_above_window', floor: 'threshold_near_floor', none: 'technical_failure' };
      const runs = p[2].split(',').map((kd, i) => {
        const q = kd.split(':');
        const result = q[0] === 'n' ? { status: 'complete_in_range', flags: [], thr: +q[1] / (2 * +q[2]), thrRaw: +q[1] / (2 * +q[2]), sumH: +q[1], count: +q[2] }
          : { status: ST[q[0]], flags: [] };
        return { id: 'r' + i, kind: 'adaptive', practice: false, order: i, result };
      });
      const s = Analysis.condSummary(runs);
      return [`SUM ${p[1]} ${s.state} ${s.exact ? s.exact.num + '/' + s.exact.den : '-'} ${s.needMore} ${s.used.length}`];
    }
    case 'BTAB': {
      const out = [];
      for (let n = 1; n <= +p[1]; n++) for (let k = 0; k <= n; k++) { const q = Exact.binomGeThird(k, n); out.push(`B ${n} ${k} ${q.num} ${q.den} ${b01(Exact.lt05(q))}`); }
      return out;
    }
    case 'FONE': {   // 표 하나 (합 41–200 — 앱의 분석 구간 크기)
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
  const rnd = mulberry32(20261031);
  const hex32 = () => Array.from({ length: 4 }, () => Math.floor(rnd() * 4294967296).toString(16).padStart(8, '0')).join('');
  const seeds = ['00000001000000020000000300000004', '00000000000000000000000000000001', 'ffffffffffffffffffffffffffffffff', 'a3c59ac2f1e0477d9b8e3d1c5f7a2b64', '80000000000000000000000000000000'];
  while (seeds.length < 220) seeds.push(hex32());
  const L = [];
  for (const s of seeds.slice(0, 40)) L.push(`RNG ${s} 25`);
  const ns = [1, 2, 3, 5, 9, 12, 60, 1000, 65537, 2147483648, 4294967295, 4294967296, 3, 9, 7, 13, 3221225473, 2863311531, 2147483649];   // 끝의 셋은 다시 뽑기가 자주 일어나는 n
  for (const s of seeds.slice(0, 40)) L.push(`INT ${s} ${ns.join(',')}`);
  for (const s of seeds.slice(0, 40)) L.push(`PLAN ${s} 12`);
  for (const s of seeds) L.push(`ORDER ${s}`);
  L.push('QTAB');
  // 적응 응답 순서: 모의 응답자 (참 역치 −5 … 70 dB · 기울기 · 실수율 · 기술적 실패) + 늘 찍음 · 늘 맞힘 · 늘 틀림 · 거꾸로(얕을수록 잘함) + 손 계산 · 극단 순서
  const seqs = ['CCCCWCCWWCWWCC', 'CCW'.repeat(60), 'C'.repeat(400), 'W'.repeat(400), 'X'.repeat(12), 'WWCC'.repeat(60), 'CX'.repeat(100), 'WX'.repeat(100), 'CCWX'.repeat(60), '',
    'W'.repeat(21) + 'CCW'.repeat(80), 'W'.repeat(20) + 'CCWCCW' + 'WWW' + 'W'.repeat(10) + 'CC' + 'CCCCCC' + 'WCC'.repeat(4) + 'W', 'C'.repeat(19) + 'W' + 'CCW'.repeat(80)];
  // 두 끝을 오가는 응답 (분석 구간에서 두 끝 다 막힘 → 신뢰성 부족)
  for (const [u, d] of [[40, 40], [44, 38], [50, 45], [36, 30]]) seqs.push(('C'.repeat(u) + 'W'.repeat(d)).repeat(4));
  // 손으로 짠 경로 (위 모의로는 안 나오는 판정): 4번째 반전 뒤 바닥에 막힘 → 0.5 dB 씩 위 끝까지 올라가 막힘 (두 끝 다 막힘 → 신뢰성 부족, 유효 169 · 173) ·
  //   위 끝 막힘 40번을 앞에 몰고 마지막 20 시행은 가운데에서 내려감 (반전 5번 · 유효 200 → 시행 상한 그대로 · 앞부분 위 끝 막힘 표시)
  seqs.push('C'.repeat(20) + 'WCCWCC' + 'C'.repeat(6) + 'CC' + 'W'.repeat(121) + 'CCW'.repeat(4) + 'CC',
    'C'.repeat(20) + 'WCCWCC' + 'C'.repeat(6) + 'CCCC' + 'W'.repeat(123) + 'CCW'.repeat(4) + 'CC',
    'WCCWCCW' + 'W'.repeat(79) + 'W'.repeat(40) + 'C'.repeat(74));
  for (let i = 0; i < 3000; i++) {
    const model = i % 12;
    const mu = -5 + rnd() * 75, s = [1.5, 3, 6][i % 3], lapse = [0, 0.02, 0.1][(i >> 2) % 3], pX = [0, 0.03, 0.2][(i >> 4) % 3];
    let st = Stair.init(CFG), seq = '';
    while (st.status === 'running' && seq.length < 400) {
      const D = st.h / 2;
      // model 3: 거꾸로 된 응답자 (얕을수록 잘 맞힘 — 위 끝 정답률이 더 얕은 깊이보다 낮음 → Fisher 신뢰성 부족) · model 4: 0 dB 에서도 잘 맞힘 (경로 단서)
      const pc = model === 0 ? 1 / 3 : model === 1 ? 1 : model === 2 ? 0 : model === 3 ? 0.15 + 0.8 / (1 + Math.exp((D - 25) / 4))
        : model === 4 ? (D === 0 ? 0.9 : 1 / 3 + (2 / 3) / (1 + Math.exp(-(D - mu) / s)))
        : 1 / 3 + (2 / 3 - lapse) / (1 + Math.exp(-(D - mu) / s));
      const ch = rnd() < pX ? 'X' : rnd() < pc ? 'C' : 'W';
      seq += ch;
      st = Stair.step(st, CFG, { trialId: 'g' + seq.length, presentedH: st.h, valid: ch !== 'X', correct: ch === 'C' }).state;
    }
    seqs.push(seq);
  }
  seqs.forEach((q, i) => L.push(`STAIR ${i} ${q || 'C'}`));
  seqs.forEach((q, i) => L.push(`CLASS ${i} ${q || 'C'}`));
  // QSMD: 씨앗 + 응답 (정답 확률 0.25 … 0.95, 기술적 실패 0 · 3 · 20 % · 기술적 실패 몰림)
  const cseq = ['C'.repeat(60), 'W'.repeat(60), 'X'.repeat(10), 'X'.repeat(9) + 'C'.repeat(60), 'CX'.repeat(9) + 'C'.repeat(60), 'C'.repeat(59) + 'X'.repeat(10), 'C'.repeat(59), ''];
  for (let i = 0; i < 300; i++) {
    const pc = 0.25 + 0.7 * rnd(), pX = [0, 0.03, 0.2][i % 3];
    let q = ''; for (let j = 0; j < 100; j++) q += rnd() < pX ? 'X' : rnd() < pc ? 'C' : 'W';
    cseq.push(q);
  }
  cseq.forEach((q, i) => L.push(`CONST ${i} ${seeds[i % seeds.length]} ${q || 'C'}`));
  // 회기 요약: 결과 종류 1 … 8 개 (숫자 · 끝 쪽 · 결정 안 됨) + 3 dB 경계 (|S1 − S2| = 60 은 정확히 3 dB → 3번째 안 함, 61 → 3번째)
  const kinds = ['above', 'ceil', 'up', 'floor', 'none'];
  const numK = () => { const c = rnd() < 0.85 ? 10 : [1, 7, 12][Math.floor(rnd() * 3)]; return `n:${Math.floor(rnd() * (120 * c + 1))}:${c}`; };
  for (let i = 0; i < 3000; i++) {
    const n = 1 + Math.floor(rnd() * 8), mode = i % 6, out = [];
    for (let j = 0; j < n; j++) {
      const u = rnd();
      out.push(mode === 0 ? (u < 0.85 ? numK() : 'none') : mode === 1 ? (u < 0.4 ? 'above' : u < 0.7 ? 'ceil' : u < 0.9 ? 'up' : 'none')
        : mode === 2 ? (u < 0.5 ? 'floor' : u < 0.8 ? numK() : 'none') : mode === 3 ? (u < 0.5 ? numK() : kinds[Math.floor(rnd() * 5)])
        : mode === 4 ? kinds[Math.floor(u * 5)] : (u < 0.7 ? numK() : 'up'));
    }
    L.push(`SUM ${i} ${out.join(',')}`);
  }
  let si = 3000;
  for (const d of [59, 60, 61, -59, -60, -61, 0, 1, -1]) for (const S of [0, 300, 600, 1140]) {
    const S2 = S + d;
    if (S2 < 0 || S2 > 1200) continue;
    L.push(`SUM ${si++} n:${S}:10,n:${S2}:10`, `SUM ${si++} n:${S}:10,n:${S2}:10,n:${(S + S2) >> 1}:10`, `SUM ${si++} none,n:${S}:10,none,n:${S2}:10,above`);
  }
  for (const [a, b] of [[60 * 7, 7], [3 * 12, 12]]) L.push(`SUM ${si++} n:${a}:${b},n:${a + 3 * 2 * b}:${b}`, `SUM ${si++} n:${a}:${b},n:${a + 3 * 2 * b + 1}:${b}`);   // 개수가 10 이 아닐 때의 경계
  L.push('BTAB 200', 'FTAB 40', 'TTAB 200', 'TSUM 200');
  // Fisher 한쪽 큰 표: 앱은 분석 구간 유효 시행(≤ 200)으로 표를 만듦 — 합 41–200 은 다 셀 수 없어 골라서
  const fr = mulberry32(20261101), fone = new Set();
  const addF = (a, b, c, d) => { if (a >= 0 && b >= 0 && c >= 0 && d >= 0) fone.add(`${a} ${b} ${c} ${d}`); };
  for (let n = 41; n <= 200; n++) {
    for (let r = 0; r < 40; r++) {   // 앱 꼴: fisherGreater(kl, L − kl, kc, C − kc) — 더 얕은 깊이 L 시행 중 kl 맞음, 위 끝 C 시행 중 kc 맞음
      const Lw = 1 + Math.floor(fr() * (n - 1)), C = n - Lw, kl = Math.floor(fr() * (Lw + 1)), kc = Math.floor(fr() * (C + 1));
      addF(kl, Lw - kl, kc, C - kc);
    }
    for (let r = 0; r < 10; r++) { const a = Math.floor(fr() * (n + 1)), b = Math.floor(fr() * (n - a + 1)), c = Math.floor(fr() * (n - a - b + 1)); addF(a, b, c, n - a - b - c); }   // 아무 꼴
  }
  for (const n of [41, 64, 100, 128, 150, 199, 200]) {   // 끝 표: 한 칸에 몰림 · 한 줄이 0 · 모두 맞음/틀림 · 반반 · 네 칸 고름
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
  const need = ['RNG', 'INT', 'PLAN', 'ORDER', 'QTAB', 'STAIR', 'CLASS', 'CONST', 'SUM', 'B', 'F', 'T', 'TSUM'];
  const missing = need.filter(t => !(r.byType[t] && r.byType[t].same + r.byType[t].diff > 0));
  console.log(`변조 시험: ${types.length}종 중 ${caught}종 잡음${missing.length ? ' · 비교 안 된 종류: ' + missing.join(' ') : ''}`);
  const ok = r.nDiff === 0 && js.length === lean.length && caught === types.length && !missing.length;
  console.log(`판정: ${ok ? '통과' : '실패'}`);
  Deno.exit(ok ? 0 : 1);
} else if (mode === 'mutants') {
  const rd = p => Deno.readTextFileSync(p).replace(/\r/g, '').split('\n').filter(x => x.length);
  const input = rd(Deno.args[1]), lean = rd(Deno.args[2]);
  let killed = 0;
  for (const m of MUTANTS) {
    let out, err = null;
    try {
      use(load(m));
      out = [];
      for (const ln of input) { try { for (const x of jsLine(ln)) out.push(x); } catch (e) { err = err || e.message; out.push(`! ${ln.split(' ')[0]} 예외`); } }
    } catch (e) { err = e.message; out = null; }
    const r = out ? compare(out, lean) : null;
    const hit = r ? m.expect.filter(t => r.byType[t] && r.byType[t].diff > 0) : [];
    const got = r ? Object.entries(r.byType).filter(([, v]) => v.diff > 0).map(([t, v]) => `${t} ${v.diff}`).join(' · ') : '';
    const ok = !!(r && hit.length);
    if (ok) killed++;
    console.log(`  ${m.id.padEnd(4)} ${ok ? '잡음' : '못 잡음'} — ${m.what}: 다른 줄 ${got || '없음'}${err ? ' · 예외 ' + String(err).slice(0, 80) : ''}`);
  }
  use(load(null));
  console.log(`검산기 검증: 일부러 넣은 결함 ${MUTANTS.length}개 중 ${killed}개 잡음`);
  console.log(`판정: ${killed === MUTANTS.length ? '통과' : '실패'}`);
  Deno.exit(killed === MUTANTS.length ? 0 : 1);
} else {
  console.log('사용: cross_check.js input <입력> <js출력> | check <js출력> <lean출력> | mutants <입력> <lean출력>');
  Deno.exit(2);
}
