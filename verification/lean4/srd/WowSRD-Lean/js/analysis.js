// 시행 계획·결과 분류·기록 다시 계산·회기 요약(잠정/확정/범위 밖)·제시 설정 묶음·회기 순서 — 순수 함수
'use strict';

const TWO32 = 4294967296;
const TARGET_P = Math.SQRT1_2;   // 2-up 1-down 이 따라가는 정답률 1/√2 ≈ 70.7 % (3선택이어도 같음)
function seedHexOf(words) {
  const w = words.map(x => x >>> 0);
  if (!(w[0] | w[1] | w[2] | w[3])) w[0] = 1;   // xoshiro 상태는 모두 0 이면 안 됨 (확률 2^-128)
  return w.map(v => v.toString(16).padStart(8, '0')).join('');
}

// 시행마다 (이 순서 그대로 — tools/srd_reference.py plan_draw 와 같음):
//   다른 소리 자리 int(3) → 무늬 위상 u32 → 구간 1·2·3 씨앗 u32×4 씩 → 구간 1·2·3 크기 흔들기 int(9) − 4
// 무늬 위상은 고정 위상 절차(Won 2007)에서도 뽑음 (난수 소비가 절차와 상관없게) — 쓰지 않을 뿐
const TrialPlan = {
  draw(rng) {
    const rngBefore = rng.hex();
    const targetPos = rng.int(3) + 1;
    const thetaU = rng.u32();
    const theta = 2 * Math.PI * (thetaU / TWO32);
    const seeds = [0, 1, 2].map(() => seedHexOf([rng.u32(), rng.u32(), rng.u32(), rng.u32()]));
    const roves = [0, 1, 2].map(() => rng.int(9) - 4);
    return { rngBefore, targetPos, thetaU, theta, seeds, roves, rngAfter: rng.hex() };
  },
};
// 임상(항상자극법) 순서: k 를 [0×per, 1×per, …] 로 늘어놓고 Fisher–Yates (뒤에서부터 j = int(i+1)) — run 씨앗 RNG 의 맨 처음 소비
const ConstPlan = {
  order(rng, densIdx, per) {
    const a = [];
    for (const k of densIdx) for (let r = 0; r < per; r++) a.push(k);
    for (let i = a.length - 1; i > 0; i--) { const j = rng.int(i + 1); const t = a[i]; a[i] = a[j]; a[j] = t; }
    return a;
  },
};

// 정확한 정수 계산 (BigInt) — 판정에 쓰는 유리수 p 값. p = { num, den } (BigInt), 판정 p < .05 ⟺ 20·num < den
const Exact = (() => {
  const rows = [[1n]];
  function binomRow(n) {
    while (rows.length <= n) {
      const m = rows.length, prev = rows[m - 1], r = new Array(m + 1);
      r[0] = 1n; r[m] = 1n;
      for (let j = 1; j < m; j++) r[j] = prev[j - 1] + prev[j];
      rows.push(r);
    }
    return rows[n];
  }
  const C = (n, k) => (k < 0 || k > n) ? 0n : binomRow(n)[k];
  const lt05 = p => p !== null && 20n * p.num < p.den;
  const toNum = p => p === null ? null : Number(p.num * 1000000000000n / p.den) / 1e12;
  // 한쪽 이항 P(X ≥ k | n, 1/3) = Σ_{j≥k} C(n,j)·2^(n−j) / 3^n
  function binomGeThird(k, n) {
    if (!n) return null;
    let s = 0n;
    for (let j = Math.max(0, k); j <= n; j++) s += C(n, j) * (2n ** BigInt(n - j));
    return { num: s, den: 3n ** BigInt(n) };
  }
  // Fisher 한쪽: 첫 행 정답 비율이 둘째 행보다 높은가 — P(X ≥ a | 여백 고정), [[a, b], [c, d]]
  function fisherGreater(a, b, c, d) {
    const r1 = a + b, r2 = c + d, c1 = a + c, n = r1 + r2;
    if (!r1 || !r2 || !c1 || c1 === n) return { num: 1n, den: 1n };
    let s = 0n;
    for (let x = a; x <= Math.min(r1, c1); x++) s += C(r1, x) * C(r2, c1 - x);
    return { num: s, den: C(n, c1) };
  }
  // 2×m 정확 검정 (Freeman–Halton): 열(자리)마다 n_j 시행 중 맞힌 x_j — 여백 고정에서 관찰 확률 이하인 표의 확률 합
  function fisher2xm(xs, ns) {
    const N = ns.reduce((s, v) => s + v, 0), K = xs.reduce((s, v) => s + v, 0);
    if (!N || ns.filter(v => v > 0).length < 2 || K === 0 || K === N) return { num: 1n, den: 1n };
    const obs = xs.reduce((p, x, j) => p * C(ns[j], x), 1n);
    let s = 0n;
    const rec = (j, left, prod) => {
      if (j === ns.length - 1) { if (left <= ns[j]) { const q = prod * C(ns[j], left); if (q <= obs) s += q; } return; }
      for (let x = Math.max(0, left - ns.slice(j + 1).reduce((a, b) => a + b, 0)); x <= Math.min(ns[j], left); x++) rec(j + 1, left - x, prod * C(ns[j], x));
    };
    rec(0, K, 1n);
    return { num: s, den: C(N, K) };
  }
  // 응답 자리 고르기 (다항 균등 1/m 정확 검정): 관찰 확률 이하인 모든 (r_1…r_m) 의 확률 합
  function multinomUniform(rs) {
    const n = rs.reduce((s, v) => s + v, 0), m = rs.length;
    if (!n || m < 2) return { num: 1n, den: 1n };
    const mult = v => { let p = 1n, left = n; for (const x of v) { p *= C(left, x); left -= x; } return p; };
    const obs = mult(rs);
    let s = 0n;
    const rec = (j, left, v) => {
      if (j === m - 1) { const q = mult([...v, left]); if (q <= obs) s += q; return; }
      for (let x = 0; x <= left; x++) rec(j + 1, left - x, [...v, x]);
    };
    rec(0, n, []);
    return { num: s, den: BigInt(m) ** BigInt(n) };
  }
  const str = p => p === null ? null : { num: p.num.toString(), den: p.den.toString() };
  return { C, binomRow, lt05, toNum, binomGeThird, fisherGreater, fisher2xm, multinomUniform, str };
})();

const Stats = (() => {
  function pmfs(n, p) {   // 이항 확률 0…n (로그로 계산해 넘침 방지) — 1/√2 처럼 무리수 확률에 씀
    const out = new Array(n + 1);
    let lc = 0;
    const lp = Math.log(p), lq = Math.log(1 - p);
    for (let k = 0; k <= n; k++) {
      if (k > 0) lc += Math.log((n - k + 1) / k);
      out[k] = Math.exp(lc + (p > 0 ? k * lp : (k ? -Infinity : 0)) + (p < 1 ? (n - k) * lq : (n - k ? -Infinity : 0)));
    }
    return out;
  }
  const ge = (k, n, p) => pmfs(n, p).slice(k).reduce((a, b) => a + b, 0);       // P(X ≥ k)
  const le = (k, n, p) => pmfs(n, p).slice(0, k + 1).reduce((a, b) => a + b, 0); // P(X ≤ k)
  function clopperPearson(k, n, alpha = 0.05) {
    if (!n) return null;
    const bis = (f) => { let lo = 0, hi = 1; for (let i = 0; i < 60; i++) { const m = (lo + hi) / 2; if (f(m)) hi = m; else lo = m; } return (lo + hi) / 2; };
    const lower = k === 0 ? 0 : bis(p => ge(k, n, p) >= alpha / 2);
    const upper = k === n ? 1 : bis(p => le(k, n, p) <= alpha / 2);
    return [lower, upper];
  }
  const mean = a => a.length ? a.reduce((s, x) => s + x, 0) / a.length : null;
  const sd = a => a.length > 1 ? Math.sqrt(a.reduce((s, x) => s + (x - mean(a)) ** 2, 0) / (a.length - 1)) : null;
  return { pmfs, ge, le, clopperPearson, mean, sd };
})();

// 제시 설정 — 같은 설정으로 잰 측정끼리만 평균·비교한다 (경로·볼륨·처리기 프로그램·기능·Windows 출력·귀·유지 신호) — 와우STM 과 같음
const Pres = (() => {
  const ROUTE_KEYS = ['rType', 'rOut', 'rDac', 'rStreamer', 'rStreamerFw', 'rProc', 'rProcFw', 'rMap', 'rMix', 'rMixOther', 'rOsVol', 'rAppVol', 'rStrVol', 'rProcVol', 'rContra', 'rResid', 'rRoom'];
  const LABEL = { ear: '검사 귀', keep: '시행 사이 유지 신호', procNow: '처리기 프로그램·볼륨(회기 칸)', rType: '경로 유형', rOut: '컴퓨터 출력 장치(칸)', rDac: 'DAC·케이블',
    rStreamer: '스트리머', rStreamerFw: '스트리머 펌웨어', rProc: '처리기 모델', rProcFw: '처리기 펌웨어', rMap: '임상 맵', rMix: '마이크·스트림 섞기', rMixOther: '섞기 비율',
    rOsVol: 'Windows 볼륨(칸)', rAppVol: '브라우저 볼륨', rStrVol: '스트리머 볼륨', rProcVol: '처리기 볼륨·감도', rContra: '반대쪽 귀', rResid: '남은 청력', rRoom: '방',
    'win.endpoint': 'Windows 출력 장치', 'win.vol': 'Windows 볼륨(자동)', 'win.mute': '음소거', 'win.fx': '소리 향상', win: 'Windows 오디오' };
  const winEss = w => (w && w.ok) ? { endpoint: w.endpointId || w.endpointName || null, vol: Math.round(+w.volume100), mute: !!w.mute, fx: w.sysFx || null } : null;
  function of(route, procNow, ear, keep, win) {
    const r = route || {};
    const o = { ear: ear || null, keep: keep || null, procNow: String(procNow || '').trim() };
    for (const k of ROUTE_KEYS) o[k] = r[k] === undefined || r[k] === '' ? null : r[k];
    o.features = Object.fromEntries(Object.entries(r.features || {}).map(([k, v]) => [k, (v && v.state) || 'unknown']).sort((a, b) => a[0].localeCompare(b[0])));
    o.win = winEss(win);
    return o;
  }
  const key = p => canonical(p);
  function flat(p) {
    const o = {};
    for (const [k, v] of Object.entries(p)) if (k !== 'features' && k !== 'win') o[k] = v;
    for (const [k, v] of Object.entries(p.features || {})) o['features.' + k] = v;
    if (p.win) for (const [k, v] of Object.entries(p.win)) o['win.' + k] = v; else o.win = '읽지 못함';
    return o;
  }
  const fmt = v => v === null || v === undefined ? '비어 있음' : typeof v === 'boolean' ? (v ? '예' : '아니오') : String(v);
  function diff(a, b) {
    if (!a || !b) return ['제시 설정 기록이 없음'];
    const A = { ...a }, B = { ...b };
    if (!A.win || !B.win) { A.win = null; B.win = null; }
    const FA = flat(A), FB = flat(B), out = [];
    for (const k of new Set([...Object.keys(FA), ...Object.keys(FB)])) {
      if (JSON.stringify(FA[k]) !== JSON.stringify(FB[k])) out.push(`${LABEL[k] || (k.startsWith('features.') ? '처리기 기능 ' + k.slice(9) : k)}: ${fmt(FA[k])} → ${fmt(FB[k])}`);
    }
    return out;
  }
  return { of, key, diff, winEss, ROUTE_KEYS };
})();

// 임상(항상자극법) 측정의 상태 전이 — 계단과 같은 꼴(시행마다 전이 기록, 재생 대조)
const ConstRun = (() => {
  function cfgFrom(P) { const c = P.constant; return { version: c.version, total: c.total, per: c.per_density, densIdx: c.densities_index.slice(), maxTechnical: c.max_technical_failures }; }
  function init(cfg, order) {
    if (!Array.isArray(order) || order.length !== cfg.total) throw new Error('임상 순서 길이가 이상함');
    return { slot: 0, k: order[0], validCount: 0, technicalCount: 0, attemptCount: 0, processed: [], status: 'running' };
  }
  // outcome = { trialId, presentedK, valid, correct, reason }
  function step(state, cfg, order, outcome) {
    if (state.processed.includes(outcome.trialId)) return { duplicate: true, state, tr: null };
    if (state.status !== 'running') throw new Error('이미 끝난 측정: ' + state.status);
    if (outcome.presentedK !== order[state.slot] || outcome.presentedK !== state.k) throw new Error(`제시 칸 ${outcome.presentedK} ≠ 순서 ${order[state.slot]}`);
    const next = clone(state);
    next.attemptCount++;
    next.processed.push(outcome.trialId);
    const tr = { trialId: outcome.trialId, attemptNo: next.attemptCount, validNo: null, slot: state.slot, presentedK: state.k, presentedMilli: DENS_MILLI[state.k],
      valid: !!outcome.valid, correct: outcome.valid ? !!outcome.correct : null, reason: outcome.valid ? null : (outcome.reason || 'invalid'), move: null, nextSlot: null, nextK: null, nextPresented: null, statusAfter: null };
    if (!outcome.valid) {
      next.technicalCount++;
      tr.move = 'INVALID_SAME_DENSITY_AGAIN';
      if (next.technicalCount >= cfg.maxTechnical) next.status = 'technical_failure';
    } else {
      next.validCount++;
      tr.validNo = next.validCount;
      next.slot++;
      tr.move = 'NEXT';
      if (next.slot >= cfg.total) next.status = 'complete';
    }
    next.k = next.slot < cfg.total ? order[next.slot] : null;
    tr.nextSlot = next.slot; tr.nextK = next.k; tr.nextPresented = next.status === 'running'; tr.statusAfter = next.status;
    return { duplicate: false, state: next, tr };
  }
  return { cfgFrom, init, step };
})();

const Analysis = (() => {
  const STATUS_TXT = {
    complete_in_range: '정상 완료',
    threshold_below_range: '역치가 측정 범위 밖 (< 0.125 rpo) — 숫자 역치 없음',
    threshold_near_easy_end: '쉬운 끝(0.125 rpo)에 막힘 — 숫자 역치 없음 (0.125 근처이거나 그 아래)',
    threshold_above_range: '역치가 측정 범위 밖 (> 11.314 rpo) — 숫자 역치 없음',
    threshold_near_hard_end: '어려운 끝(11.314 rpo)에 막힘 — 숫자 역치 없음 (11.314 근처이거나 그 위)',
    unreliable_responses: '측정 신뢰성 부족 (다시 하기)',
    technical_failure: '기술적 실패로 중단', participant_aborted: '중간에 멈춤', trial_cap_before_reversal_target: '시행 상한 — 반전 13번 전에 끝남',
    complete: '72시행 완료', protocol_deviation: '절차 어긋남', insufficient_data: '자료 부족', running: '진행 중',
  };
  const REASON_TXT = {
    easy_blocked: '분석 구간에서 계단이 0.125 rpo 보다 성기게 가려다 막힘 — 그 골이 0.125 로 잘려 반전 평균이 실제보다 좋게(높게) 치우침. 0.125 정답률로는 70.7 % 위·아래를 가르지 못함',
    easy_below_target: '분석 구간에서 쉬운 끝에 막혔고, 그 구간의 0.125 rpo 정답률이 70.7 % 보다 낮음이 확인됨 (한쪽 정확 이항 p < .05)',
    easy_worse_than_harder: '분석 구간에서 가장 쉬운 0.125 rpo 정답률이 더 촘촘한(어려운) 밀도보다 낮음 (한쪽 Fisher p < .05) — 쉬울수록 잘해야 하므로 ‘가장 쉬운 것도 못 함’이 아니라 과제 이해·주의 문제로 봄',
    hard_blocked: '분석 구간에서 계단이 11.314 rpo 보다 촘촘하게 가려다 막힘 — 그 꼭짓점이 11.314 로 잘려 반전 평균이 실제보다 나쁘게(낮게) 치우침',
    hard_above_target: '분석 구간에서 어려운 끝에 막혔고, 그 구간의 11.314 rpo 정답률이 70.7 % 보다 높음이 확인됨 (한쪽 정확 이항 p < .05)',
    both_ends_blocked: '분석 구간에서 두 끝(0.125 · 11.314)에 모두 막힘 — 응답이 일정하지 않음',
  };
  const FLAG_TXT = {
    near_easy_end: '분석 구간이 0.125 rpo 에 닿음(막히지는 않음) — 쉬운 끝 가까이: 다시 재면 막힐 수 있고, 숫자로 남은 값은 좋게 치우칠 수 있음',
    near_hard_end: '분석 구간이 11.314 rpo 에 닿음(막히지는 않음)',
    early_easy_errors: '분석 구간 앞에서 0.125 rpo 에서 막힌 이동이 3번 이상 — 처음에 과제를 잘못 이해했거나 역치가 쉬운 끝 가까이일 수 있음 (판정에는 안 씀)',
    track_not_above_chance: '시행 전체 정답률이 우연(1/3)보다 높다는 증거 없음 — ‘못 함’이라는 뜻은 아님',
    interval_bias: '다른 소리 자리(1·2·3)마다 정답률이 다름 — 같은 밀도끼리 견줌 (밀도별 순열 검정 p < .05)',
    response_bias: '틀린 시행에서 고른 자리가 한쪽으로 몰림 (자리 선호, 순열 검정 p < .05)',
    presentation_changed_during_run: '측정 중 Windows 출력·볼륨이 바뀜 — 어느 묶음에도 넣지 않음', presentation_differs: '회기 시작 때와 제시 설정이 다름 — 따로 묶음',
    win_unverified: 'Windows 오디오를 읽지 못해 측정 중 바뀌었는지 확인 못 함',
    examples_before_clinical: '임상 검사 전에 예시를 들음 — Drennan 2014 는 연습 없음 (점수는 남김)',
    filter_pending: '말소리 모양 필터 표(Byrne 1994)가 원문 대조 전 — Won 자극과 다름',
  };
  const NUMERIC = new Set(['complete_in_range']);

  // 정확한 유리수 (BigInt 분자/분모) — 와우STM analysis_v4 와 같음
  const Q = (() => {
    const abs = x => x < 0n ? -x : x;
    const gcd = (a, b) => { a = abs(a); b = abs(b); while (b) [a, b] = [b, a % b]; return a; };
    function make(n, d) {
      if (d === 0n) throw new Error('분모가 0');
      if (d < 0n) { n = -n; d = -d; }
      const g = gcd(n, d) || 1n;
      return { n: n / g, d: d / g };
    }
    const of = (sum, count) => {
      if (!Number.isSafeInteger(sum) || !Number.isSafeInteger(count) || count <= 0) throw new Error(`정확한 값에 쓸 수 없는 합/개수 ${sum}/${count}`);
      return make(BigInt(sum), BigInt(count));
    };
    const add = (a, b) => make(a.n * b.d + b.n * a.d, a.d * b.d);
    const sub = (a, b) => make(a.n * b.d - b.n * a.d, a.d * b.d);
    const cmp = (a, b) => { const x = a.n * b.d - b.n * a.d; return x > 0n ? 1 : x < 0n ? -1 : 0; };
    const mean = qs => {
      if (!qs.length) throw new Error('빈 평균');
      const s = qs.reduce(add, { n: 0n, d: 1n });
      return make(s.n, s.d * BigInt(qs.length));
    };
    const num = a => {
      if (abs(a.n) > 9007199254740992n || a.d > 9007199254740992n) throw new Error('정확한 값을 숫자로 바꿀 수 없음 (2^53 초과)');
      return Number(a.n) / Number(a.d);
    };
    return { of, add, sub, cmp, mean, num, abs: a => ({ n: abs(a.n), d: a.d }), int: k => make(BigInt(k), 1n),
      str: a => ({ num: a.n.toString(), den: a.d.toString() }), from: s => make(BigInt(s.num), BigInt(s.den)) };
  })();

  // 자리(1·2·3)와 응답 — 순열 검정 두 가지 (씨앗 고정이라 같은 기록이면 늘 같은 p)
  //   ① 자리별 정답률: 밀도 칸마다 묶어(층) 그 안에서만 자리 이름을 섞음 — 계단은 쉬운 밀도가 앞에 몰려 있어,
  //      층을 나누지 않고 자리별 정답률을 견주면 우연히 쉬운 시행이 몰린 자리가 ‘치우침’ 으로 보임 (2026-10-21 흐름 시험에서 발견)
  //      통계량 T = Σ_자리 (O − E)² / V (E·V 는 층마다 초기하 기대·분산의 합)
  //   ② 자리 선호: 틀린 시행만 — 고른 자리는 다른 소리가 아닌 두 자리 중 하나이고, 선호가 없으면 반반.
  //      (전체 누름 분포를 균등과 견주면 다른 소리 자리가 우연히 고르지 않을 때 그대로 따라감)
  //   p = (1 + #{T_b ≥ T}) / (1 + B), 판정 p < .05 ⟺ 20·(1 + #) < 1 + B (정수)
  const PERM_B = 2000;
  const permRng = seedHex => Rng.fromHex(seedHexOf(/^[0-9a-f]{32}$/.test(seedHex || '') ? [0, 1, 2, 3].map(i => (parseInt(seedHex.slice(i * 8, i * 8 + 8), 16) ^ 0x5a5a5a5a) >>> 0) : [0x5eed, 1, 2, 3]));
  function posStat(strata, labels) {
    const O = [0, 0, 0], E = [0, 0, 0], V = [0, 0, 0];
    let idx = 0;
    for (const st of strata) {
      const n = st.length, c = st.reduce((s2, t) => s2 + (t.correct ? 1 : 0), 0);
      const np = [0, 0, 0], cp = [0, 0, 0];
      for (let i = 0; i < n; i++) { const q = labels[idx + i] - 1; np[q]++; if (st[i].correct) cp[q]++; }
      for (let q = 0; q < 3; q++) {
        O[q] += cp[q]; E[q] += np[q] * c / n;
        if (n > 1) V[q] += np[q] * (n - np[q]) * c * (n - c) / (n * n * (n - 1));
      }
      idx += n;
    }
    let T = 0;
    for (let q = 0; q < 3; q++) if (V[q] > 1e-12) T += (O[q] - E[q]) ** 2 / V[q];
    return T;
  }
  function prefStat(wrong, chosen) {
    const X = [0, 0, 0], M = [0, 0, 0];
    wrong.forEach((t, i) => { for (const q of [1, 2, 3]) if (q !== t.targetPos) M[q - 1]++; X[chosen[i] - 1]++; });
    let T = 0;
    for (let q = 0; q < 3; q++) if (M[q] > 0) T += (X[q] - M[q] / 2) ** 2 / (M[q] / 4);
    return { T, X, M };
  }
  function positionStats(valid, seedHex) {
    const n = [1, 2, 3].map(q => valid.filter(t => t.targetPos === q).length);
    const k = [1, 2, 3].map(q => valid.filter(t => t.targetPos === q && t.correct).length);
    const resp = [1, 2, 3].map(q => valid.filter(t => t.response === q).length);
    const rng = permRng(seedHex);
    // ① 층 = 밀도 칸
    const byK = new Map();
    for (const t of valid) { if (!byK.has(t.k)) byK.set(t.k, []); byK.get(t.k).push(t); }
    const strata = [...byK.keys()].sort((x, y) => x - y).map(kk => byK.get(kk));
    const lab0 = strata.flatMap(st => st.map(t => t.targetPos));
    const T0 = posStat(strata, lab0);
    let ge = 0;
    for (let bb = 0; bb < PERM_B; bb++) {
      const lab = [];
      for (const st of strata) {
        const arr = st.map(t => t.targetPos);
        for (let i = arr.length - 1; i > 0; i--) { const j = rng.int(i + 1); const x = arr[i]; arr[i] = arr[j]; arr[j] = x; }
        lab.push(...arr);
      }
      if (posStat(strata, lab) >= T0 - 1e-9) ge++;
    }
    // ② 틀린 시행의 자리 선호
    const wrong = valid.filter(t => t.correct === false && [1, 2, 3].includes(t.response) && t.response !== t.targetPos);
    const P0 = prefStat(wrong, wrong.map(t => t.response));
    let geP = 0;
    for (let bb = 0; bb < PERM_B; bb++) {
      const ch = wrong.map(t => { const opts = [1, 2, 3].filter(q => q !== t.targetPos); return opts[rng.int(2)]; });
      if (prefStat(wrong, ch).T >= P0.T - 1e-9) geP++;
    }
    const pq = c => ({ num: String(1 + c), den: String(1 + PERM_B) });
    return { n, k, resp, method: 'permutation_B2000_seeded', B: PERM_B,
      pPos: (1 + ge) / (1 + PERM_B), pPosExact: pq(ge), sigPos: 20 * (1 + ge) < 1 + PERM_B, statPos: T0,
      nWrong: wrong.length, prefChosen: P0.X, prefAvail: P0.M, pPref: (1 + geP) / (1 + PERM_B), pPrefExact: pq(geP), sigPref: 20 * (1 + geP) < 1 + PERM_B, statPref: P0.T };
  }
  // 밀도 칸별 시행 수·정답 (주어진 시행들)
  function densTable(trials) {
    const m = new Map();
    for (const t of trials) { const e = m.get(t.k) || { k: t.k, n: 0, c: 0 }; e.n++; if (t.correct) e.c++; m.set(t.k, e); }
    return [...m.values()].sort((a, b) => a.k - b.k);
  }
  const isBlock = (t, side) => !!(t.tr && t.tr.move === 'BLOCKED_ZERO_MOVE' && t.tr.blockedAt === side);
  const binomStats = (k, n) => n ? { n, k, rate: k / n, ci95: Stats.clopperPearson(k, n),
    pBelowTarget: Stats.le(k, n, TARGET_P), pAboveTarget: Stats.ge(k, n, TARGET_P) } : { n: 0, k: 0, rate: null, ci95: null, pBelowTarget: null, pAboveTarget: null };

  // 적응 track 분류. 분석 구간 W = 남기지 않은 마지막 반전(5번째)의 다음 유효 시행부터 끝까지 (시행 상한으로 끝난 track 은 마지막 20 시행)
  //   W 안의 막힌 이동이 남긴 반전(6–13번째)을 끝 값으로 자른 막힘 전부 — 5번째 반전 시행까지의 막힘은 남기지 않은 반전만 자름
  function classifyAdaptive(run, cfg) {
    const st = run.state, flags = [];
    const R = st ? Stair.threshold(st, cfg) : null;
    let status;
    if (run.endReason === 'participant_aborted') status = 'participant_aborted';
    else if (!st) status = 'insufficient_data';
    else if (st.status === 'technical_failure') status = 'technical_failure';
    else if (st.status === 'trial_cap_before_reversal_target') status = 'trial_cap_before_reversal_target';
    else if (st.status === 'reversal_target_reached' && R) status = 'complete_in_range';
    else status = 'insufficient_data';
    const valid = (run.trials || []).filter(t => t.valid);
    let W = null;
    if (R && status === 'complete_in_range') {
      const nDrop = st.reversals.length - cfg.retained;
      const lastDrop = nDrop > 0 ? st.reversals[nDrop - 1] : null;
      W = valid.filter(t => t.tr && (!lastDrop || t.tr.validNo > lastDrop.validNo));
    } else if (status === 'trial_cap_before_reversal_target') W = valid.slice(-20);
    let bound = null;
    if (W) {
      const firstW = W.length && W[0].tr ? W[0].tr.validNo : Infinity;
      const at0 = W.filter(t => t.k === cfg.minK), atH = W.filter(t => t.k === cfg.maxK);
      const harder = W.filter(t => t.k > cfg.minK);
      const k0 = at0.filter(t => t.correct).length, kh = harder.filter(t => t.correct).length;
      const pEasyWorse = (at0.length && harder.length) ? Exact.fisherGreater(kh, harder.length - kh, k0, at0.length - k0) : null;
      bound = {
        nWin: W.length, firstValidNo: W.length ? firstW : null,
        easyBlocksWin: W.filter(t => isBlock(t, 'easy')).length, hardBlocksWin: W.filter(t => isBlock(t, 'hard')).length,
        easyBlocksBefore: valid.filter(t => isBlock(t, 'easy') && t.tr.validNo < firstW).length,
        touchedEasy: W.some(t => t.k === cfg.minK), touchedHard: W.some(t => t.k === cfg.maxK),
        easyWin: binomStats(k0, at0.length), hardWin: binomStats(atH.filter(t => t.correct).length, atH.length),
        harderWin: { n: harder.length, k: kh, rate: harder.length ? kh / harder.length : null },
        pEasyWorse: Exact.toNum(pEasyWorse), pEasyWorseExact: Exact.str(pEasyWorse), sigEasyWorse: Exact.lt05(pEasyWorse),
      };
    }
    const limE = !!(bound && bound.easyBlocksWin > cfg.blocksMax), limH = !!(bound && bound.hardBlocksWin > cfg.blocksMax);
    let reason = null;
    if (status === 'complete_in_range' || status === 'trial_cap_before_reversal_target') {
      if (limE && limH) { status = 'unreliable_responses'; reason = 'both_ends_blocked'; }
      else if (limE) {
        if (bound.sigEasyWorse) { status = 'unreliable_responses'; reason = 'easy_worse_than_harder'; }
        else if (bound.easyWin.n && bound.easyWin.pBelowTarget < 0.05) { status = 'threshold_below_range'; reason = 'easy_below_target'; }
        else { status = 'threshold_near_easy_end'; reason = 'easy_blocked'; }
      } else if (limH) {
        if (bound.hardWin.n && bound.hardWin.pAboveTarget < 0.05) { status = 'threshold_above_range'; reason = 'hard_above_target'; }
        else { status = 'threshold_near_hard_end'; reason = 'hard_blocked'; }
      }
    }
    if (bound && !limE && bound.touchedEasy && status === 'complete_in_range') flags.push('near_easy_end');
    if (bound && !limH && bound.touchedHard && status === 'complete_in_range') flags.push('near_hard_end');
    if (bound && bound.easyBlocksBefore >= 3) flags.push('early_easy_errors');
    const n = valid.length, k = valid.filter(t => t.correct).length;
    const pAll = n ? Exact.binomGeThird(k, n) : null;
    if (n && !Exact.lt05(pAll)) flags.push('track_not_above_chance');
    const pos = positionStats(valid, run.seed);
    if (pos.sigPos) flags.push('interval_bias');
    if (pos.sigPref) flags.push('response_bias');
    commonFlags(run, flags);
    const kept = R ? R.retainedMilli : [];
    return {
      kind: 'adaptive', status, reason, flags, thr: NUMERIC.has(status) ? R.thr : null, thrRaw: R ? R.thr : null, sumMilli: R ? R.sumMilli : null, count: R ? R.count : null,
      retainedMilli: kept, reversalsMilli: st ? st.reversals.map(r => r.milli) : [], sdKept: kept.length > 1 ? Stats.sd(kept.map(v => v / 1000)) : null,
      nValid: n, nCorrect: k, pCorrect: n ? k / n : null, pVsChance: Exact.toNum(pAll), pVsChanceExact: Exact.str(pAll), bound, blocksMax: cfg.blocksMax,
      nAttempts: st ? st.attemptCount : 0, nTechnical: st ? st.technicalCount : 0, pos, dens: densTable(valid),
      nBlocked: valid.filter(t => t.tr && t.tr.move === 'BLOCKED_ZERO_MOVE').length,
      maxK: valid.length ? Math.max(...valid.map(t => t.k)) : null, minK: valid.length ? Math.min(...valid.map(t => t.k)) : null,
    };
  }
  function commonFlags(run, flags) {
    if (run.presChangedDuring && run.presChangedDuring.length) flags.push('presentation_changed_during_run');
    if (run.presDiffers && run.presDiffers.length) flags.push('presentation_differs');
    if (run.winUnverified) flags.push('win_unverified');
    if (run.filterPending) flags.push('filter_pending');
    if (run.kind === 'constant' && (run.examplesBefore || 0) > 0) flags.push('examples_before_clinical');
  }
  // 임상 측정 분류: 72시행이 모두 유효로 끝났을 때만 점수
  function classifyConstant(run, P) {
    const cfg = ConstRun.cfgFrom(P), st = run.state, flags = [];
    let status;
    if (run.endReason === 'participant_aborted') status = 'participant_aborted';
    else if (!st) status = 'insufficient_data';
    else if (st.status === 'technical_failure') status = 'technical_failure';
    else if (st.status === 'complete' && st.validCount === cfg.total) status = 'complete';
    else status = 'insufficient_data';
    const valid = (run.trials || []).filter(t => t.valid);
    const n = valid.length, k = valid.filter(t => t.correct).length;
    const pAll = n ? Exact.binomGeThird(k, n) : null;
    if (n && !Exact.lt05(pAll)) flags.push('track_not_above_chance');
    const pos = positionStats(valid, run.seed);
    if (pos.sigPos) flags.push('interval_bias');
    if (pos.sigPref) flags.push('response_bias');
    commonFlags(run, flags);
    const done = status === 'complete';
    return {
      kind: 'constant', status, reason: null, flags, pc: done ? k / n : null, pcRaw: n ? k / n : null, nCorrect: k, nValid: n,
      ci95: n ? Stats.clopperPearson(k, n) : null, pVsChance: Exact.toNum(pAll), pVsChanceExact: Exact.str(pAll), notAboveChance: !!(n && !Exact.lt05(pAll)),
      dens: densTable(valid), pos, nAttempts: st ? st.attemptCount : 0, nTechnical: st ? st.technicalCount : 0,
    };
  }
  const classify = (run, P) => run.kind === 'constant' ? classifyConstant(run, P) : classifyAdaptive(run, Stair.cfgFrom(P));

  // ── 값 검증 도우미 (산술 전에, 강제 형변환 없이) ──
  const isNum = v => typeof v === 'number' && Number.isFinite(v);
  const HEX32 = /^[0-9a-f]{32}$/;
  const desc = v => v === undefined ? '없음' : v === null ? 'null' : typeof v === 'number' ? String(v) : typeof v === 'string' ? `문자열 "${v.slice(0, 24)}"`
    : typeof v === 'boolean' ? `참거짓 ${v}` : Array.isArray(v) ? `배열(${v.length})` : typeof v;
  function deq(a, b) {
    if (a === b) return true;
    if (a === null || b === null || typeof a !== 'object' || typeof b !== 'object' || Array.isArray(a) !== Array.isArray(b)) return false;
    const ka = Object.keys(a), kb = Object.keys(b);
    return ka.length === kb.length && ka.every(k => Object.prototype.hasOwnProperty.call(b, k) && deq(a[k], b[k]));
  }
  const diffKeys = (a, b) => [...new Set([...Object.keys(a || {}), ...Object.keys(b || {})])].filter(k => !deq(a ? a[k] : undefined, b ? b[k] : undefined)).sort();
  // 숫자 결과의 값 검증: thr 는 유한한 숫자이고 반전 합(milli-rpo 정수)/(1000·개수) 와 같아야 함
  function numericResultIssue(x) {
    if (!isNum(x.thr)) return `역치 thr 가 유한한 숫자가 아님 (${desc(x.thr)})`;
    if (!Number.isSafeInteger(x.sumMilli)) return `반전 합 sumMilli 가 정수가 아님 (${desc(x.sumMilli)})`;
    if (!(Number.isSafeInteger(x.count) && x.count > 0)) return `반전 개수 count 가 양의 정수가 아님 (${desc(x.count)})`;
    if (x.thr !== x.sumMilli / (1000 * x.count)) return `역치 thr ${x.thr} 가 반전 합/(1000·개수) ${x.sumMilli}/(1000·${x.count}) 와 다름`;
    if (x.thrRaw !== undefined && x.thrRaw !== x.thr) return `계산값 thrRaw (${desc(x.thrRaw)}) 가 thr 와 다름`;
    return null;
  }
  function pcResultIssue(x) {
    if (!(Number.isSafeInteger(x.nCorrect) && Number.isSafeInteger(x.nValid) && x.nValid > 0 && x.nCorrect >= 0 && x.nCorrect <= x.nValid)) return `정답·시행 수가 이상함 (${desc(x.nCorrect)}/${desc(x.nValid)})`;
    if (!isNum(x.pc) || x.pc !== x.nCorrect / x.nValid) return `점수 pc ${desc(x.pc)} 가 ${x.nCorrect}/${x.nValid} 와 다름`;
    return null;
  }

  // track 하나의 결과 종류: num(숫자 역치) · below(< 0.125) · easy(쉬운 끝에 막힘) · above(> 11.314) · hard(어려운 끝에 막힘) · pc(임상 점수)
  //   · none(숫자 없음: 멈춤·실패·절차 어긋남·신뢰성 부족·측정 중 설정 바뀜 등 — 다시 함)
  function outcome(r) {
    const x = r && r.result;
    if (!x) return { kind: 'none', value: null };
    const flags = Array.isArray(x.flags) ? x.flags : [];
    if (flags.includes('presentation_changed_during_run') || (r.presChangedDuring && r.presChangedDuring.length)) return { kind: 'none', value: null };
    if (r.kind === 'constant') {
      if (x.status !== 'complete') return { kind: 'none', value: null };
      const bad = pcResultIssue(x);
      if (bad) return { kind: 'none', value: null, invalid: bad };
      return { kind: 'pc', value: x.pc, k: x.nCorrect, n: x.nValid, notAboveChance: !!x.notAboveChance };
    }
    if (NUMERIC.has(x.status)) {
      const bad = numericResultIssue(x);
      if (bad) return { kind: 'none', value: null, invalid: bad };
      return { kind: 'num', value: x.thr, sumMilli: x.sumMilli, count: x.count, nearEasy: flags.includes('near_easy_end'), nearHard: flags.includes('near_hard_end') };
    }
    if (x.status === 'threshold_below_range') return { kind: 'below', value: null };
    if (x.status === 'threshold_near_easy_end') return { kind: 'easy', value: null };
    if (x.status === 'threshold_above_range') return { kind: 'above', value: null };
    if (x.status === 'threshold_near_hard_end') return { kind: 'hard', value: null };
    return { kind: 'none', value: null };
  }
  const isIncluded = r => !!(r && !r.practice && ['num', 'pc'].includes(outcome(r).kind));

  // ── 저장된 입력의 자료형·범위 ──
  function validateCommon(run, P, need) {
    need(Array.isArray(run.trials), '측정', 'trials', run.trials);
    need(typeof run.seed === 'string' && HEX32.test(run.seed), '측정', 'seed', run.seed);
    need(isNum(run.levelDbfs) && run.levelDbfs === P.stimulus.level_dbfs, '측정', 'levelDbfs', run.levelDbfs);
    need(run.protocolKey === P.id, '측정', 'protocolKey', run.protocolKey);
  }
  function validateTrial(t, i, need, maxK) {
    const w = `${i + 1}번째 시행`;
    if (!need(t !== null && typeof t === 'object', w, '시행 기록', t)) return;
    need(typeof t.id === 'string' && t.id.length > 0, w, 'id', t.id);
    need(typeof t.valid === 'boolean', w, 'valid', t.valid);
    need(Number.isSafeInteger(t.k) && t.k >= 0 && t.k <= maxK, w, 'k', t.k);
    need(Number.isSafeInteger(t.k) && t.rpoMilli === DENS_MILLI[t.k], w, 'rpoMilli', t.rpoMilli);
    need(t.targetPos === 1 || t.targetPos === 2 || t.targetPos === 3, w, 'targetPos', t.targetPos);
    need(Number.isSafeInteger(t.thetaU) && t.thetaU >= 0 && t.thetaU < TWO32, w, 'thetaU', t.thetaU);
    need(isNum(t.theta) && t.theta >= 0 && t.theta < 2 * Math.PI, w, 'theta', t.theta);
    need(Array.isArray(t.seeds) && t.seeds.length === 3 && t.seeds.every(s => typeof s === 'string' && HEX32.test(s)), w, 'seeds', t.seeds);
    need(Array.isArray(t.roves) && t.roves.length === 3 && t.roves.every(v => Number.isInteger(v) && v >= -4 && v <= 4), w, 'roves', t.roves);
    need(typeof t.rngBefore === 'string' && HEX32.test(t.rngBefore), w, 'rngBefore', t.rngBefore);
    need(typeof t.rngAfter === 'string' && HEX32.test(t.rngAfter), w, 'rngAfter', t.rngAfter);
    need(t.tr !== null && typeof t.tr === 'object', w, '저장된 전이(tr)', t.tr);
    if (t.valid === true) {
      need(typeof t.correct === 'boolean', w, 'correct', t.correct);
      need(t.response === 1 || t.response === 2 || t.response === 3, w, 'response', t.response);
      const s = t.stim;
      if (need(Array.isArray(s) && s.length === 3 && s.every(x => x !== null && typeof x === 'object'), w, '자극 기록(stim)', s)) {
        s.forEach((x, j) => {
          const wk = `${w} 구간 ${j + 1}`;
          need(isNum(x.rmsRaw) && x.rmsRaw > 0, wk, 'rmsRaw', x.rmsRaw);
          need(isNum(x.gainDb), wk, 'gainDb', x.gainDb);
          need(isNum(x.rmsOutDbfs), wk, 'rmsOutDbfs', x.rmsOutDbfs);
          need(isNum(x.peakDbfs), wk, 'peakDbfs', x.peakDbfs);
          if (x.fp !== undefined) need(Array.isArray(x.fp) && x.fp.every(isNum), wk, 'fp', x.fp);
        });
      }
      const tm = t.timing;
      if (tm && tm.clockRate !== undefined && tm.clockRate !== null) need(isNum(tm.clockRate), w, 'timing.clockRate', tm.clockRate);
    }
  }
  function validateRun(run, P) {
    const out = [];
    const need = (ok, where, field, v) => { if (!ok) out.push(`${where}: ${field} 값이 올바르지 않음 (${desc(v)})`); return ok; };
    validateCommon(run, P, need);
    const maxK = DENS_MILLI.length - 1;
    (Array.isArray(run.trials) ? run.trials : []).forEach((t, i) => validateTrial(t, i, need, maxK));
    const st = run.state;
    if (need(st !== null && typeof st === 'object', '최종 상태', 'state', st)) {
      need(typeof st.status === 'string', '최종 상태', 'status', st.status);
      need(Array.isArray(st.processed) && st.processed.every(x => typeof x === 'string'), '최종 상태', 'processed', st.processed);
      for (const k of ['attemptCount', 'validCount', 'technicalCount']) need(Number.isSafeInteger(st[k]) && st[k] >= 0, '최종 상태', k, st[k]);
      if (run.kind === 'constant') {
        need(Number.isSafeInteger(st.slot) && st.slot >= 0 && st.slot <= P.constant.total, '최종 상태', 'slot', st.slot);
        need(Array.isArray(run.mcsOrder) && run.mcsOrder.length === P.constant.total && run.mcsOrder.every(k => P.constant.densities_index.includes(k)), '측정', 'mcsOrder', run.mcsOrder);
      } else {
        need(Number.isSafeInteger(st.k) && st.k >= 0 && st.k <= maxK, '최종 상태', 'k', st.k);
        need(Number.isSafeInteger(st.correctStreak) && st.correctStreak >= 0, '최종 상태', 'correctStreak', st.correctStreak);
        need(Number.isSafeInteger(st.moves) && st.moves >= 0, '최종 상태', 'moves', st.moves);
        need(st.lastDir === null || st.lastDir === 1 || st.lastDir === -1, '최종 상태', 'lastDir', st.lastDir);
        if (need(Array.isArray(st.reversals), '최종 상태', 'reversals', st.reversals)) st.reversals.forEach((r, j) => {
          const w = `최종 상태 반전 ${j + 1}`;
          if (!need(r !== null && typeof r === 'object', w, '반전 기록', r)) return;
          need(Number.isSafeInteger(r.k) && r.k >= 0 && r.k <= maxK && r.milli === DENS_MILLI[r.k], w, 'k·milli', `${r.k}/${r.milli}`);
          need(Number.isSafeInteger(r.validNo) && r.validNo >= 1, w, 'validNo', r.validNo);
          need(Number.isSafeInteger(r.attemptNo) && r.attemptNo >= 1, w, 'attemptNo', r.attemptNo);
          need(typeof r.trialId === 'string', w, 'trialId', r.trialId);
          need(r.dirAfter === 1 || r.dirAfter === -1, w, 'dirAfter', r.dirAfter);
          need(r.atBound === null || r.atBound === 'easy' || r.atBound === 'hard', w, 'atBound', r.atBound);
        });
      }
    }
    return out;
  }

  // 기록 대조: ① 자료형·범위 ② 시행만으로 처음부터 재생(난수·계획·순서·계단/진행) ③ 저장된 전이(모든 필드)·최종 상태(전체)와 대조
  //   ④ 기존 결과(덮어쓰기 전에 보존한 prior)의 판에 상관없는 값과 대조. 재생한 상태·전이를 돌려주어 판정은 그것으로 (judge)
  function audit(run, P, prior = run.result || null) {
    const validation = validateRun(run, P);
    const issues = validation.slice();
    const adaptive = run.kind !== 'constant';
    const cfg = adaptive ? Stair.cfgFrom(P) : ConstRun.cfgFrom(P);
    let order = null, st = null, replayOk = Array.isArray(run.trials);
    const trs = [];
    let prevAfter = run.seed || null;
    try {
      if (adaptive) st = Stair.init(cfg);
      else {
        const rng = Rng.fromHex(run.seed);
        order = ConstPlan.order(rng, cfg.densIdx, cfg.per);
        if (!deq(order, run.mcsOrder)) issues.push('임상 순서(mcsOrder)가 씨앗으로 다시 만든 순서와 다름');
        prevAfter = rng.hex();
        st = ConstRun.init(cfg, order);
      }
    } catch (e) { issues.push('재생 시작 실패 — ' + e.message); replayOk = false; }
    if (run.clockOverride) issues.push('출력 시계 점검을 끈 채 잰 측정(시험용 allowClockDrift) — 절차 어긋남');
    if (run.filterPending) issues.push('말소리 모양 필터 표가 원문 대조 전인 채 잰 측정(시험용 allowPendingFilter) — 절차 어긋남');
    const lev = run.levelDbfs;
    const seen = new Set();
    (Array.isArray(run.trials) ? run.trials : []).forEach((t, i) => {
      const where = `${i + 1}번째 시행`;
      if (t === null || typeof t !== 'object') { replayOk = false; return; }
      if (seen.has(t.id)) issues.push(`${where}: 같은 trial ID 가 두 번 (${t.id})`);
      seen.add(t.id);
      // RNG: 이어지는 상태 + 같은 추출. 페이지가 닫혀 끊긴 노출(run.abandoned)이 사이에 있으면 그것을 거쳐 이어져야 함
      let guard = 0;
      while (prevAfter && t.rngBefore !== prevAfter && guard++ < 20) {
        const a = (run.abandoned || []).find(x => x.rngBefore === prevAfter);
        if (!a) break;
        try {
          const d = TrialPlan.draw(Rng.fromHex(a.rngBefore));
          if (d.targetPos !== a.targetPos || d.seeds.join() !== (a.seeds || []).join() || d.thetaU !== a.thetaU || d.rngAfter !== a.rngAfter) issues.push(`끊긴 노출 ${a.trialId}: RNG 로 다시 뽑은 값이 기록과 다름`);
        } catch (e) { issues.push(`끊긴 노출 ${a.trialId}: RNG 오류 ${e.message}`); }
        prevAfter = a.rngAfter;
      }
      if (prevAfter && t.rngBefore !== prevAfter) issues.push(`${where}: RNG 상태가 앞 시행과 이어지지 않음`);
      try {
        const d = TrialPlan.draw(Rng.fromHex(t.rngBefore));
        if (d.targetPos !== t.targetPos || d.thetaU !== t.thetaU || d.theta !== t.theta || d.seeds.join() !== (t.seeds || []).join() || d.roves.join() !== (t.roves || []).join()) issues.push(`${where}: RNG 로 다시 뽑은 자리·위상·씨앗·흔들기가 기록과 다름`);
        if (d.rngAfter !== t.rngAfter) issues.push(`${where}: RNG 다음 상태가 기록과 다름`);
      } catch (e) { issues.push(`${where}: RNG 다시 뽑기 실패 — ${e.message}`); }
      prevAfter = t.rngAfter;
      if (Number.isSafeInteger(t.k) && t.rpoMilli !== DENS_MILLI[t.k]) issues.push(`${where}: 밀도 값이 칸과 다름`);
      if (t.valid === true) {
        if (typeof t.correct === 'boolean' && [1, 2, 3].includes(t.response) && (t.response === t.targetPos) !== t.correct) issues.push(`${where}: 응답 ${t.response} · 다른 소리 ${t.targetPos} 인데 정오 기록 ${t.correct}`);
        const s = Array.isArray(t.stim) ? t.stim : [];
        if (!(s[0] && s[1] && s[2])) issues.push(`${where}: 자극 기록(RMS·peak·지문)이 없는데 채점됨`);
        else if (s.every(x => isNum(x.rmsRaw) && x.rmsRaw > 0 && isNum(x.gainDb) && isNum(x.rmsOutDbfs) && isNum(x.peakDbfs)) && Array.isArray(t.roves) && t.roves.every(Number.isInteger) && isNum(lev)) {
          // 크기는 경사 전 RMS 로 맞춤 → 20·log10(rmsRaw) + gainDb = 크기 + 흔들기 (기록은 소수 6자리라 1e-4 dB 안)
          s.forEach((x, j) => {
            const got = 20 * Math.log10(x.rmsRaw) + x.gainDb, want = lev + t.roves[j];
            if (!(Math.abs(got - want) < 1e-4)) issues.push(`${where}: 구간 ${j + 1} 정규화 크기 ${got.toFixed(4)} ≠ ${want.toFixed(4)} dBFS`);
          });
          if (!(Math.max(...s.map(x => x.peakDbfs)) <= -1)) issues.push(`${where}: peak 가 −1 dBFS 를 넘음 (잘림 가능)`);
        }
        const cr = t.timing && t.timing.clockRate;
        if (isNum(cr) && Math.abs(cr - 1) > P.task.audio_clock_tolerance && !run.clockOverride) issues.push(`${where}: 출력 시계 ${cr} 인 시행이 채점됨`);
      }
      if (!replayOk) return;
      try {
        const out = { trialId: t.id, presentedK: t.k, valid: t.valid, correct: t.correct, reason: t.invalidReason };
        const r = adaptive ? Stair.step(st, cfg, out) : ConstRun.step(st, cfg, order, out);
        if (r.duplicate) { issues.push(`${where}: 다시 계산에서 중복으로 처리됨`); replayOk = false; return; }
        trs.push(r.tr);
        const dk = diffKeys(r.tr, t.tr);
        if (dk.length) issues.push(`${where}: 저장된 전이가 다시 계산과 다름 — ${dk.slice(0, 4).map(k => `${k} 기록 ${JSON.stringify(t.tr ? t.tr[k] : undefined)} · 계산 ${JSON.stringify(r.tr[k])}`).join(' · ')}`);
        st = r.state;
      } catch (e) { issues.push(`${where}: 다시 계산 오류 — ${e.message}`); replayOk = false; }
    });
    if (run.state && typeof run.state === 'object') {
      if (replayOk && st) {
        for (const k of diffKeys(st, run.state)) {
          if (k === 'reversals' && Array.isArray(run.state.reversals) && Array.isArray(st.reversals)) {
            const n = Math.max(st.reversals.length, run.state.reversals.length);
            for (let j = 0; j < n; j++) {
              const a = st.reversals[j], b = run.state.reversals[j];
              if (!deq(a, b)) issues.push(`최종 상태 반전 ${j + 1}: ${a && b ? diffKeys(a, b).map(f => `${f} 기록 ${JSON.stringify(b[f])} · 계산 ${JSON.stringify(a[f])}`).join(' · ') : (a ? '기록에 없음' : '계산에 없음')}`);
            }
          } else issues.push(`최종 상태 ${k}: 기록 ${JSON.stringify(run.state[k])} · 계산 ${JSON.stringify(st[k])}`.slice(0, 300));
        }
      }
    } else issues.push('최종 상태(state)가 기록에 없음');
    let priorCheck = null;
    if (prior) {
      const pIssue = s => issues.push(`기존 결과: ${s}`);
      priorCheck = { version: prior.analysisVersion || run.analysisVersion || null, status: prior.status, statusBeforeAudit: prior.statusBeforeAudit || null };
      if (adaptive) {
        const th = replayOk && st ? Stair.threshold(st, cfg) : null;
        const re = th ? th.thr : null;
        priorCheck.thr = prior.thr ?? null; priorCheck.sumMilli = prior.sumMilli ?? null; priorCheck.count = prior.count ?? null; priorCheck.recomputed = re;
        if (prior.thr !== null && prior.thr !== undefined && !isNum(prior.thr)) pIssue(`thr 가 숫자가 아님 (${desc(prior.thr)})`);
        if (prior.thrRaw !== null && prior.thrRaw !== undefined && !isNum(prior.thrRaw)) pIssue(`thrRaw 가 숫자가 아님 (${desc(prior.thrRaw)})`);
        if (prior.sumMilli !== null && prior.sumMilli !== undefined && !Number.isSafeInteger(prior.sumMilli)) pIssue(`sumMilli 가 정수가 아님 (${desc(prior.sumMilli)})`);
        if (prior.count !== null && prior.count !== undefined && !(Number.isSafeInteger(prior.count) && prior.count > 0)) pIssue(`count 가 양의 정수가 아님 (${desc(prior.count)})`);
        if (replayOk) {
          if (prior.sumMilli !== undefined && prior.sumMilli !== (th ? th.sumMilli : null)) pIssue(`반전 합 ${desc(prior.sumMilli)} ≠ 다시 계산 ${th ? th.sumMilli : 'null'}`);
          if (prior.count !== undefined && prior.count !== (th ? th.count : null)) pIssue(`반전 개수 ${desc(prior.count)} ≠ 다시 계산 ${th ? th.count : 'null'}`);
          if (prior.thrRaw !== undefined && prior.thrRaw !== re) pIssue(`계산값 thrRaw ${desc(prior.thrRaw)} ≠ 다시 계산 ${re}`);
          if (prior.retainedMilli !== undefined && th && !deq(prior.retainedMilli, th.retainedMilli)) pIssue('남긴 반전 목록이 다시 계산과 다름');
          if (prior.reversalsMilli !== undefined && st && !deq(prior.reversalsMilli, st.reversals.map(r => r.milli))) pIssue('반전 목록이 다시 계산과 다름');
          if (isNum(prior.thr) && prior.thr !== re) pIssue(`역치 thr ${prior.thr} ≠ 다시 계산한 반전 평균 ${re}`);
        }
        if (NUMERIC.has(prior.status)) { const b = numericResultIssue(prior); if (b) pIssue(b); }
        else if ((prior.analysisVersion || run.analysisVersion || null) === P.analysis.version && prior.thr !== null && prior.thr !== undefined) pIssue(`숫자가 아닌 상태(${prior.status})인데 thr ${desc(prior.thr)}`);
      } else if (replayOk) {
        const valid = run.trials.filter(t => t && t.valid);
        const k = valid.filter(t => t.correct).length;
        priorCheck.nCorrect = prior.nCorrect ?? null; priorCheck.nValid = prior.nValid ?? null; priorCheck.pc = prior.pc ?? null;
        if (prior.nCorrect !== undefined && prior.nCorrect !== k) pIssue(`정답 수 ${desc(prior.nCorrect)} ≠ 다시 계산 ${k}`);
        if (prior.nValid !== undefined && prior.nValid !== valid.length) pIssue(`유효 시행 수 ${desc(prior.nValid)} ≠ 다시 계산 ${valid.length}`);
        if (prior.status === 'complete') { const b = pcResultIssue(prior); if (b) pIssue(b); }
        if (prior.dens !== undefined && !deq(prior.dens, densTable(valid))) pIssue('밀도별 정답 표가 다시 계산과 다름');
      }
    }
    return { ok: issues.length === 0, issues, validation, replayOk, replayState: st, replayTr: trs, priorCheck };
  }

  // DB 의 시행 기록과 journal 의 시행 기록(저장 확인 때 그대로 적은 것)을 시행마다 모든 칸 맞대기 — 계산값에 영향이 없는 변경(예: 틀린 응답 → 다른 틀린 응답)도 잡음.
  //   committedAt 은 journal 저장이 확인된 뒤 DB 에만 붙는 칸이라 뺌
  function journalDiff(dbTrials, jTrials) {
    const out = [];
    const strip = t => { if (!t || typeof t !== 'object') return t; const { committedAt, ...rest } = t; return rest; };
    // 한쪽에만 있는 칸(undefined)도 글로 적음 — 전에는 JSON.stringify(undefined).slice 에서 예외가 나 화면엔 ‘journal 을 읽지 못함’ 만 보였음 (2026-11-02)
    const jv = v => v === undefined ? '없음' : String(JSON.stringify(v)).slice(0, 40);
    const n = Math.max((dbTrials || []).length, (jTrials || []).length);
    for (let i = 0; i < n; i++) {
      const a = strip((dbTrials || [])[i]), b = strip((jTrials || [])[i]);
      if (!a || !b) { out.push(`${i + 1}번째 시행: ${a ? 'journal 에 없음' : 'DB 에 없음'}`); continue; }
      const dk = diffKeys(a, b);
      if (dk.length) out.push(`${i + 1}번째 시행: ${dk.slice(0, 4).map(k => `${k} DB ${jv(a[k])} · journal ${jv(b[k])}`).join(' · ')}`);
    }
    return out;
  }

  // 판정: 대조 → 재생한 상태와 재생한 전이로 분류 → 같은 판의 기존 결과와 상태·값 대조 → 실패면 protocol_deviation(숫자 없음). run 은 바꾸지 않음
  function judge(run, P, prior = run.result || null) {
    const au = audit(run, P, prior);
    const safeTrials = Array.isArray(run.trials) ? run.trials.filter(t => t !== null && typeof t === 'object').map(t => ({ ...t, tr: null })) : [];
    const view = au.replayOk ? { ...run, state: au.replayState, trials: run.trials.map((t, i) => ({ ...t, tr: au.replayTr[i] })) } : { ...run, state: null, trials: safeTrials };
    let res;
    try { res = classify(view, P); }
    catch (e) { au.issues.push(`분류 오류 — ${e.message}`); res = classify({ ...run, state: null, trials: [] }, P); }
    res.analysisVersion = P.analysis.version;
    const issues = au.issues.slice();
    if (!au.replayOk && !issues.length) issues.push('시행을 처음부터 다시 계산하지 못함');
    let versionNote = null;
    if (prior) {
      const pv = prior.analysisVersion || run.analysisVersion || null;
      const pStatus = prior.statusBeforeAudit || prior.status;
      if (pv === P.analysis.version) {
        if (pStatus !== res.status) issues.push(`기존 결과: 판정 ${pStatus} 가 같은 판(${pv}) 규칙으로 다시 한 판정 ${res.status} 와 다름`);
        else if (prior.status !== 'protocol_deviation' && run.kind !== 'constant' && (prior.thr ?? null) !== (res.thr ?? null)) issues.push(`기존 결과: 역치 ${desc(prior.thr)} 가 다시 판정 ${res.thr} 와 다름`);
        else if (prior.status !== 'protocol_deviation' && run.kind === 'constant' && (prior.pc ?? null) !== (res.pc ?? null)) issues.push(`기존 결과: 점수 ${desc(prior.pc)} 가 다시 판정 ${res.pc} 와 다름`);
      } else versionNote = { from: pv, to: P.analysis.version, statusFrom: pStatus, statusTo: res.status };
    }
    const ok = issues.length === 0;
    if (!ok) { res.statusBeforeAudit = res.status; res.status = 'protocol_deviation'; if (run.kind === 'constant') res.pc = null; else res.thr = null; }
    return { result: res, audit: { ok, issues: issues.slice(0, 30), nIssues: issues.length, at: new Date().toISOString(), analysisVersion: P.analysis.version, versionNote }, replayOk: au.replayOk };
  }
  // 결과 = judge. 기존 결과는 대조 전에 보존하고(prior), 새 결과는 맨 끝에 저장
  function finalize(run, P) {
    const prior = run.result ? JSON.parse(JSON.stringify(run.result)) : null;
    const j = judge(run, P, prior);
    run.result = j.result;
    return { result: j.result, audit: j.audit, prior };
  }

  // 한 묶음(같은 회기·같은 제시 설정)의 적응 track 들 → Won 2007 회기 결과 (결정된 track 6개 평균)
  //   state: final(6개 모두 숫자 → 평균) · provisional(결정된 track 이 6개 안 됨 — 잠정값은 화면용)
  //     · low(쓴 track 모두 쉬운 끝 쪽: < 0.125 확인 또는 쉬운 끝에 막힘 — 숫자 없음; 모두 확인이면 below) · high(어려운 끝 쪽; 모두 확인이면 above) · mixed(숫자와 숫자 아님이 섞임, 평균 안 냄)
  const LOW = new Set(['below', 'easy']), HIGH = new Set(['above', 'hard']);
  const qOf = t => Q.of(t.sumMilli, 1000 * t.count);
  function wonSummary(runs, need = 6) {
    const tests = runs.filter(r => r.kind === 'adaptive' && !r.practice && r.result).sort((a, b) => (a.order || 0) - (b.order || 0));
    const tracks = tests.map(r => ({ id: r.id, order: r.order, status: r.result.status, ...outcome(r) }));
    const det = tracks.filter(t => t.kind !== 'none');
    const nums = det.filter(t => t.kind === 'num');
    const pm = nums.length ? Q.mean(nums.map(qOf)) : null;
    const invalid = tracks.filter(t => t.invalid).map(t => ({ id: t.id, order: t.order, why: t.invalid }));
    const out = { tracks, det: det.length, need, state: 'provisional', value: null, exact: null, provisional: pm ? Q.num(pm) : null, needMore: Math.max(0, need - det.length),
      note: '', used: [], sd: null, nearEasy: false, invalid };
    if (det.length < need) out.note = `결정된 track ${det.length}/${need}`;
    else {
      const use = det.slice(0, need);
      out.used = use.map(t => t.id);
      const kinds = new Set(use.map(t => t.kind));
      if (kinds.size === 1 && kinds.has('num')) {
        const m = Q.mean(use.map(qOf));
        out.state = 'final'; out.value = Q.num(m); out.exact = Q.str(m); out.sd = Stats.sd(use.map(t => t.value)); out.note = `track ${need}개 평균`;
      } else if ([...kinds].every(k => LOW.has(k))) { out.state = kinds.size === 1 && kinds.has('below') ? 'below' : 'low'; out.note = out.state === 'below' ? '쓴 track 모두 < 0.125 rpo 확인' : '쓴 track 모두 쉬운 끝(0.125)에 막힘 또는 범위 밖 — 숫자 없음'; }
      else if ([...kinds].every(k => HIGH.has(k))) { out.state = kinds.size === 1 && kinds.has('above') ? 'above' : 'high'; out.note = '쓴 track 모두 어려운 끝(11.314) 쪽 — 숫자 없음'; }
      else { out.state = 'mixed'; out.note = '숫자 track 과 끝에 막힘·범위 밖 track 이 섞여 평균을 내지 않음'; }
      out.nearEasy = use.some(t => t.nearEasy);
    }
    if (nums.length > 1 && out.sd === null) out.sdProvisional = Stats.sd(nums.map(t => t.value));
    if (invalid.length) out.note += `${out.note ? ' · ' : ''}값 검증 실패로 뺀 track ${invalid.length}개 (${invalid.map(x => x.why).join(' / ')})`;
    return out;
  }
  // 임상 회기 결과: 결정된(72시행 완료) 첫 측정의 점수
  function clinicalSummary(runs) {
    const tests = runs.filter(r => r.kind === 'constant' && !r.practice && r.result).sort((a, b) => (a.order || 0) - (b.order || 0));
    const tracks = tests.map(r => ({ id: r.id, order: r.order, status: r.result.status, ...outcome(r) }));
    const det = tracks.filter(t => t.kind === 'pc');
    const invalid = tracks.filter(t => t.invalid).map(t => ({ id: t.id, order: t.order, why: t.invalid }));
    const out = { tracks, det: det.length, need: 1, state: 'provisional', value: null, k: null, n: null, note: det.length ? '' : '끝난 72시행 측정 없음', used: [], invalid };
    if (det.length) {
      const t = det[0];
      Object.assign(out, { state: 'final', value: t.value, k: t.k, n: t.n, used: [t.id], notAboveChance: t.notAboveChance, note: '72시행 정답률' + (det.length > 1 ? ` · 같은 회기의 다른 끝난 측정 ${det.length - 1}개는 첫 것만 씀` : '') });
    }
    return out;
  }
  function groupSummary(sess, runs) {
    const pid = sess && sess.protocolKey;
    return pid === 'drennan2014' ? { kind: 'constant', ...clinicalSummary(runs) } : { kind: 'adaptive', ...wonSummary(runs, (PROTOCOLS.won2007.session.tracks)) };
  }
  const presKeyOf = r => r.presKey || (r.pres ? Pres.key(r.pres) : `legacy:${r.condKey || ''}:${r.segment || 0}`);
  const changedDuring = r => !!(r.presChangedDuring && r.presChangedDuring.length);
  // 회기 시작 때의 제시 설정(presRefKey)과 같은 측정 = 주 묶음. 측정 중 설정이 바뀐 측정은 어느 묶음에도 넣지 않음
  const inMainGroup = (sess, r) => !changedDuring(r) && (!(sess && sess.presRefKey) || presKeyOf(r) === sess.presRefKey);
  function sessionGroups(sess, runs) {
    const tests = runs.filter(r => !r.practice && (r.kind === 'adaptive' || r.kind === 'constant'));
    const ok = tests.filter(r => !changedDuring(r));
    const ref = sess && sess.presRefKey;
    const keys = [...new Set(ok.map(presKeyOf))];
    keys.sort((a, b) => (b === ref) - (a === ref));
    const groups = keys.map((k, i) => {
      const rr = ok.filter(r => presKeyOf(r) === k);
      const pres = (rr.find(r => r.pres) || {}).pres || null;
      return { key: k, main: ref ? k === ref : i === 0, pres, diffFromMain: ref && k !== ref && pres && sess.presRef ? Pres.diff(sess.presRef, pres) : [], runs: rr, sum: groupSummary(sess, rr) };
    });
    return { groups, main: groups.find(g => g.main) || null, changed: tests.filter(changedDuring) };
  }
  return { STATUS_TXT, REASON_TXT, FLAG_TXT, NUMERIC, TARGET_P, positionStats, densTable, classify, classifyAdaptive, classifyConstant, outcome, validateRun, audit, judge, finalize,
    isIncluded, numericResultIssue, pcResultIssue, journalDiff, wonSummary, clinicalSummary, groupSummary, sessionGroups, inMainGroup, presKeyOf, Q, deq };
})();

// 회기 순서와 다시 하기
const Queue = (() => {
  // Won: 연습(골랐으면) → track 6개 · 임상: 72시행 측정 1개
  function build(planId, practice) {
    const pl = planOf(planId);
    if (!pl) throw new Error('회기 설계를 모름: ' + planId);
    const q = [];
    if (pl.protocol === 'won2007') {
      if (practice) q.push({ kind: 'adaptive', practice: true, block: 0 });
      for (let i = 0; i < PROTOCOLS.won2007.session.tracks; i++) q.push({ kind: 'adaptive', block: 1 });
    } else q.push({ kind: 'constant', block: 1 });
    return q;
  }
  // 끝난 측정 하나를 보고 큐 끝에 붙일 것 (sess.queue 를 바꿈, 붙인 항목을 돌려줌).
  //   주 묶음의 결정된 결과가 아니면(숫자·범위 밖·점수 없음 · 다른 제시 설정 · 측정 중 설정 바뀜) 같은 종류를 회기 끝에 한 번 다시 (다시 한 것은 또 다시 하지 않음)
  function afterRun(sess, sessRuns, run) {
    const added = [];
    if (run.practice) return added;
    const o = Analysis.outcome(run);
    const main = Analysis.inMainGroup(sess, run);
    if ((o.kind === 'none' || !main) && !run.replacement) {
      const it = { kind: run.kind, block: run.block, replacement: run.id };
      sess.queue.push(it); added.push(it);
    }
    return added;
  }
  return { build, afterRun };
})();

if (typeof module !== 'undefined') module.exports = { TrialPlan, ConstPlan, Exact, Stats, Pres, ConstRun, Analysis, Queue, seedHexOf, TARGET_P };
