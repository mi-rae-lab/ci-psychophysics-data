// 적응 계단 — 2-down 1-up (70.7%, Levitt 1971). 깊이 단위 = 20·log10(m) dB, 상한 0 dB(100%).
//  규칙(시작 깊이, 큰/작은 보폭, 보폭 바꾸는 반전 수, 총 반전, 평균할 마지막 반전 수)은 절차(protocols.js)에서 받음.
//  ceiling 'stop4' : 0 dB 에서 4번 틀리면 '측정 불가'로 끝내고 0 dB 로 기록 (De Ruiter 2015 의 0 dB 처리)
//  ceiling 'none'  : 논문(Won 2011, Park 2015)처럼 끝까지 진행. 대신 0 dB 시행의 정답률로 '우연 수준' 여부를 따로 판정.
//  모의 실험(2AFC, Won 규칙): 변조를 전혀 못 듣는 청취자도 끝까지 하면 평균 −2.0 dB(SD 1.4)가 나옴 — 바닥 효과.
'use strict';

// 이항 검정: n 번 중 k 번 이상 맞힐 확률 (정답 확률 p0 일 때)
function binomTail(k, n, p0) {
  let s = 0;
  for (let i = k; i <= n; i++) {
    let c = 1; for (let j = 0; j < i; j++) c = c * (n - j) / (j + 1);
    s += c * p0 ** i * (1 - p0) ** (n - i);
  }
  return Math.min(1, s);
}

class Track {
  // P: {nAFC, startDb, bigUntil, big, small, totalRev, avgLast, ceiling}
  constructor(P, opt = {}) {
    this.P = P;
    this.maxDb = 0; this.minDb = -40;
    this.depth = P.startDb ?? 0;
    this.ceilingLimit = 4;
    this.maxTrials = opt.maxTrials ?? 160;
    this.run = 0; this.dir = 0;
    this.reversals = []; this.trials = []; this.revAt = [];   // revAt (3.1): 반전마다 그 반전을 만든 시행의 번호(0부터)
    this.ceilMiss = 0; this.n0 = 0; this.k0 = 0;
    this.done = false; this.ceiling = false; this.incomplete = false;
  }
  step() { return this.reversals.length < this.P.bigUntil ? this.P.big : this.P.small; }
  move(d) {
    if (this.dir !== 0 && d !== this.dir) { this.reversals.push(this.depth); this.revAt.push(this.trials.length - 1); }
    this.dir = d;
    this.depth = Math.max(this.minDb, Math.min(this.maxDb, this.depth + d * this.step()));
  }
  respond(correct, extra = {}) {
    if (this.done) return;
    this.trials.push({ d: this.depth, c: correct ? 1 : 0, ...extra });
    if (this.depth >= this.maxDb) { this.n0++; if (correct) this.k0++; else this.ceilMiss++; }
    if (correct) { this.run++; if (this.run >= 2) { this.run = 0; this.move(-1); } }
    else { this.run = 0; this.move(+1); }
    if (this.P.ceiling === 'stop4' && this.ceilMiss >= this.ceilingLimit) { this.done = true; this.ceiling = true; return; }
    if (this.reversals.length >= this.P.totalRev) { this.done = true; return; }
    if (this.trials.length >= this.maxTrials) { this.done = true; this.incomplete = true; }
  }
  // 100% 변조 시행에서 우연보다 잘 맞혔는가 (단측 이항 검정)
  chance() {
    const p0 = 1 / this.P.nAFC;
    if (this.n0 < 6) return { n0: this.n0, k0: this.k0, p: null, atChance: false };
    const p = binomTail(this.k0, this.n0, p0);
    return { n0: this.n0, k0: this.k0, p, atChance: p > 0.05 };
  }
  result() {
    const ch = this.chance();
    // 0 dB 에서 4번 틀려 멈춘 경우: 기록값은 0 dB(De Ruiter 처리). '우연 수준'은 100% 시행 정답률로 따로 판정한다
    // (이전 판은 여기서 무조건 우연으로 표시 → 100% 를 우연보다 잘 맞힌 경우(예: 8/12)도 '못 들음'으로 잘못 보였음)
    if (this.ceiling) return { thr: 0, ceiling: true, sd: null, used: [], ...ch };
    const used = this.reversals.slice(-this.P.avgLast);
    if (used.length < 4) return { thr: null, ceiling: false, sd: null, used, incomplete: true, ...ch };
    const mean = used.reduce((a, b) => a + b, 0) / used.length;
    const sd = Math.sqrt(used.reduce((a, b) => a + (b - mean) ** 2, 0) / Math.max(1, used.length - 1));
    return { thr: +mean.toFixed(2), ceiling: false, sd: +sd.toFixed(2), used, incomplete: this.incomplete || used.length < this.P.avgLast, ...ch };
  }
}
