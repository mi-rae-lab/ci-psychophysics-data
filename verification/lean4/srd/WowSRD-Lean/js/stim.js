// 정적 리플(spectral ripple) 자극 합성 — 화면·소리와 떨어진 순수 계산 (본 화면·worker·tests.html·Deno 시험이 같이 씀)
//
// Won 2007 · Won 2011 JASA 130:2088 식 (1) · Drennan 2014:
//   s(t) = Σ_i a_i · sin(2π f_i t + φ_i),   f_i = 100·50^(i/N), i = 0…N−1   (N = 200: Won 2007 · N = 2555: Drennan 2014 임상)
//   a_i(dB) = D·|sin(π·R·F_i + θ)| + G(f_i),   F_i = log2(f_i/100) = i·log2(50)/N,  D = 30 dB
//   θ = 0 (표준) / π/2 (뒤집힘) — 임상 검사는 시행마다 θ 무작위, 뒤집힘 = θ + π/2
//   G = 말소리 장기 평균 스펙트럼 이득 (js/ltass.js — Byrne 1994, 원문 대기 중이면 0)
//   φ_i = 2π·u32/2^32, 구간 씨앗(128비트)으로 xoshiro128** 에서 i 순서대로
// 크기: 경사 전 0.5 s RMS = levelDbfs + roveDb, 앞뒤 150 ms 선형 경사 (가운데 200 ms 일정)
// 순음은 회전(복소수 곱) 되풀이로 만들되 4096 표본마다 cos·sin 으로 다시 맞춤 (쌓이는 오차 < 1e-12, 파이썬 직접 계산과 대조).
'use strict';

const Stim = (() => {
  const FS = 44100;
  const LEN = Math.round(0.5 * FS);        // 22050 표본 = 500 ms
  const RAMP_N = Math.round(0.15 * FS);    // 6615 표본 = 150 ms
  const BLOCK = 4096;
  const TWO32 = 4294967296;
  const D_DB = 30;
  const FP_IDX = [441, 3307, 6614, 6615, 11025, 15435, 18742, 21609];   // 지문: 출력 표본 몇 개 (경사 안·경계·가운데)
  const L50 = Math.log2(50);
  const tabs = new Map();

  function toneTable(N) {
    if (!(Number.isInteger(N) && N >= 2 && N <= 20000)) throw new Error('운반음 수 N 이 이상함: ' + N);
    let t = tabs.get(N);
    if (t) return t;
    const F = new Float64Array(N), X = new Float64Array(N), W = new Float64Array(N), G = new Float64Array(N);
    for (let i = 0; i < N; i++) {
      X[i] = i * L50 / N;               // 옥타브 (100 Hz 부터)
      F[i] = 100 * Math.pow(50, i / N);
      W[i] = 2 * Math.PI * F[i] / FS;
      G[i] = ltassGainDb(F[i]);
    }
    t = { N, F, X, W, G };
    tabs.set(N, t);
    return t;
  }
  // 운반음마다 dB 진폭 (상대) — 무늬 + 말소리 모양
  function envelopeDb(N, rpo, theta) {
    const t = toneTable(N), out = new Float64Array(N);
    for (let i = 0; i < N; i++) out[i] = D_DB * Math.abs(Math.sin(Math.PI * rpo * t.X[i] + theta)) + t.G[i];
    return out;
  }
  const ramp = n => n < RAMP_N ? n / RAMP_N : n >= LEN - RAMP_N ? (LEN - 1 - n) / RAMP_N : 1;

  function check(spec) {
    const { N, rpo, theta, seedHex, levelDbfs, roveDb } = spec;
    toneTable(N);
    if (!(typeof rpo === 'number' && Number.isFinite(rpo) && rpo > 0 && rpo < 100)) throw new Error('밀도 R 이 이상함: ' + rpo);
    if (!(typeof theta === 'number' && Number.isFinite(theta))) throw new Error('무늬 위상 θ 가 이상함: ' + theta);
    if (!/^[0-9a-f]{32}$/.test(seedHex)) throw new Error('씨앗 형식이 틀림: ' + seedHex);
    if (!(typeof levelDbfs === 'number' && Number.isFinite(levelDbfs) && levelDbfs < 0)) throw new Error('크기 levelDbfs 가 이상함: ' + levelDbfs);
    if (!(Number.isInteger(roveDb) && roveDb >= -4 && roveDb <= 4)) throw new Error('크기 흔들기는 −4…+4 dB 정수: ' + roveDb);
  }

  // 한 소리(구간). spec = { N, rpo, theta, seedHex, levelDbfs, roveDb }
  function render(spec) {
    check(spec);
    const t = toneTable(spec.N), N = t.N;
    const r = Rng.fromHex(spec.seedHex);
    const y = new Float64Array(LEN);
    for (let i = 0; i < N; i++) {
      const phi = 2 * Math.PI * (r.u32() / TWO32);
      const a = Math.pow(10, (D_DB * Math.abs(Math.sin(Math.PI * spec.rpo * t.X[i] + spec.theta)) + t.G[i]) / 20);
      const w = t.W[i], cw = Math.cos(w), sw = Math.sin(w);
      for (let n0 = 0; n0 < LEN; n0 += BLOCK) {
        const th = w * n0 + phi;
        let re = Math.cos(th), im = Math.sin(th);
        const n1 = Math.min(LEN, n0 + BLOCK);
        for (let n = n0; n < n1; n++) {
          y[n] += a * im;
          const q = re * cw - im * sw; im = re * sw + im * cw; re = q;
        }
      }
    }
    let ss = 0;
    for (let n = 0; n < LEN; n++) ss += y[n] * y[n];
    const rmsRaw = Math.sqrt(ss / LEN);
    if (!(rmsRaw > 0)) throw new Error('RMS 가 0');
    const gain = Math.pow(10, (spec.levelDbfs + spec.roveDb) / 20) / rmsRaw;
    const pcm = new Float32Array(LEN);
    let pk = 0, so = 0;
    for (let n = 0; n < LEN; n++) {
      const v = Math.fround(y[n] * gain * ramp(n));
      pcm[n] = v; so += v * v;
      const av = Math.abs(v); if (av > pk) pk = av;
    }
    return { pcm, stats: { rmsRaw, gainDb: 20 * Math.log10(gain), rmsOutDbfs: 10 * Math.log10(so / LEN), peakDbfs: 20 * Math.log10(pk), fp: FP_IDX.map(i => pcm[i]) } };
  }

  // 한 시행의 세 구간 명세 — 표적 구간만 뒤집힘(θ + π/2). P = 절차, plan = TrialPlan.draw 결과, k = 밀도 칸
  function trialSpecs(P, plan, k) {
    const base = P.stimulus.phase_mode === 'random' ? plan.theta : 0;
    const rpo = DENS_MILLI[k] / 1000;
    if (!(rpo > 0)) throw new Error('밀도 칸 k 가 이상함: ' + k);
    return [0, 1, 2].map(j => ({ N: P.stimulus.n_tones, rpo, theta: plan.targetPos === j + 1 ? base + Math.PI / 2 : base,
      seedHex: plan.seeds[j], levelDbfs: P.stimulus.level_dbfs, roveDb: plan.roves[j] }));
  }

  return { FS, LEN, RAMP_N, BLOCK, D_DB, FP_IDX, toneTable, envelopeDb, ramp, render, trialSpecs, check };
})();

if (typeof module !== 'undefined') module.exports = Stim;
