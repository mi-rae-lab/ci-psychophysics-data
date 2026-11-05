// 자극 만들기 — 정현 진폭 변조(SAM) 잡음
//  s(t) = [1 + m·sin(2π·fm·t + φ)] · n(t)          (Viemeister 1979; Shen & Richards 2013 식 13)
//  · 반송파 n(t): 구간마다 새로 뽑은 가우스 잡음. 광대역(문헌과 같음) 또는 인공와우 대역(188–7938 Hz)
//  · 변조 시작 위상 φ: 구간마다 0–2π 무작위 (Shen & Richards 2013)
//  · 변조 잡음과 안 변조 잡음의 RMS 를 똑같이 맞춤 → 변조가 만드는 평균 세기 증가(크기 단서)를 없앰 (Viemeister 1979)
//  · 켜짐/꺼짐 경사: 10 ms 직선 (Won et al. 2011, 2015)
'use strict';

const Stim = (() => {
  const TARGET_RMS = 0.05;          // −26 dBFS. m=1 이고 잡음 봉우리 4.5σ 여도 ±0.45 안 → 헤드룸 충분
  const fftCache = {};

  function nextPow2(n) { let p = 1; while (p < n) p <<= 1; return p; }

  // 제자리 반복형 radix-2 FFT. inverse=true 면 역변환(1/n 포함)
  function fft(re, im, inverse) {
    const n = re.length;
    for (let i = 1, j = 0; i < n; i++) {
      let bit = n >> 1;
      for (; j & bit; bit >>= 1) j ^= bit;
      j ^= bit;
      if (i < j) { let t = re[i]; re[i] = re[j]; re[j] = t; t = im[i]; im[i] = im[j]; im[j] = t; }
    }
    let tw = fftCache[n];
    if (!tw) {
      tw = { c: new Float64Array(n / 2), s: new Float64Array(n / 2) };
      for (let k = 0; k < n / 2; k++) { tw.c[k] = Math.cos(2 * Math.PI * k / n); tw.s[k] = Math.sin(2 * Math.PI * k / n); }
      fftCache[n] = tw;
    }
    const sgn = inverse ? 1 : -1;
    for (let len = 2; len <= n; len <<= 1) {
      const half = len >> 1, step = n / len;
      for (let i = 0; i < n; i += len) {
        for (let k = 0; k < half; k++) {
          const wr = tw.c[k * step], wi = sgn * tw.s[k * step];
          const a = i + k, b = a + half;
          const xr = re[b] * wr - im[b] * wi, xi = re[b] * wi + im[b] * wr;
          re[b] = re[a] - xr; im[b] = im[a] - xi;
          re[a] += xr; im[a] += xi;
        }
      }
    }
    if (inverse) for (let i = 0; i < n; i++) { re[i] /= n; im[i] /= n; }
  }

  // 씨앗(seed)으로 되풀이할 수 있는 난수 — mulberry32. 같은 씨앗이면 같은 잡음이 나와서, 기록된 씨앗으로 들려준 소리를 그대로 다시 만들 수 있다.
  function makeRng(seed) {
    let a = seed >>> 0, spare = null;
    const uniform = () => {
      a = (a + 0x6D2B79F5) >>> 0;
      let t = a;
      t = Math.imul(t ^ (t >>> 15), t | 1);
      t ^= t + Math.imul(t ^ (t >>> 7), t | 61);
      return ((t ^ (t >>> 14)) >>> 0) / 4294967296;
    };
    const gauss = () => {
      if (spare !== null) { const s = spare; spare = null; return s; }
      let u = 0; while (u === 0) u = uniform();
      const v = uniform(), r = Math.sqrt(-2 * Math.log(u));
      spare = r * Math.sin(2 * Math.PI * v);
      return r * Math.cos(2 * Math.PI * v);
    };
    return { uniform, gauss };
  }
  function newSeed() {
    try { return crypto.getRandomValues(new Uint32Array(1))[0]; } catch { return Math.floor(Math.random() * 4294967296); }
  }

  function rms(x) { let s = 0; for (let i = 0; i < x.length; i++) s += x[i] * x[i]; return Math.sqrt(s / x.length); }

  // 가우스 잡음을 주파수 영역에서 만든다: 칸마다 무작위 복소수 × 대역 모양, 역변환.
  // 결과는 주기 신호라 앞 N 개를 잘라도 가장자리 왜곡이 없다.
  // band: {type:'wide'} 20 Hz–fs/2 평평 | {type:'brick', lo, hi} 대역 밖 0 | {type:'bp', lo, hi, order} 버터워스 크기 응답
  //  (bp: 가장자리마다 order 차 → order=2 면 12 dB/옥타브. De Ruiter 2015 "fourth-order band-pass" 를 저역·고역 2차씩으로 해석)
  function noise(N, fs, band, rng) {
    const n = nextPow2(N);
    const gauss = rng.gauss;
    const re = new Float64Array(n), im = new Float64Array(n);
    const t = band.type || 'wide';
    const lo = t === 'wide' ? 20 : band.lo, hi = t === 'wide' ? fs / 2 : band.hi;
    const kStart = t === 'bp' ? 1 : Math.max(1, Math.ceil(lo * n / fs));
    const kEnd = t === 'bp' ? n / 2 - 1 : Math.min(n / 2 - 1, Math.floor(hi * n / fs));
    for (let k = kStart; k <= kEnd; k++) {
      let g = 1;
      if (t === 'bp') {
        const f = k * fs / n, o2 = 2 * (band.order || 2);
        g = 1 / Math.sqrt((1 + (lo / f) ** o2) * (1 + (f / hi) ** o2));
      }
      re[k] = gauss() * g; im[k] = gauss() * g;
      re[n - k] = re[k]; im[n - k] = -im[k];
    }
    fft(re, im, true);
    const out = new Float32Array(N);
    for (let i = 0; i < N; i++) out[i] = re[i];
    const r = rms(out) || 1;
    for (let i = 0; i < N; i++) out[i] /= r;
    return out;
  }

  // opts: {fs, dur(초), band:{…}, fm, depthDb(20·log10 m, null 이면 안 변조), phase:'zero'|'random', rampMs, rampShape:'linear'|'cos2', gainDb, seed}
  // phase 'zero' = 논문 식 그대로 sin(2π·fm·t) (Won 2011, Park 2015, De Ruiter 2015), 'random' = Shen & Richards 2013
  // 돌려주는 값: data, seed(되풀이용), rmsDb·peakDb(실제로 나갈 신호의 dBFS), scaled(클리핑 막으려고 줄였는지)
  function make(opts) {
    const { fs, dur, band, fm, depthDb, phase = 'random', rampMs = 10, rampShape = 'linear', gainDb = 0 } = opts;
    const seed = opts.seed ?? newSeed();
    const rng = makeRng(seed);
    const N = Math.round(fs * dur);
    const x = noise(N, fs, band, rng);
    let ph = null;
    if (depthDb !== null && depthDb !== undefined) {
      const m = Math.pow(10, depthDb / 20);
      ph = phase === 'zero' ? 0 : rng.uniform() * 2 * Math.PI;
      const w = 2 * Math.PI * fm / fs;
      for (let i = 0; i < N; i++) x[i] *= 1 + m * Math.sin(w * i + ph);
    }
    // 켜짐·꺼짐 경사를 먼저 씌운 뒤, 실제로 나갈 신호의 RMS 를 목표에 정확히 맞춤 → 변조·비변조 평균 세기 같음.
    // 세 논문 모두 목적을 '평균 세기(RMS) 같게'라고 밝힘 (Won 2011 의 '1 + m²/2 로 나눔'을 진폭에 그대로 쓰면 변조 쪽이 오히려 작아짐).
    // 이전 판(3.0 이전)은 경사 전에 맞춰서, 경사 구간에서 깎이는 에너지가 변조·비변조에 따라 조금 달랐음.
    // 잰 차이(m = 1, 60쌍 평균): Won/Park 10 Hz +0.017 dB, De Ruiter 10 Hz +0.021 dB, 100 Hz 는 0 에 가까움 → 무시할 크기지만 0 으로 만듦.
    const R = Math.min(Math.round(fs * rampMs / 1000), Math.floor(N / 2));
    for (let i = 0; i < R; i++) {
      const t = (i + 0.5) / R;
      const a = rampShape === 'cos2' ? Math.sin(t * Math.PI / 2) ** 2 : t;
      x[i] *= a; x[N - 1 - i] *= a;
    }
    const g = TARGET_RMS * Math.pow(10, gainDb / 20) / (rms(x) || 1);
    for (let i = 0; i < N; i++) x[i] *= g;
    let peak = 0;
    for (let i = 0; i < N; i++) { const v = Math.abs(x[i]); if (v > peak) peak = v; }
    let scaled = false;
    if (peak > 0.99) { const s = 0.99 / peak; for (let i = 0; i < N; i++) x[i] *= s; peak = 0.99; scaled = true; }
    const r = rms(x);
    return { data: x, peak, seed, phase: ph, scaled, rmsDb: 20 * Math.log10(r || 1e-12), peakDb: 20 * Math.log10(peak || 1e-12) };
  }

  // 검증용: 신호의 힐버트 포락선에서 fm 성분 크기로 실제 변조 깊이를 추정 (자체 점검에서 사용)
  function measureDepth(x, fs, fm) {
    const n = nextPow2(x.length);
    const re = new Float64Array(n), im = new Float64Array(n);
    for (let i = 0; i < x.length; i++) re[i] = x[i];
    fft(re, im, false);
    for (let k = 1; k < n / 2; k++) { re[k] *= 2; im[k] *= 2; }
    for (let k = n / 2 + 1; k < n; k++) { re[k] = 0; im[k] = 0; }
    fft(re, im, true);
    // 경사 구간을 뺀 가운데 80% 만 사용
    const a = Math.floor(x.length * 0.1), b = Math.floor(x.length * 0.9);
    let mean = 0, c = 0, s = 0;
    for (let i = a; i < b; i++) {
      const e = Math.hypot(re[i], im[i]);
      mean += e; c += e * Math.cos(2 * Math.PI * fm * i / fs); s += e * Math.sin(2 * Math.PI * fm * i / fs);
    }
    const L = b - a;
    mean /= L;
    return (2 * Math.hypot(c, s) / L) / mean;
  }

  return { make, noise, measureDepth, rms, makeRng, newSeed, TARGET_RMS };
})();
