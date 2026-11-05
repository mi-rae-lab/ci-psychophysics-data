// JS ↔ Lean 대조의 JS 쪽 (Claude, 2026-10-24 — 와우TMTF 3.2, 와우SRD tools/lean/cross_check.js 와 같은 방식)
//   1) deno run --allow-read --allow-write tools/lean/cross_check.js input <입력.txt> <js출력.txt>
//        앱의 js(protocols · stim · track)를 화면 없이 올려, 입력 줄과 같은 꼴의 기대 출력을 같은 순서로 씀
//   2) (tools/lean 에서) .lake/build/bin/crosscheck.exe <입력.txt> <lean출력.txt>
//   3) deno run --allow-read tools/lean/cross_check.js check <js출력.txt> <lean출력.txt>
//        한 줄씩 비교 → 종류마다 같은 줄 수 · 다른 줄(처음 30개) · 변조 시험(종류마다 한 줄을 일부러 바꾼 lean 출력은 반드시 다르게 잡혀야 함)
//        PV(우연 판정 p) · GAIN(대역 모양) 은 js 부동소수와 Lean 정확한 분수를 허용 오차로, 나머지는 글자 그대로.
//        마지막 줄 ‘판정: 통과/실패’ — 다른 줄이 있거나, 비교한 종류가 비거나, 변조를 못 잡으면 종료 코드 1
const root = new URL('../../', import.meta.url);
const read = f => Deno.readTextFileSync(new URL(f, root));
(0, eval)(['js/protocols.js', 'js/stim.js', 'js/track.js'].map(read).join('\n;\n') +
  '\n;globalThis.__T = { PROTOCOLS, CUSTOM_PROCS, CUSTOM_FMS, FINE_FMS, fmChoices, isPaperFm, resolveProtocol, Stim, Track, binomTail };');
const { PROTOCOLS, FINE_FMS, fmChoices, isPaperFm, resolveProtocol, Stim, Track } = globalThis.__T;
const csv = a => a.length ? a.join(',') : '-';
const b01 = x => x ? '1' : '0';
const TOL = { PV: 1e-9, GAIN: 2e-5 };   // 상대 오차 (GAIN: noise() 출력이 Float32Array 라 칸 크기에 2⁻²⁴ 수준 반올림)

// 결정적인 입력 만들기용 난수 (앱 makeRng 와 별개로 고정 — 입력만 정함)
function lcg(seed) { let s = seed >>> 0; return () => { s = (Math.imul(s, 1664525) + 1013904223) >>> 0; return s / 4294967296; }; }

function makeInput() {
  const L = [], r = lcg(20261024);
  // RNG: 끝 값 · 상수 · 무작위 씨앗
  for (const s of [0, 1, 2, 0x6D2B79F5, 0x7FFFFFFF, 0x80000000, 4294967295]) L.push(`RNG ${s} 64`);
  for (let i = 0; i < 300; i++) L.push(`RNG ${Math.floor(r() * 4294967296)} ${i < 10 ? 2000 : 48}`);
  // RAMP: 실제 쓰는 값 + 반올림 반값(15 ms × 44.1 kHz = 661.5) + N/2 로 막히는 짧은 구간
  //  (N = 2 는 빼고 3 · 4: 두 표본이 모두 1/2 이면 전체 이득과 구별되지 않아 출력에서 R 을 읽을 수 없음 — 세기 맞춤 뒤 소리도 같음)
  for (const fs of [44100, 48000, 22050, 96000]) for (const ms of [10, 30, 15, 1, 7]) for (const N of [fs, fs / 2, 600, 101, 4, 3]) L.push(`RAMP ${fs} ${ms} ${N}`);
  // BINS: 세 대역 × fs × 길이
  for (const ty of ['wide', 'bp', 'brick']) for (const fs of [44100, 48000, 22050, 96000]) for (const N of [fs, fs / 2, 1000, 4096, 12345]) L.push(`BINS ${ty} ${fs} ${N}`);
  // SPEC: N = 2 의 거듭제곱(자르지 않음)에서 DFT 로 칸 범위 · 모양
  for (const ty of ['wide', 'bp', 'brick']) for (const fs of [44100, 48000]) for (const N of [1024, 4096]) {
    const ks = [];
    for (let k = 1; k < N / 2; k = k < 16 ? k + 1 : Math.ceil(k * 1.25)) ks.push(k);
    ks.push(N / 2 - 1);
    L.push(`SPEC ${ty} ${fs} ${N} ${N / 16} ${[...new Set(ks)].join(',')}`);
  }
  for (const fs of [44100, 48000, 22050, 96000, 32000, 8000]) for (const [a, b] of [[1, 1], [1, 2], [8, 10], [3, 10], [1, 3]]) L.push(`DUR ${fs} ${a} ${b}`);
  L.push('GRID');
  // TRACK: 절차 6가지 × 듣는 사람 모형(정신물리 곡선 · 우연 · 늘 맞음 · 늘 틀림 · 번갈아) — 응답은 160 개를 넘게도
  const protos = ['uw', 'deruiter', 'std2', 'std3', 'short2', 'short3'];
  let id = 0;
  for (const pr of protos) {
    const P = protoP(pr), chance = 1 / P.nAFC;
    for (let j = 0; j < 60; j++) {
      const model = j % 6, T = new Track(P);
      let seq = '';
      const thr = -6 - (j % 9) * 4, slope = 1 + (j % 4);
      for (let i = 0; i < 200; i++) {
        let c;
        if (model === 0 || model === 1) { const d = T.depth; const p = chance + (1 - chance) / (1 + Math.exp(-(d - thr) / slope)); c = r() < p; }
        else if (model === 2) c = r() < chance;
        else if (model === 3) c = i < 3 + (j % 5) ? r() < 0.5 : true;           // 늘 맞음 → −40 dB 바닥
        else if (model === 4) c = false;                                        // 늘 틀림 → 0 dB 천장 · 160 개 · stop4
        else c = (i % 3) !== 2;                                                 // 맞음 맞음 틀림 반복
        seq += c ? 'C' : 'W';
        if (!T.done) T.respond(c);
      }
      L.push(`TRACK ${id++} ${pr} ${seq}`);
    }
  }
  return L;
}

function protoP(pr) {
  if (pr === 'uw') return { ...PROTOCOLS.uw };
  if (pr === 'deruiter') return { ...PROTOCOLS.deruiter };
  const proc = pr.startsWith('std') ? 'std' : 'short', nAFC = +pr.slice(-1);
  return resolveProtocol({ proto: 'custom', proc, nAFC, dur: 1, isi: 0, ramp: 'linear', band: 'wide', level: 65, rove: 0 });
}

function bandOf(ty) { return ty === 'bp' ? { type: 'bp', lo: 80, hi: 8500, order: 2 } : ty === 'brick' ? { type: 'brick', lo: 188, hi: 7938 } : { type: 'wide' }; }

// 실수 DFT 한 칸 (N 이 작을 때만)
function dftMag2(x, k) {
  const N = x.length; let re = 0, im = 0;
  for (let t = 0; t < N; t++) { const a = -2 * Math.PI * k * t / N; re += x[t] * Math.cos(a); im += x[t] * Math.sin(a); }
  return re * re + im * im;
}

function jsLine(ln) {
  const p = ln.split(' ');
  switch (p[0]) {
    case 'RNG': {
      const g = Stim.makeRng(+p[1]), out = [];
      for (let i = 0; i < +p[2]; i++) out.push(g.uniform() * 4294967296);
      return [`RNG ${p[1]} ${csv(out)}`];
    }
    case 'RAMP': {
      const fs = +p[1], ms = +p[2], N = +p[3], dur = N / fs, seed = 777;
      const base = { fs, dur, band: { type: 'wide' }, fm: 10, depthDb: null, phase: 'zero', rampShape: 'linear', gainDb: 0, seed };
      const x = Stim.make({ ...base, rampMs: ms }).data, y = Stim.make({ ...base, rampMs: 0 }).data;
      if (x.length !== N || y.length !== N) return [`RAMP ${p[1]} ${p[2]} ${p[3]} 길이오류 0`];
      const a = Array.from(x, (v, i) => v / y[i]);   // = 경사 이득 w_i × (두 구간의 전체 이득 비 c)
      const w = (R, i) => i < R ? (2 * i + 1) / (2 * R) : i >= N - R ? (2 * (N - 1 - i) + 1) / (2 * R) : 1;
      const fits = (R, c) => { for (let i = 0; i < N; i++) if (Math.abs(a[i] / c - w(R, i)) > 1e-5) return false; return true; };
      // (가) 가운데에 이득 1 인 표본이 있을 때(R < N/2): c = 가운데 비, R = 앞에서 이득이 1 보다 작은 표본 수
      const half = Math.floor(N / 2), cA = a[half];
      let RA = 0; while (RA < half && a[RA] / cA < 1 - 1e-6) RA++;
      let R = RA, ok = fits(RA, cA);
      // (나) N 이 짝수이고 경사가 구간 전체(R = N/2)일 때: 가운데 이득이 1 이 아님 → c = 첫 표본 비 × 2R
      if (!ok && N % 2 === 0) { const cB = a[0] * N; if (fits(N / 2, cB)) { R = N / 2; ok = true; } }
      return [`RAMP ${p[1]} ${p[2]} ${p[3]} ${R} ${b01(ok)}`];
    }
    case 'BINS': {
      let calls = 0;
      Stim.noise(+p[3], +p[2], bandOf(p[1]), { gauss: () => { calls++; return 0; } });
      return [`BINS ${p[1]} ${p[2]} ${p[3]} ${calls}`];
    }
    case 'SPEC': {
      const ty = p[1], fs = +p[2], N = +p[3], kref = +p[4], ks = p[5].split(',').map(Number);
      const x = Stim.noise(N, fs, bandOf(ty), { gauss: () => 1 });
      const mags = [];
      for (let k = 0; k <= N / 2; k++) mags.push(dftMag2(x, k));
      const mx = Math.max(...mags), on = mags.map(v => v > 1e-8 * mx);
      const k0 = on.indexOf(true), k1 = on.lastIndexOf(true);
      const out = [`SPEC ${ty} ${fs} ${N} ${k0} ${k1}`];
      if (ty === 'bp') for (const k of ks) out.push(`GAIN ${ty} ${fs} ${N} ${k} ${mags[k] / mags[kref]}`);
      else {
        let lo = Infinity, hi = 0;
        for (let k = k0; k <= k1; k++) { lo = Math.min(lo, mags[k]); hi = Math.max(hi, mags[k]); }
        let gap = true; for (let k = 0; k <= N / 2; k++) if ((k < k0 || k > k1) && on[k]) gap = false;
        out.push(`FLAT ${ty} ${fs} ${N} ${b01(hi / lo - 1 < 1e-5 && gap)}`);
      }
      return out;
    }
    case 'DUR': return [`DUR ${p[1]} ${p[2]} ${p[3]} ${Math.round(+p[1] * (+p[2] / +p[3]))}`];
    case 'GRID': {
      const custom = resolveProtocol({ proto: 'custom', proc: 'std', nAFC: 2, dur: 1, isi: 0, ramp: 'linear', band: 'wide', level: 65, rove: 0 });
      return [`GRID ${csv(FINE_FMS)}`,
        `CHOICES uw ${csv(fmChoices(PROTOCOLS.uw))}`, `CHOICES deruiter ${csv(fmChoices(PROTOCOLS.deruiter))}`, `CHOICES custom ${csv(fmChoices(custom))}`,
        `PAPER uw ${csv(FINE_FMS.filter(f => isPaperFm('uw', f)))}`, `PAPER deruiter ${csv(FINE_FMS.filter(f => isPaperFm('deruiter', f)))}`];
    }
    case 'TRACK': {
      const P = protoP(p[2]), T = new Track(P);
      for (const ch of p[3]) T.respond(ch === 'C');
      const res = T.result(), ch = T.chance();
      const out = [`TRACK ${p[1]} ${p[2]} ${b01(T.done)} ${b01(T.ceiling)} ${b01(T.incomplete)} ${T.depth} ${T.run} ${T.dir} ${T.n0} ${T.k0} ${T.ceilMiss} ` +
        `${csv(T.reversals)} ${csv(T.revAt)} ${csv(T.trials.map(t => t.d))} ${res.thr === null ? '-' : String(res.thr)} ${ch.p === null ? '-' : b01(ch.atChance)}`];
      if (ch.p !== null) out.push(`PV ${p[1]} ${ch.p}`);
      return out;
    }
  }
  return [`? ${ln}`];
}

// 분수 "a/b" 를 부동소수로 (BigInt 로 17자리까지)
function fracToNum(s) {
  const [a, b] = s.split('/').map(v => BigInt(v));
  if (a === 0n) return 0;
  const neg = (a < 0n) !== (b < 0n), A = a < 0n ? -a : a, B = b < 0n ? -b : b;
  // A/B = m × 10^e
  const scale = 10n ** 40n, q = (A * scale) / B;
  const v = Number(q) / 1e40;
  return neg ? -v : v;
}

function same(js, le) {
  if (js === le) return true;
  const a = js.split(' '), b = le.split(' ');
  if (a.length !== b.length || a[0] !== b[0]) return false;
  const tol = TOL[a[0]];
  if (!tol) return false;
  for (let i = 0; i < a.length - 1; i++) if (a[i] !== b[i]) return false;
  const x = +a[a.length - 1], y = fracToNum(b[b.length - 1]);
  if (!Number.isFinite(x) || !Number.isFinite(y)) return false;
  return Math.abs(x - y) <= tol * Math.max(Math.abs(y), 1e-300);
}

function compare(js, lean) {
  const kinds = {}, bad = [];
  if (js.length !== lean.length) bad.push(`줄 수 다름: js ${js.length} · lean ${lean.length}`);
  const n = Math.min(js.length, lean.length);
  let worst = { PV: 0, GAIN: 0 };
  for (let i = 0; i < n; i++) {
    const k = js[i].split(' ')[0];
    kinds[k] = kinds[k] || { n: 0, ok: 0 };
    kinds[k].n++;
    if (same(js[i], lean[i])) {
      kinds[k].ok++;
      if (TOL[k] && js[i] !== lean[i]) {
        const a = js[i].split(' '), b = lean[i].split(' '), x = +a[a.length - 1], y = fracToNum(b[b.length - 1]);
        worst[k] = Math.max(worst[k], Math.abs(x - y) / Math.max(Math.abs(y), 1e-300));
      }
    } else if (bad.length < 30) bad.push(`${i + 1}: js «${js[i].slice(0, 200)}» ≠ lean «${lean[i].slice(0, 200)}»`);
    else bad.push(null);
  }
  return { kinds, bad, worst };
}

const mode = Deno.args[0];
if (mode === 'input') {
  const L = makeInput();
  Deno.writeTextFileSync(Deno.args[1], L.join('\n') + '\n');
  const out = L.flatMap(jsLine);
  Deno.writeTextFileSync(Deno.args[2], out.join('\n') + '\n');
  console.log(`입력 ${L.length} 줄 · js 출력 ${out.length} 줄`);
} else if (mode === 'check') {
  const rd = f => Deno.readTextFileSync(f).split('\n').filter(s => s.length);
  const js = rd(Deno.args[1]), lean = rd(Deno.args[2]);
  const { kinds, bad, worst } = compare(js, lean);
  const need = ['RNG', 'RAMP', 'BINS', 'SPEC', 'GAIN', 'FLAT', 'DUR', 'GRID', 'CHOICES', 'PAPER', 'TRACK', 'PV'];
  let pass = bad.length === 0;
  for (const k of need) {
    const v = kinds[k];
    console.log(`${k.padEnd(8)} ${v ? `${v.ok}/${v.n}` : '없음'}`);
    if (!v || v.n === 0 || v.ok !== v.n) pass = false;
  }
  console.log(`허용 오차 안 가장 큰 상대 차: PV ${worst.PV.toExponential(2)} (허용 ${TOL.PV}) · GAIN ${worst.GAIN.toExponential(2)} (허용 ${TOL.GAIN})`);
  const shown = bad.filter(Boolean);
  if (shown.length) { console.log(`다른 줄 ${bad.length}개 (처음 ${shown.length}개):`); for (const b of shown) console.log('  ' + b); }
  // 변조 시험: 종류마다 첫 줄의 마지막 글자를 바꾼 lean 출력은 반드시 다르게 잡혀야 함
  let mutOk = true;
  for (const k of need) {
    const i = lean.findIndex(l => l.split(' ')[0] === k);
    if (i < 0) { mutOk = false; continue; }
    const m = lean.slice();
    const last = m[i].slice(-1);
    m[i] = m[i].slice(0, -1) + (last === '1' ? '2' : '1');
    if (TOL[k]) {   // 숫자 비교 줄은 값을 크게 바꿈
      const parts = lean[i].split(' '); const [a, b] = parts[parts.length - 1].split('/');
      parts[parts.length - 1] = `${BigInt(a) * 2n + 1n}/${b}`; m[i] = parts.join(' ');
    }
    const r = compare(js, m);
    const caught = r.bad.length > 0;
    console.log(`변조 ${k.padEnd(8)} ${caught ? '잡음' : '못 잡음!'}`);
    if (!caught) mutOk = false;
  }
  pass = pass && mutOk;
  console.log(`판정: ${pass ? '통과' : '실패'}`);
  if (!pass) Deno.exit(1);
} else {
  console.log('쓰는 법: input <입력> <js출력> | check <js출력> <lean출력>');
  Deno.exit(2);
}
