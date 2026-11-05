// 검사 절차 — 논문 원문(본문)을 그대로 옮긴 것. 같은 절차로 재야 그 논문의 숫자와 직접 비교할 수 있다.
'use strict';

const PROTOCOLS = {
  // Won et al. 2011 JASA 130:376 (DOI 10.1121/1.3592521) 실험 1 · Park et al. 2015 JARO 16:389 (DOI 10.1007/s10162-014-0499-z)
  uw: {
    id: 'uw',
    label: 'Won 2011 · Park 2015 방식',
    sub: '2구간 2AFC · 1초+1초 이어 붙임 · 광대역 · 65 dBA',
    nAFC: 2, dur: 1, isi: 0,                 // "Acoustic stimuli were 2-s in duration. One of the two 1-s observation intervals … concatenated with no gap"
    rampMs: 10, rampShape: 'linear',          // "gated on and off with 10 ms linear ramps"
    band: { type: 'wide' },                   // "wide band noise" (Park: "wideband Gaussian noise carrier … refreshed for every observation")
    phase: 'zero',                            // 식에 위상 항 없음: [f(t)][1 + m·sin(2π·fm·t)]
    startDb: 0, bigUntil: 4, big: 4, small: 2, totalRev: 14, avgLast: 10,   // 100% 시작, 4번째 반전까지 4 dB, 다음 10번 2 dB, 마지막 10번 평균
    ceiling: 'none',                          // 논문은 중단 규칙을 적지 않음 → 끝까지 진행(우연 수준 표시는 따로)
    fms: [10, 50, 75, 100, 150, 200, 300],    // Won 실험 1 (Park 은 75 Hz 를 뺀 6개)
    fmSets: [
      ['Won 2011 전체 7개', [10, 50, 75, 100, 150, 200, 300]],
      ['Park 2015 6개', [10, 50, 100, 150, 200, 300]],
      ['Won 단축 5개 (30–40분)', [10, 50, 100, 150, 300]],
    ],
    reps: 2, extraIfDiff: 3,                  // Park: 두 번이 3 dB 넘게 다르면 세 번째 (Won 2011 그림 9 의 단축법)
    level: 65, levelUnit: 'dBA', dist: 1,
    feedback: true,                           // "Visual feedback of the correct answer was given after each presentation"
    refs: ['park_nh_adult', 'won_ci_adult'],
  },
  // De Ruiter et al. 2015 Ear Hear 36:557 (DOI 10.1097/AUD.0000000000000162)
  deruiter: {
    id: 'deruiter',
    label: 'De Ruiter 2015 방식',
    sub: '3구간 oddity · 0.5초 · 80–8500 Hz · 65 dB SPL',
    nAFC: 3, dur: 0.5, isi: 0.5,              // "The stimulus duration, as well as the interstimulus duration, was 500 msec"
    rampMs: 30, rampShape: 'linear',          // "30-msec linear ramps"
    band: { type: 'bp', lo: 80, hi: 8500, order: 2 },   // "fourth-order band-pass filter with cut-off frequencies of 80 and 8500 Hz" (가장자리마다 2차로 해석)
    phase: 'zero',
    startDb: -2, bigUntil: 2, big: 4, small: 2, totalRev: 8, avgLast: 6,  // −2 dB 시작, 4 dB → 반전 2번 뒤 2 dB, 반전 8번 중 마지막 6번 평균
    ceiling: 'stop4',                         // "unable to detect … the threshold was reported as 0 dB"
    fms: [5, 10, 50, 75, 100, 150, 200],
    fmSets: [['De Ruiter 7개', [5, 10, 50, 75, 100, 150, 200]]],
    reps: 2, extraIfDiff: null,               // 7개 한 바퀴를 두 번, 두 값 평균
    level: 65, levelUnit: 'dB SPL', dist: 1,
    feedback: true,                           // 논문에 언급 없음
    refs: ['deruiter_post', 'deruiter_pre'],
  },
};

// 직접 정하기 — 이전 판의 자유 설정
const CUSTOM_PROCS = {
  std:   { label: '반전 14번, 마지막 10번 평균 (4→2 dB, Won 규칙)', bigUntil: 4, big: 4, small: 2, totalRev: 14, avgLast: 10 },
  short: { label: '반전 8번, 마지막 6번 평균 (4→2 dB, De Ruiter 규칙)', bigUntil: 2, big: 4, small: 2, totalRev: 8, avgLast: 6 },
};
// 3.3.1 (2026-11-03): 66 · 67 · 68 · 69 Hz 더함 — 사용자 요청, 오른쪽에서 65 Hz(측정됨)와 70 Hz(측정 불가) 사이를 1 Hz 간격으로
// 3.3.2 (2026-11-03): 61 · 62 · 63 Hz 더함 — 사용자 요청, 60–70 Hz 를 1 Hz 간격으로 채움(60 · 65 · 70 은 5 Hz 칸, 64 는 원래 목록)
// 3.3.3 (2026-11-04): 56 · 57 · 58 · 59 Hz 더함 — 사용자 요청, 55–70 Hz 전체를 1 Hz 간격으로
const CUSTOM_FMS = [2, 4, 5, 8, 10, 16, 32, 50, 56, 57, 58, 59, 61, 62, 63, 64, 66, 67, 68, 69, 75, 100, 128, 150, 200, 256, 300, 512];

// 5 Hz 간격 변조 주파수 (3.2, 2026-10-24 사용자 요청 ‘5 Hz 별로 변조를 따로 추가 — 이제 정밀하게 측정’)
// 논문 절차(구간 · 길이 · 경사 · 대역 · 계단 · 반복)는 그대로 두고, 변조 주파수만 5–300 Hz 를 5 Hz 간격으로 따로 고를 수 있게 함
// (300 Hz = Won 2011 실험 1 의 가장 높은 주파수). 논문 주파수(PROTOCOLS[*].fms)는 모두 이 안에 있음.
// 논문 주파수가 아닌 것은 문헌 값이 없어 문헌과 비교하지 않고, 요약 지표(지수 맞춤 · 평균 MDT · 넓이 · Park 식 3)에서도 뺌.
const FINE_STEP = 5, FINE_MAX = 300;
const FINE_FMS = Array.from({ length: FINE_MAX / FINE_STEP }, (_, i) => (i + 1) * FINE_STEP);
// 화면에서 고를 수 있는 변조 주파수 — 논문 절차: 5 Hz 간격 60개, 직접 정하기: 이전 목록(2 · 4 · 8 … 512) + 5 Hz 간격
function fmChoices(Pr) { return [...new Set([...(Pr.id === 'custom' ? CUSTOM_FMS : []), ...FINE_FMS, ...Pr.fms])].sort((a, b) => a - b); }
// 이 절차의 논문 주파수인가 (직접 정하기는 논문이 없으므로 늘 false)
function isPaperFm(protoId, fm) { return !!PROTOCOLS[protoId] && PROTOCOLS[protoId].fms.includes(fm); }

// 화면의 조건 값 → 실제 절차 하나로
function resolveProtocol(c) {
  if (c.proto !== 'custom') return { ...PROTOCOLS[c.proto] };
  const pr = CUSTOM_PROCS[c.proc] || CUSTOM_PROCS.std;
  const { label: ruleLabel, ...rule } = pr;   // 3.3: 계단 규칙의 이름이 절차 이름('직접 정하기')을 덮어쓰던 것 — 규칙 이름은 ruleLabel 로 따로
  return {
    id: 'custom', label: '직접 정하기', ruleLabel, nAFC: c.nAFC, dur: c.dur, isi: c.isi,
    rampMs: 10, rampShape: c.ramp,
    band: c.band === 'ci' ? { type: 'brick', lo: 188, hi: 7938 } : { type: 'wide' },
    phase: 'random', startDb: 0, ...rule, ceiling: 'stop4',
    fms: [4, 8, 16, 32, 64, 128, 256], fmSets: [['옥타브 4–256', [4, 8, 16, 32, 64, 128, 256]], ['짧게', [8, 32, 128]]],
    reps: 2, extraIfDiff: 3, level: c.level, levelUnit: 'dBA', feedback: true, refs: [], rove: c.rove,
  };
}
