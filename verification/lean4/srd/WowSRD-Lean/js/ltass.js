// 말소리 장기 평균 스펙트럼(LTASS) — Won 2007 자극의 ‘long-term, speech-shaped filter (Byrne et al. 1994)’ 에 쓰는 값.
// 원문: Byrne et al. 1994 JASA 96(4):2108–2120 표 II (2116쪽) 의 ‘Combined’ 칸 — 저자들이 권하는 보편(universal) LTASS.
//   160 Hz 까지는 남성 값, 그 위는 남녀 평균 · 17 표본(아랍어 제외) 평균 · 전체 70 dB SPL 로 맞춘 1/3 옥타브 rms (입에서 20 cm, 45°).
// 옮긴 방법 (2026-10-21, 사용자가 준 PDF): 페이지 그림을 눈으로 읽어 이 파일에 적고, PDF 글자층(pypdf)에서 따로 뽑은 값과 맞대어
//   25행 × 4칸(주파수 · 남 · 여 · 합친)이 모두 같음. ‘합친 = 남성(≤ 160 Hz) / 남녀 평균(그 위)’ 이 모든 행에서 반올림 0.05 dB 안.
//   파이썬 기준(tools/srd_reference.py 의 BYRNE94)은 글자층에서 옮긴 것 — 고정 시험이 두 표를 칸마다 맞댐.
// 어느 칸을 쓰는지는 Won 2007 · 2011 에 없음 → 보편 LTASS(합친 칸)를 쓰는 것은 추론(DERIVED).
// 이 표가 바뀌면 절차 해시(config hash)가 바뀌어 앞의 측정과 섞이지 않음.
'use strict';

const LTASS = Object.freeze({
  status: 'verified',         // 'pending' (원문 대기) | 'verified' (원문 PDF 와 두 번 대조)
  source: 'Byrne D, Dillon H, Tran K, Arlinger S, Wilbraham K, Cox R, et al. (1994) An international comparison of long-term average speech spectra. J Acoust Soc Am 96(4):2108–2120 · 10.1121/1.410152',
  table: '표 II (2116쪽): Male, Female, and combined speech spectra, normalized for 70 dB SPL overall level and averaged across samples (excluding Arabic)',
  column: 'Combined — 보편 LTASS (≤ 160 Hz 남성, 그 위 남녀 평균). Byrne: “recommended as an appropriate universal spectrum for many, but not all, purposes”',
  unit: '1/3옥타브 띠 크기 dB SPL (상대값만 씀 — 전체 크기는 소리마다 RMS 로 다시 맞춤)',
  // [공칭 띠 중심 Hz, Combined dB] — 원문 표 그대로 25행
  bands: Object.freeze([[63, 38.6], [80, 43.5], [100, 54.4], [125, 57.7], [160, 56.8], [200, 60.2], [250, 60.3], [315, 59.0], [400, 62.1], [500, 62.1],
    [630, 60.5], [800, 56.8], [1000, 53.7], [1250, 53.0], [1600, 52.0], [2000, 48.7], [2500, 48.1], [3150, 46.8], [4000, 45.6], [5000, 44.5],
    [6300, 44.3], [8000, 43.7], [10000, 43.4], [12500, 41.3], [16000, 40.7]]),
  // 같은 표의 남성 · 여성 칸 (옮김 점검용 — 합친 칸 관계를 고정 시험이 확인)
  male: Object.freeze([38.6, 43.5, 54.4, 57.7, 56.8, 58.2, 59.7, 60.0, 62.4, 62.6, 60.6, 55.7, 53.1, 53.7, 52.3, 48.7, 48.9, 47.0, 46.0, 44.4, 43.3, 42.4, 41.9, 39.8, 40.4]),
  female: Object.freeze([37.0, 36.0, 37.5, 40.1, 53.4, 62.2, 60.9, 58.1, 61.7, 61.7, 60.4, 58.0, 54.3, 52.3, 51.7, 48.8, 47.3, 46.7, 45.3, 44.6, 45.2, 44.9, 45.0, 42.8, 41.1]),
  interpolation: '운반음 주파수에서 표의 공칭 띠 중심(63 · 80 · 100 · 125 …) 사이를 log2 주파수에 선형 · 표 밖은 끝 띠 값. 정확한 1/3 옥타브 중심(10^(n/10))과는 최대 0.95 % 차 → 운반음 이득으로 0.14 dB 안 (추론)',
  why_band_levels: '운반음이 로그 등간격이라 1/3옥타브 띠마다 운반음 수가 같음 → 운반음 이득(dB) = 그 주파수의 띠 크기로 두면 자극의 1/3옥타브 띠 크기가 LTASS 를 따름 (추론 — Won 2011 은 ‘CoolEdit 2000 으로 Byrne 1994 에 맞춘 필터’ 라고만 적음. 자극 분석이 띠마다 확인)',
  transcribed: Object.freeze({ by: 'Claude Opus 5.5', at: '2026-10-21', pdf: 'Desktop\\byrne1994.pdf (사용자가 줌, 스캔본 + 글자층)', pdfSha256: '4da7fe5634004b6596a9f21d2369b6d4730705064ff9c8e1b7cd250ef1f2c5e5',
    pages: 'PDF 9쪽 = 학술지 2116쪽 표 II', method: '페이지 그림을 눈으로 읽음 ↔ PDF 글자층에서 따로 뽑음: 25행 × 4칸 같음 · 합친 칸 관계 모든 행 0.05 dB 안' }),
});

// 주파수 f(Hz) 의 LTASS 이득(dB, 상대). 표가 비었으면 0 (필터 없음)
function ltassGainDb(f) {
  const b = LTASS.bands;
  if (!b || !b.length) return 0;
  if (f <= b[0][0]) return b[0][1];
  if (f >= b[b.length - 1][0]) return b[b.length - 1][1];
  const x = Math.log2(f);
  for (let j = 1; j < b.length; j++) {
    if (f <= b[j][0]) {
      const x0 = Math.log2(b[j - 1][0]), x1 = Math.log2(b[j][0]);
      return b[j - 1][1] + (b[j][1] - b[j - 1][1]) * (x - x0) / (x1 - x0);
    }
  }
  return b[b.length - 1][1];
}

if (typeof module !== 'undefined') module.exports = { LTASS, ltassGainDb };
