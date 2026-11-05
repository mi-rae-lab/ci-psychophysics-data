// 절차 설정 — 인공와우 정적 리플 변별(SRD, spectral-ripple discrimination).
//   won2007     : Won, Drennan & Rubinstein 2007 JARO 8:384 (10.1007/s10162-007-0085-8, PMC2538435) 적응 검사
//   drennan2014 : Drennan, Anderson, Won & Rubinstein 2014 Ear Hear 35:e92 (10.1097/AUD.0000000000000009, PMC3999174) 임상(항상자극법) 검사
// 값마다 근거 종류: WON(Won 2007 원문) · DRN(Drennan 2014 원문) · LAB(같은 연구실이 같은 절차를 다시 적은 논문: Won 2010·2011, Drennan 2010·2016, Jones 2013)
//   · REF(다른 논문) · DERIVED(식·계산·추론) · PROPOSED(이 프로그램이 정함) · PENDING(원문 PDF 대기) · DEVIATION(원문과 다름)
// 원문에 없는 값을 조용히 채우지 않는다 — LAB·REF·DERIVED·PROPOSED·PENDING 은 화면·기록에 그대로 드러낸다.
'use strict';

const APP_VERSION = '1.0.7 (2026-11-02)';

// 밀도 표 — Won 2007 원문 그대로(소수 셋째 자리, 0.125·√2^k 와 0.5 % 안 — 0.176 만 반올림 0.177 이 아님). 자극과 역치 모두 이 값을 씀 (DERIVED)
const DENS_MILLI = Object.freeze([125, 176, 250, 354, 500, 707, 1000, 1414, 2000, 2828, 4000, 5657, 8000, 11314]);
const rpoOf = k => DENS_MILLI[k] / 1000;
const rpoTxt = k => (DENS_MILLI[k] / 1000).toFixed(3);

const COMMON_STIM = Object.freeze({
  f_low_hz: 100, span_ratio: 50, spacing: 'f_i = 100·50^(i/N), i = 0…N−1 (로그 등간격, 양 끝: 100 Hz · 100·50^((N−1)/N) Hz)',
  envelope: 'dB 진폭 = D·|sin(π·R·F_i + θ)|, F_i = log2(f_i/100) (전파 정류 사인, dB 눈금)',
  depth_db: 30, theta_standard: 0, theta_inverted_offset: 'π/2',
  tone_phase: 'U[0,2π) — 소리마다 새로 (구간 씨앗 128비트 → xoshiro128** 에서 순서대로)',
  duration_s: 0.5, ramp_s: 0.15, ramp_shape: 'linear', steady_s: 0.2,
  speech_filter: 'Byrne 1994 LTASS — 운반음 이득 = 그 주파수의 1/3옥타브 띠 크기 (js/ltass.js)',
  level_dbfs: -25, level_rule: '소리마다 경사 전 0.5 s RMS = level_dbfs + 흔들기 (디지털 크기 — dB SPL 아님)',
  rove_db_min: -4, rove_db_max: 4, rove_rule: '소리(구간)마다 따로 −4…+4 dB 정수 균등 (9값)',
  sample_rate_hz: 44100, channels: 'mono → 출력 장치 모든 채널에 같은 신호',
});
const COMMON_TASK = Object.freeze({
  type: '3I3AFC', intervals: 3, isi_s: 0.5, lead_s: 0.5, response_after_s: 0.05, iti_s: 1.0,
  target_position: 'uniform_1_3', chance: 1 / 3, feedback: 'none',
  early_input_policy: 'ignored_and_logged', replay_policy: 'no_replay (기술적 실패 때만 새 시행으로 대체, 원 시행과 연결해 기록)',
  audio_clock_tolerance: 0.02,
});

const PROTOCOLS = Object.freeze({
  won2007: Object.freeze({
    id: 'won2007', protocol_id: 'SRD_WON2007_STREAM_v1', kind: 'adaptive',
    label: 'Won 2007 적응 검사', cite: 'Won, Drennan & Rubinstein 2007 JARO 8:384',
    spec: 'Won 2007 JARO 적응 SRD — 빠진 세부는 같은 연구실의 후속 논문(Won 2010·2011, Drennan 2010·2014·2016, Jones 2013)',
    validation_status: 'research_use_self_test',
    stimulus: Object.freeze({ ...COMMON_STIM, n_tones: 200, phase_mode: 'fixed', bandwidth_hz: '100–4903' }),
    task: COMMON_TASK,
    staircase: Object.freeze({
      version: 'won2007_2up1down_index_v1', unit: '밀도 칸 k (0 = 0.125 rpo … 13 = 11.314 rpo), 값은 DENS_MILLI',
      densities_milli: DENS_MILLI, start_index: 1, min_index: 0, max_index: 13,
      correct_required_for_harder: 2, incorrect_required_for_easier: 1, step_index: 1,
      total_reversals: 13, retained_reversals: 8,
      boundary_policy: 'blocked_zero_move_is_not_move_or_reversal (0.125 에서 더 성기게·11.314 에서 더 촘촘하게 = 막힌 이동)',
      max_valid_trials: 150, max_technical_failures: 10,
    }),
    session: Object.freeze({ tracks: 6, rule: 'six_mean', final: '결정된 track 6개가 모두 숫자일 때만 6개 산술 평균 = 회기 역치 (그 전은 잠정)' }),
    analysis: Object.freeze({
      version: 'srd_analysis_v1', threshold: 'mean_of_last_8_of_13_reversal_densities_rpo (산술 평균)', target_p: 'Math.SQRT1_2',
      exact: '반전 값은 milli-rpo 정수 → 역치 = 합 / (8 × 1000), 평균·비교는 BigInt 유리수',
      analysis_window: '남기지 않은 마지막 반전(5번째)의 다음 유효 시행부터 끝까지 — 응답으로 정해진 시점 다음부터',
      boundary_blocks_allowed_in_window: 0,
      numeric: '분석 구간에서 끝(0.125·11.314 rpo)에 막힌 이동이 없을 때만 반전 평균을 숫자 역치로 — 막히면 그 골·꼭짓점이 끝 값으로 잘려 평균이 치우침',
      easy_limited: '쉬운 끝(0.125)에 막혔으면 분석 구간 시행만으로: 0.125 정답률 < 더 촘촘한 밀도(한쪽 Fisher p < .05) → 신뢰성 부족(다시 하기) · 0.125 정답률 < 70.7 % 확인(한쪽 정확 이항 p < .05) → < 0.125 rpo · 그 밖 → 쉬운 끝에 막힘(숫자 없음)',
      hard_limited: '어려운 끝(11.314)에 막혔으면: 11.314 정답률 > 70.7 % 확인(한쪽 정확 이항 p < .05) → > 11.314 rpo · 그 밖 → 어려운 끝에 막힘(숫자 없음)',
      grouping: 'presentation_key (귀·유지 신호·처리기 프로그램 칸·경로 칸·처리기 기능·Windows 출력 장치/볼륨/음소거/소리 향상)',
      deviation_policy: 'audit_fail_to_protocol_deviation_exclude_from_mean_keep_raw',
      changelog: [],
    }),
  }),
  drennan2014: Object.freeze({
    id: 'drennan2014', protocol_id: 'SRD_DRENNAN2014_CLINICAL_STREAM_v1', kind: 'constant',
    label: 'Drennan 2014 임상 검사', cite: 'Drennan, Anderson, Won & Rubinstein 2014 Ear Hear 35:e92',
    spec: 'Drennan 2014 Ear Hear 임상 SRD (항상자극법) — 같은 자극 틀, 2555음 · 무늬 위상 무작위 · 12 밀도 × 6',
    validation_status: 'research_use_self_test',
    stimulus: Object.freeze({ ...COMMON_STIM, n_tones: 2555, phase_mode: 'random', bandwidth_hz: '100–4992' }),
    task: COMMON_TASK,
    constant: Object.freeze({
      version: 'drennan2014_mcs_v1', densities_index: Object.freeze([0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]), per_density: 6, total: 72,
      order: 'run 씨앗 RNG 로 Fisher–Yates (k 순서 [0×6, 1×6, …, 11×6] 을 뒤에서부터 섞음)',
      score: '72시행 정답률 p(c) — 심리측정 함수 아래 넓이 (Drennan 2014)',
      technical_policy: '기술적 실패 시행은 같은 밀도를 바로 다시 (원 시행과 연결해 기록)', max_technical_failures: 10,
    }),
    session: Object.freeze({ runs: 1, rule: 'clinical_pc' }),
    analysis: Object.freeze({
      version: 'srd_analysis_v1', score: 'p(c) = 정답 / 72 (정확한 유리수), 95 % Clopper–Pearson',
      chance_test: '한쪽 정확 이항 (p₀ = 1/3)', retest_reference: 'Drennan 2014: 같은 사람 두 번의 차이 > 8.4 % 이면 우연 밖 (스피커 · 집단 값 — 참고만)',
      grouping: 'presentation_key', deviation_policy: 'audit_fail_to_protocol_deviation_exclude_from_mean_keep_raw', changelog: [],
    }),
  }),
});
const protoOf = id => PROTOCOLS[id] || null;

// 회기마다 고르는 선택지 — 유지 신호는 소리 내용이 아니라 경로 선택이라 절차 해시에 넣지 않고 따로 기록
const OPTIONS = {
  keep: [['tone18', '18 Hz −45 dBFS 유지 신호 (다른 와우 검사 앱과 같음)'], ['zeros', '디지털 무음 반복'], ['off', '출력 멈춤 (경로 시험용)']],
};

// 회기 설계
const PLANS = [
  { id: 'won6', protocol: 'won2007', label: 'Won 2007 — 적응 track 6개', sub: '6개 평균 = 역치 · track 하나 약 5분 (Won 2011) · 6개 약 30분 (Jones 2013)', src: 'WON' },
  { id: 'clinical', protocol: 'drennan2014', label: 'Drennan 2014 — 임상 72시행', sub: '12 밀도 × 6번, 무작위 순서 · 정답률 p(c) · 검사 약 6분 + 안내', src: 'DRN' },
];
const planOf = id => PLANS.find(p => p.id === id) || null;

// 화면 표: [항목, 값, 근거 종류, 근거] — 공통 + 절차별
const ROWS_COMMON = [
  ['과제', '3구간 3선택(3I-3AFC): 두 구간은 같은 소리(표준), 한 구간은 무늬를 뒤집은 소리(뒤집힘). 다르게 들린 하나를 고름. 우연 = 1/3', 'WON',
    'Won 2007 “three-interval forced-choice” · Drennan 2014 “two standard and one inverted stimulus were presented”'],
  ['무늬', 'dB 진폭 = 30·|sin(π·R·F_i + θ)|, F_i = log2(f_i/100): 전파 정류 사인을 dB 눈금에, 봉우리–골 30 dB. R = 옥타브당 봉우리 수 (rpo)', 'WON',
    'Won 2007 “full-wave rectified sinusoidal envelope on a logarithmic amplitude scale” · “peak-to-valley ratio of 30 dB” · 식은 Won 2011 JASA 130:2088 식 (1)'],
  ['운반음 위상', '0–2π 균등, 소리(구간)마다 새로', 'WON', 'Won 2007 “The starting phases of the components were randomized for each presentation”'],
  ['길이', '0.5 s (경사 포함) = 앞 150 ms + 일정 200 ms + 뒤 150 ms', 'WON', 'Won 2007 “500 ms total duration … 150 ms rise/fall” · Drennan 2014 “a 200 ms steady-state portion”'],
  ['경사 모양', '선형', 'REF', 'Won 2007 · Henry 2005 는 ‘150 ms rise/fall’ 만 적음 → Iowa 원형 Henry & Turner 2003 “linear rise/fall times of 150-ms applied to each stimulus” (Won 2007 자극은 Henry 2005 를 바탕으로 함). 같은 연구실 TMTF 자극도 “10 ms linear ramps” (Won 2011 JASA 130:376)'],
  ['말소리 모양 필터', `Byrne 1994 의 말소리 장기 평균 스펙트럼(LTASS)으로 운반음 크기를 모양 지음 — 지금 상태: ${LTASS.status === 'verified' ? '원문 표 II 를 두 번 따로 옮겨 대조 끝' : '원문 대기 — 표 값 없음, 실제 회기 막힘'}`, LTASS.status === 'verified' ? 'WON' : 'PENDING',
    'Won 2007 “filtered with a long-term, speech-shaped filter (Byrne et al. 1994)” · Won 2011 JASA 130:2088 “created in CoolEdit 2000 with parameters specified in accordance with … Byrne” · Henry 2003 · 2005 도 같은 필터'],
  ['필터 값', '표 II 의 ‘Combined’ 칸(보편 LTASS: 160 Hz 까지 남성, 그 위 남녀 평균, 70 dB SPL 로 맞춘 1/3 옥타브) · 운반음 이득 = 공칭 띠 중심 사이 log 주파수 선형 → 띠 중심에서 표 값을 지나고, 1/3 옥타브 띠 평균은 표와 최대 0.58 dB 차(국소 봉우리 · 골이 매끄러워짐)', 'DERIVED',
    'Won 2007 · 2011 은 어느 칸 · 어떤 곡선인지 적지 않음. Byrne 1994 “recommended as an appropriate universal spectrum for many, but not all, purposes” — 공칭 중심(125 · 160 …)과 정확한 1/3 옥타브 중심의 차는 이득으로 0.14 dB 안'],
  ['크기', '소리마다 경사 전 0.5 s RMS 를 −25 dBFS 로 같게 (디지털 크기 — 처리기에 들어가는 dB SPL 이 아님)', 'PROPOSED',
    '원문: 스피커 1 m, 65 dBA (Won 2007) · 후속 61 dBA (Won 2010 · Drennan 2014) · 65 dBA rms (Drennan 2016). 크기를 잰 방법(소음계 등)은 네 논문 본문에 없음. Iowa 원형 Henry 2005 “The overall levels of the rippled noise sound files were then approximately equalized”'],
  ['크기 흔들기', '소리(구간)마다 따로 −4 … +4 dB, 1 dB 단위 (9값 균등)', 'LAB',
    'Won 2007 “roved within trials (8 dB range in 1 dB steps)” · Won 2010 “± 4-dB in 1-dB steps” · Drennan 2016 “+/− 4 dB in 1-dB steps” · Iowa 원형 Henry & Turner 2003 “varied randomly for each interval within an 8-dB range in 1-dB steps”. 다르게 적힌 곳: Won 2011 JASA 130:376 “7 dB range”, Jones 2013 “attenuation of 1–8 dB”, Henry 2005 “from trial to trial”'],
  ['구간 사이', '무음 500 ms (앞 소리 끝 → 다음 소리 시작)', 'LAB', 'Won 2007 에 없음 → Won 2011 JASA 130:2088 “The interstimulus interval (offset to onset) was 500 ms” (같은 절차라고 밝힘)'],
  ['다른 소리 자리', '1·2·3 균등 무작위 (시행마다)', 'LAB', 'Jones 2013 “The order of presentation of the three tokens was randomized”'],
  ['첫 소리 앞', '0.5 s', 'PROPOSED', '논문에 없음 (와우STM 과 같음)'],
  ['응답', '세 번째 소리가 끝나고 50 ms 뒤부터 1·2·3 (화면 단추 · 키보드 1 2 3). 그 전 입력은 무시하고 기록', 'WON',
    'Won 2007 “click on an on-screen button that was labeled 1, 2, and 3 after they were presented the stimuli” — 50 ms 는 PROPOSED'],
  ['구간 표시', '소리가 나는 동안 그 순서의 번호 단추(1 → 2 → 3)를 밝힘. 세 구간 모두 똑같이 밝혀 답의 단서는 아님', 'PROPOSED',
    '원문은 단추 1·2·3 만 적고 재생 중 화면 표시는 적지 않음 — 소리 사이 500 ms 를 화면으로도 나눠 볼 수 있게 함'],
  ['피드백', '없음 (맞았는지 알려 주지 않음)', 'WON', 'Won 2007 “Feedback was not provided.” · Drennan 2014 “No correct-response feedback”'],
  ['시행 사이', '응답 뒤 1.0 s 쉬고 다음 시행', 'PROPOSED', '논문에 없음'],
  ['안내 문구', '“두 개는 같고 하나만 다릅니다. 크기는 일부러 조금씩 바꾸니 크기 말고 소리 느낌이 다른 하나를 고르세요. 모르겠으면 하나를 고르세요.”', 'PROPOSED',
    'Won 2007 “discriminate the test stimulus from the reference stimuli” · Henry 2005 (Iowa) “ignoring any loudness variation between intervals” · Jeon 2015 (Iowa) “different … in terms of pitch or quality, rather than loudness”'],
  ['제시', '스트리밍(유선 → 스트리머 → 처리기) · 편한 크기 · 한쪽 귀씩 또는 양쪽', 'DEVIATION',
    '원문: 스피커 1 m, 평균 65 dBA, 자기 처리기를 편한 듣기 크기로 맞춤, 양쪽 사용자는 두 귀 함께 (Won 2007 “own speech processor set to a comfortable listening level”) · 편한 크기 + 임상 설정 그대로 (Won 2010) · 평소 쓰는 설정, 잡음 줄이기 프로그램 안 씀 (Drennan 2014). 처리기 마이크·방향성·AGC·잡음 줄이기의 입력 단계와 실제 크기가 다름 → 논문 값과 같은 척도로 비교·순위를 매길 근거 없음. 직결 선례: Henry & Turner 2003 (Iowa 원형, CI 는 “direct input into the speech processor”, 처리기 감도 고정) · Lopez Valdes 2014 (오디오 라인 입력, 마이크 볼륨 · 감도 최소, 0(무음)–10(너무 큼) 눈금의 6 = 가장 편한 크기)'],
  ['음성처리기', '참가자도 처리기 설정(코딩 전략 · 전류 · 자극 속도 · 펄스 폭 · T/C(M) · 자극 모드 · AGC · IDR · 스펙트럼 처리)을 모름 → 이 측정에서 인공와우는 블랙박스', 'DEVIATION',
    '결과는 ‘사람 + 소리 경로 + 음성처리기(설정 포함)’ 전체의 반응 — 역치가 크거나 작은 까닭을 사람 쪽과 처리기 쪽으로 나눌 수 없음. 직접 전기자극 연구와 같은 것을 재는 것이 아님'],
  ['장치 한계', '높은 밀도는 처리기 안에서 무늬가 일그러짐(aliasing): Cochlear 약 2 (2–2.5) · Advanced Bionics 약 2 · MED-EL 약 1.1 rpo 위 역치는 밀도 순서대로 놓이지 않음 — 결과에 표시하고 숫자는 남김', 'REF',
    'Winn & O’Brien 2022 Ear Hear 43:764 (10.1097/AUD.0000000000001162) “around 2 RPO, but device-specific” · 포화 3.46 · 2.02 · 1.26 rpo · “we recommend not grouping data … above and below the limit”'],
  ['표본률', '44.1 kHz 로 합성, 모노', 'PROPOSED', 'Winn 2016 의 리플 자극 44,100 Hz · 다른 와우 검사 앱과 같음'],
  ['출력 시계', '회기 시작 전 2 s, 시행마다 버퍼 재생 동안 오디오 시계/실제 시간이 1 ± 0.02 밖이면 시작 안 함·무효', 'PROPOSED', '와우STRIPES · 와우STM 과 같음 (가상 출력 장치가 꺼져 있으면 0.6 대)'],
  ['시행 사이 유지', '18 Hz −45 dBFS 유지 신호 (기본) / 디지털 무음 / 출력 멈춤', 'PROPOSED', '스트리머가 무음 뒤 마이크로 돌아가 앞부분을 자르는 것을 막기 위함 (와우 온셋 검사)'],
  ['기록 대조', '저장값 자료형·범위 → 시행만으로 처음부터 다시 계산(난수·계획·계단·점수) → 저장된 전이·최종 상태·결과와 비교 → 하나라도 다르면 절차 어긋남(숫자 없음, 원자료는 남김)', 'PROPOSED', '와우STM analysis_v4 와 같은 틀'],
  ['제시 설정 묶음', '귀 · 경로 · 볼륨 · 처리기 프로그램 · 처리기 기능 · Windows 출력(장치 · 볼륨 · 음소거 · 소리 향상)이 같은 측정끼리만 평균·비교. 측정마다 시작·끝에 Windows 오디오를 다시 읽음', 'PROPOSED', '설정 효과가 청취 능력·반복 오차와 섞이지 않게 (와우STM 과 같음)'],
];
const ROWS_BY = {
  won2007: [
    ['운반음', '순음 200개, f_i = 100·50^(i/200) (i = 0…199) → 100–4903 Hz, 로그 등간격', 'LAB',
      'Won 2007 “Two-hundred pure-tone frequency components” · “bandwidth of 100–5,000 Hz” → 식과 끝 값은 Won 2011 JASA 130:2088 식 (1) “100 − 4903 Hz” · Won 2010 “spaced equally on a logarithmic frequency scale”'],
    ['표준 · 뒤집힘', 'θ = 0 (표준) · π/2 (뒤집힘) — |sin| 의 주기가 π 라서 π/2 를 더하면 봉우리와 골이 바뀜', 'WON', 'Won 2007 “set to zero radians, and for inverted ripples, it was set to π / 2”'],
    ['밀도', '14가지: ' + DENS_MILLI.map(m => (m / 1000).toFixed(3)).join(' · ') + ' rpo (한 칸 ×√2). 원문 표의 소수 셋째 자리 값을 자극·역치 모두에 씀', 'WON',
      'Won 2007 “ratios of 1.414 (0.125, 0.176, … 11.314 ripples/octave)” — 원문 값을 그대로 쓰는 것은 DERIVED (정확한 0.125·√2^k 와 0.5 % 안. 가장 큰 차는 0.176: 0.125·√2 = 0.17678 의 반올림이면 0.177)'],
    ['계단', '2-up 1-down: 연달아 2번 맞히면 한 칸 촘촘하게(어렵게), 1번 틀리면 한 칸 성기게(쉽게) → 정답률 70.7 % 지점. 이동에 쓴 정답 2개는 다시 쓰지 않음', 'WON',
      'Won 2007 “two-up and one-down adaptive procedure, converging on 70.7% correct” · 이름의 뜻: Jones 2013 각주 1'],
    ['시작 · step', '0.176 rpo 에서 시작, 한 번에 한 칸 (×1.414)', 'WON', 'Won 2007 “started with 0.176 ripples per octave and moved in equal ratio steps of 1.414”'],
    ['범위', '0.125–11.314 rpo 안에서만. 0.125 에서 더 성기게 · 11.314 에서 더 촘촘하게 가라는 요청 = 막힌 이동 (이동도 반전도 아님)', 'LAB',
      'Jones 2013 “Ripple density was varied within the range 0.125–11.314” — 막힌 이동 처리는 PROPOSED (와우STM · STRIPES 와 같음)'],
    ['끝 · 역치', '반전 13번에서 끝. 마지막 8번 반전에서 제시한 밀도(rpo)의 산술 평균. 정확한 값 = 밀도 정수(milli-rpo) 합 / 8', 'WON',
      'Won 2007 “averaging the ripple spacing (the number of ripples/octave) for the final 8 of 13 reversals”'],
    ['반전 세기', '첫 실제 이동은 반전 아님 · 반전 값 = 그 시행에서 제시한 밀도 (방향이 바뀐 자리)', 'PROPOSED', '와우STM · STRIPES 와 같은 규칙'],
    ['회기', 'track 6개 (연습 track 은 고르면 앞에 하나 더, 평균에서 뺌). 회기 역치 = 6개 평균', 'WON',
      'Won 2007 “Subjects did at least six test runs … averaging the threshold from six runs” · Drennan 2014 · Jones 2013 · Won 2010 · Won 2011 JASA 130:376 도 6개 (Won 2011 JASA 130:2088 은 조건마다 3개)'],
    ['숫자 역치', '분석 구간(5번째 반전의 다음 시행부터 끝)에서 끝(0.125 · 11.314)에 막힌 이동이 한 번도 없는 track 만 숫자. 막히면 그 골(또는 꼭짓점)이 끝 값으로 잘려 반전 평균이 좋게(또는 나쁘게) 치우침', 'PROPOSED',
      '늘 찍는(1/3) 응답자도 이 계단에서 반전 평균이 나옴 — Won 은 이를 구분하지 않음. 비율·치우침은 tests.html 모의 측정 · 검증.md'],
    ['막힌 track 판정', '쉬운 끝(0.125)에 막힘: 분석 구간 시행만으로 0.125 정답률 < 더 촘촘한 밀도 정답률(한쪽 Fisher p < .05) → ‘신뢰성 부족’(다시 하기) · 0.125 정답률 < 70.7 % 확인(한쪽 정확 이항 p < .05) → ‘< 0.125 rpo’ · 그 밖 → ‘쉬운 끝에 막힘’. 어려운 끝(11.314)에 막힘: 11.314 정답률 > 70.7 % 확인 → ‘> 11.314 rpo’ · 그 밖 → ‘어려운 끝에 막힘’. 모두 숫자 없음', 'PROPOSED',
      '와우STM analysis_v3 의 천장 규칙과 같은 생각 (검증.md)'],
    ['상한', '유효 시행 150 (넘으면 ‘미완’) · 기술적 실패 10번이면 중단', 'PROPOSED', ''],
    ['확정 · 잠정', '결정된 track 6개가 모두 숫자일 때만 회기 역치 ‘확정’. 그 전은 ‘잠정’(괄호). 숫자와 숫자 아님(끝에 막힘 · 범위 밖)이 섞이면 평균을 내지 않음 (막힌 track 을 빼고 평균하면 좋은 쪽으로 고른 값)', 'PROPOSED', ''],
    ['다시 하기', '숫자도 범위 밖도 아닌 track(멈춤 · 기술적 실패 · 신뢰성 부족 · 절차 어긋남 · 다른 제시 설정 · 측정 중 설정 바뀜)은 회기 끝에 한 번 다시', 'PROPOSED', ''],
    ['예시', '측정마다 시작 전에 원하는 만큼 (0.176 rpo · 3번째가 다름 / 1번째가 다름 / 같은 소리 셋)', 'REF',
      'Won 2007 에 없음 → Winn 2016 “Before actual testing, subjects listened to the stimuli several times with the experimenter”'],
    ['연습 track', '고르면 회기 맨 앞에 하나 (똑같은 track, 평균에서 뺌). 기본은 없음', 'REF', 'Iowa 절차: Henry 2005 “four practice runs were completed for each subject” · Jeon 2015 “At least one practice run was completed before testing” · Won 2007 은 연습을 적지 않았고 6 track 사이 학습 없음 (1.75 → 1.76 rpo)'],
  ],
  drennan2014: [
    ['운반음', '순음 2555개, f_i = 100·50^(i/2555) (i = 0…2554) → 100–4992 Hz, 로그 등간격', 'DRN',
      'Drennan 2014 “summing 2555 random-phase pure tones … to minimize potential variations in the ripple spectrum at high ripple densities” — 주파수 식은 DERIVED (Won 2011 식의 꼴. Winn 2016 식 (1) 은 50·100^((i−1)/2555) 인데 본문은 “100 – 4991 Hz” 로 서로 맞지 않음)'],
    ['무늬 위상', '시행마다 θ = 2π·x (x 는 0–1 균등). 두 표준은 같은 θ, 뒤집힘 = θ + π/2', 'DRN',
      'Drennan 2014 “θ = x*(2π) radians, where x is a random number between 0 and 1; the phase of the corresponding inverted stimuli = θstand+(π/2)” — 가장자리 크기 단서를 막기 위함'],
    ['밀도', '12가지: ' + DENS_MILLI.slice(0, 12).map(m => (m / 1000).toFixed(3)).join(' · ') + ' rpo', 'DRN', 'Drennan 2014 “12, rather than 14, log-spaced values (0.125 … 5.657 rpo)”'],
    ['방법', '항상자극법: 밀도마다 6시행, 72시행을 무작위 순서로. 순서는 run 씨앗 난수로 Fisher–Yates', 'DRN',
      'Drennan 2014 “each ripple frequency represented on six trials that occurred in random order” — 섞는 방법은 PROPOSED'],
    ['점수', '72시행 정답률 p(c) (= 심리측정 함수 아래 넓이). 밀도별 정답률(6번씩)도 보임', 'DRN', 'Drennan 2014 “The p(c) across all ripple densities … representing a measure of the area under the psychometric function”'],
    ['피드백 · 연습', '없음. 예시 듣기를 쓰면 기록되고 ‘원문과 다름’ 표시 (점수는 남김)', 'DRN', 'Drennan 2014 “No correct-response feedback or training trials were provided.”'],
    ['기술적 실패', '그 시행은 채점하지 않고 같은 밀도를 바로 다시 (밀도마다 유효 6시행이 되게)', 'PROPOSED', ''],
    ['재검 참고', '다른 날 다시 (원문은 대개 1주 이상 사이). 두 번의 차이가 8.4 % 보다 크면 우연 밖 — 스피커 조건 집단 값이라 참고만', 'DRN',
      'Drennan 2014 “greater than 8.4%, the difference could be considered to be statistically significant” · Drennan 2016 표 8 repeatability 8.5 % (N 27)'],
  ],
};
const rowsOf = id => [...ROWS_COMMON.slice(0, 1), ...(ROWS_BY[id] || []), ...ROWS_COMMON.slice(1)];

// canonical JSON (키 정렬) → SHA-256 16진
function canonical(v) {
  if (v === null || typeof v !== 'object') return JSON.stringify(v);
  if (Array.isArray(v)) return '[' + v.map(canonical).join(',') + ']';
  return '{' + Object.keys(v).sort().map(k => JSON.stringify(k) + ':' + canonical(v[k])).join(',') + '}';
}
async function sha256Hex(data) {
  const buf = typeof data === 'string' ? new TextEncoder().encode(data) : data;
  const h = await crypto.subtle.digest('SHA-256', buf);
  return Array.from(new Uint8Array(h), b => b.toString(16).padStart(2, '0')).join('');
}
// 절차 + 말소리 필터 표(상태 포함) 해시. 표가 바뀌면 해시가 바뀌어 앞 측정과 섞이지 않음
const configHash = protoId => sha256Hex(canonical({ protocol: PROTOCOLS[protoId], ltass: LTASS, app: 'SRD' }));

if (typeof module !== 'undefined') module.exports = { APP_VERSION, DENS_MILLI, rpoOf, rpoTxt, PROTOCOLS, protoOf, OPTIONS, PLANS, planOf, ROWS_COMMON, ROWS_BY, rowsOf, canonical, sha256Hex, configHash };
