# 와우TMTF 검사 모델의 Lean 4 검증 보고서

2026년 11월 4일 · 와우TMTF 3.3.3 소스 · Lean 4.24.0 · Windows x86-64

**Lean이 증명한 대상은 검사 앱의 계단과 자극 계산을 옮겨 쓴 별도의 수학 모델이다.** 브라우저는 JavaScript의 `Track.respond`로 실제 응답을 처리하고 `Stim.make`로 자극 표본을 만든다. Lean에서는 참·거짓 응답열에 `runTrack`을 적용하고, 자극 수식의 성질을 주로 정확한 유리수로 계산한다. 앱과 모델의 연결은 같은 입력을 두 구현에서 실행해 확인했다.

| 확인 항목 | 이번 공개본에서 확인한 결과 | ZIP 안의 근거 |
|---|---|---|
| 클린 빌드 | 빈 빌드 디렉터리에서 `lake build` 종료 코드 0. 마지막 출력은 `Build completed successfully (27 jobs).` 경고·오류 출력 0건 | `verification/lake-build.txt` |
| 정리별 공리 | 원본에 명시한 123개 정리 전부에 실제 `#print axioms` 실행. 공리 의존성이 없는 정리는 22개 | `tools/lean/PrintAxioms.lean`, `verification/print-axioms.txt` |
| 생략된 증명 | 원본 Lean 파일 13개에서 주석과 문자열을 제외하고 `sorry`·`admit`·`sorryAx` 및 `axiom` 선언을 검색한 결과 0건. 보고할 소스 위치가 없다 | `verification/source-scan.txt` |
| 컴파일된 모델 | `TMTF.*` 선언 402개의 의존 공리를 추적. 프로젝트 공리 선언 0개, `sorryAx` 의존 0개, 표준 세 공리 밖의 의존 0개 | `verification/environment-audit.txt` |
| 앱과의 교차검증 | 고정 시드의 합성 입력 890개. 비교한 출력 1,174행이 모두 통과했으며, 그중 360행은 6가지 절차 설정의 계단 결과 | `verification/cross-check.txt` |

### 공리 출력 읽는 법

| 123개 명시적 정리의 의존 공리 | 정리 수 |
|---|---:|
| 없음 | 22 |
| `propext` | 9 |
| `propext`, `Quot.sound` | 14 |
| `propext`, `Classical.choice`, `Quot.sound` | 78 |

예를 들어 `uw_params`와 `dr_params`는 공리에 의존하지 않는다. `runTrack_done`은 `propext`와 `Quot.sound`에, `thr_bounds`는 세 공리 모두에 의존한다. 아래 부록에 정리별 결과가 있고, `print-axioms.txt`에는 Lean이 인쇄한 원문이 있다.

`MyAudit.lean`의 원문 요약은 `SUMMARY consts=402 theorems=293 axiomDecls=0 others=109`이다. 293은 컴파일러가 생성한 방정식 정리와 보조 증명 등을 포함한다. 이 감사의 대상은 빌드된 `TMTF.*` 모델 선언이고, 교차검증용 CLI와 감사 도구 코드는 소스 검색 범위에 포함했다. 감사 결과의 마지막 두 줄은 다음과 같다.

```text
UNION Classical.choice,Quot.sound,propext
NONSTANDARD 0
```

## 두 검사 절차의 설정

| 계단 설정 | UW (Won/Park) | De Ruiter |
|---|---|---|
| 시작 깊이 | 0 dB | −2 dB |
| 보폭 4 → 2 dB | 4번째 반전을 기록하는 이동부터 2 dB | 2번째 반전을 기록하는 이동부터 2 dB |
| 반전 목표 / 역치용 마지막 반전 | 14회 / 최대 10개 평균 | 8회 / 최대 6개 평균 |
| 0 dB 누적 오답 4회에서 조기 종료 | 끔 | 켬. 이 경우 기록값은 0 dB |
| 시행 상한 | 160회 | 160회 |

`uw_params`와 `dr_params`가 시작 깊이, 보폭, 전환 기준, 반전 목표, 평균 개수, 조기 종료 사용 여부와 시행 상한을 확인한다. 누적 오답 **4회**라는 조건은 `finish`의 정의에 있다. De Ruiter에서 이 조건으로 기록하는 0 dB는 반전 평균으로 추정한 역치와 구별된다. 반전이 부족해 평균을 낼 수 없는 상태는 모델에서 `none`으로 표현한다.

## 계단 규칙과 역치 판정

아래 정리 이름의 공통 접두사는 `TMTF.`이며 Lean 소스 위치는 `tools/lean/` 기준이다. `TMTF/Track.lean`의 `def`는 응답을 받아 다음 상태나 결과를 계산하는 규칙이다. `theorem`은 그 계산에 관해 Lean이 검사하는 명제다. 규칙이 모델에 쓰여 있다는 사실과 그 규칙으로부터 어떤 결론을 증명했는지를 구분했다.

| 검사 규칙 | 모델이 계산하는 내용 | 정리와 보장 범위 |
|---|---|---|
| 2-down 1-up | `afterAnswer`는 첫 정답에 깊이를 유지하고, 연속 두 번째 정답에 아래로 이동을 시도한다. 오답 한 번에 위로 이동을 시도한다. 이동 뒤 연속 정답 수는 0이 된다. 깊이 경계에서는 실제 변화가 0일 수 있다. | `afterAnswer_inv`, `respond_inv`, `runTrack_inv`는 이 규칙을 거친 상태의 깊이와 기록된 반전 깊이가 모두 [−40, 0] dB의 짝수임을 증명한다. 전제 `GoodP`는 시작 깊이가 범위 안의 짝수이고 두 보폭도 짝수라는 조건이다. `uw_good`, `dr_good`은 두 절차가 이를 만족함을 증명한다. |
| 70.7% 목표 | `levitt_target`이 다루는 수는 목표 정답률을 계산할 때 쓰는 `1/√2`다. | 실제 명제는 **0.7071² < 1/2 < 0.7072²**라는 유리수 부등식이다. 응답의 확률 모형도, 계단이나 사람의 수행이 그 값으로 수렴한다는 명제도 이 정리에 포함되지 않는다. |
| 단계 크기 변경 | `markRev`로 이번 반전을 먼저 기록한 뒤 `stepOf`가 누적 반전 수를 읽는다. UW는 4번째, De Ruiter는 2번째 반전을 **만드는 이동부터** 4 dB 대신 2 dB를 적용한다. | `uw_params`, `dr_params`가 각 보폭과 전환 기준을 증명한다. `stepOf_even`은 선택된 보폭의 짝수성을, `clampDb_ok`, `move_inv`는 경계를 적용한 뒤의 깊이 범위와 짝수성을 증명한다. |
| 반전 기록과 목표 횟수 | 첫 이동 뒤 이동 방향이 바뀌면 `markRev`가 이동 **전** 깊이와 시행 번호(0부터)를 추가한다. 경계에 막혀도 방향 기준은 같다. `finish`는 목표 반전 수에 도달하면 종료한다. | `markRev_inv`는 기록한 반전 깊이의 범위와 짝수성을 보존한다. `uw_params`, `dr_params`가 목표 횟수 14회, 8회를 확정한다. 어떤 응답열이든 이 횟수를 모두 달성한다고 증명한 것은 아니다. |
| 시행 수 상한 | `finish`는 천장 종료, 반전 수 종료, 시행 수 종료 순으로 검사한다. 마지막 조건으로 종료하면 `incomplete`를 설정한다. | `respond_len`은 진행 중인 상태가 한 번 응답하면 기록이 한 건 늘어남을, `respond_done`은 종료 후 상태가 그대로임을 증명한다. `runTrack_done`은 `0 < maxTrials ≤ 응답열 길이`이면 종료함을 증명한다. 두 절차의 `maxTrials`는 160이다. |
| 역치 계산 | `thrQ`는 천장 종료면 `some 0`, 그 밖에는 마지막 `avgLast`개까지의 반전 깊이를 취해 4개 미만이면 `none`, 4개 이상이면 정확한 유리수 산술평균을 돌려준다. UW는 마지막 10개, De Ruiter는 마지막 6개를 사용한다. | `uw_params`, `dr_params`가 평균 개수를 확정한다. `sumI_bounds`, `lastK_sub`, `thr_bounds`로, 상태가 `Inv`를 만족하고 수치 역치가 있으면 그 값은 [−40, 0] dB임을 증명한다. 역치의 짝수성은 주장하지 않는다. 앱의 소수 둘째 자리 반올림과 표준편차는 `thr_bounds`의 대상 밖이다. |
| 측정 불가와 0 dB 기록 | `tally`가 0 dB 시행의 오답을 **누적**한다. `drP.stop4 = true`이면 네 번째 오답에서 `finish`가 `ceiling = true`로 종료하고 `thrQ`는 0 dB를 돌려준다. `uwP.stop4 = false`이면 이 조기 종료를 쓰지 않는다. | `dr_params`, `uw_params`가 모드 값을 증명한다. 네 번 조건과 결과값 0은 `tally`, `finish`, `thrQ`의 분기 정의다. `tally_inv`, `finish_inv`는 깊이와 반전 값의 불변식을 보존한다. 천장 종료가 청취자의 탐지 불능을 뜻한다는 정리는 없다. |
| 0 dB의 우연 수준 판정 | `TMTF/Chance.lean`의 `atChanceQ`는 0 dB 시행이 6개 미만이면 `none`, 그 이상이면 이항 상측확률이 1/20을 **초과**하는지를 반환한다. | `cQ_small`은 조합 계수 세 값, `report_uw75_right`, `report_uw100_right`, `report_dr75_right`, `report_dr100_right`, `report_uw75_left2`, `report_uw100_left2`는 여섯 입력의 확률 구간 또는 정확한 값을 증명한다. `report_decisions`에서 7/7(2AFC)만 `some false`, 나머지 다섯은 `some true`다. |

**보조정리.** `init_inv`와 `foldl_inv`는 한 번의 응답에서 보존한 성질을 전체 응답열로 확장한다. `markRev_trials`, `move_trials`, `tally_trials`, `afterAnswer_trials`, `finish_trials`는 해당 단계에서 시행 목록이 유지됨을 증명한다. `finish_live`, `respond_live`, `foldl_done_stays`, `foldl_done`은 종료 후 상태와 남은 시행 수를 이용해 `runTrack_done`을 뒷받침한다.

**앱에서 대응하는 위치.** `js/protocols.js` 14–15, 36–37행이 두 절차의 설정을 제공한다. `js/track.js` 31–46행이 이동·반전·종료를, 48–63행이 이항 판정과 결과를 계산한다. `js/app.js` 724–751행에서 실제 사용자 입력을 정오로 채점한 뒤 `Track.respond`를 호출한다. Lean의 `runTrack`은 이 채점 뒤의 참·거짓 목록을 입력으로 받는다. `js/app.js` 824–831행은 천장 종료 때 0 dB 시행이 6회 미만이거나 우연 수준이면 ‘측정 불가’, 6회 이상이고 우연 수준보다 성적이 높으면 ‘역치가 100% 근처’로 표시한다. 천장 종료 없이 반전이 부족하면 ‘반전이 모자라 역치를 못 냄’으로 표시한다.

## 자극 수식과 보조 정리

정리 이름의 공통 접두사는 `TMTF.`이다. 아래 표에서 파일명은 ZIP의 `tools/lean/TMTF/` 아래 Lean 모듈을 가리킨다. 앱 파일명과 줄 번호는 대조한 원본의 위치이다. `m`은 변조 깊이, `s`는 사인 값을 대신하는 표본, `ms`는 구간의 평균제곱, `T`는 목표 평균제곱이다.

### 변조 포락선과 세기

| 모듈 · 정리 | 수식 또는 규칙 | Lean이 보장하는 범위 |
|---|---|---|
| Sam · `env_nonneg`, `env_le_two` | SAM 포락선 `1 + m·s` | `0 ≤ m ≤ 1`에서 `s ≥ −1`이면 포락선은 0 이상, `s ≤ 1`이면 2 이하이다. 앱은 `m = 10^(depthDb/20)`과 `Math.sin`을 계산해 잡음에 곱한다. 두 초월함수는 이 정리의 전제 밖에 있다. (`js/stim.js` 109–115행) |
| Sam · `sam_power` | 포락선의 제곱합 | `Σs = 0`과 `Σs² = n/2`이면 `Σ(1+m·s)² = n(1+m²/2)`이다. 임의의 노이즈 표본에 포락선을 곱했을 때의 실제 구간 전력은 별도 계산이 필요하다. |
| Sam · `sine4_moments`, `sine4_power`, `sine8_moments`, `sine12_moments` | 표로 준 사인 표본의 예 | 4점 표에서는 두 합과 포락선 제곱합을 계산한다. 8점·12점 표에서는 정수쌍으로 인코딩한 값의 모멘트 검사식이 참임을 보인다. 각 값이 런타임의 사인 계산과 일치한다는 정리는 없다. |
| Sam · `one_add_half_sq_pos`, `literal_power`, `literal_lt_one`, `literal_full`, `literal_small`, `db_three_halves` | 진폭을 `A = 1 + m²/2`로 나누는 보정식 | `A > 0`이고, 원래 전력비를 `A`로 두면 보정 후 `1/A`이다. `m ≠ 0`이면 1 미만, `m = 1`이면 2/3, `0 ≤ m ≤ 0.1`이면 부족분은 1/200 이하이다. 마지막 정리는 3/2 전력비의 1.76–1.77 dB에 해당하는 정수 거듭제곱 부등식이다. |
| Sam · `sqrt_gain_exact` | 이론적 제곱근 보정 | 유리수 이득 `g`가 `g² = 1/A`를 만족하면 `g²·A = 1`이다. 앱에서 실제로 사용하는 구간별 RMS 보정은 다음 행의 대상이다. |
| Level · `ms_scale`, `ms_equalized`, `equal_power`, `current_order` | 포락선 → 경사 → RMS 보정 | 상수 이득을 곱하면 평균제곱은 `g²`배이다. 경사까지 적용한 신호의 평균제곱이 0이 아니고 `g² = T/ms`이면 보정 후 평균제곱이 `T`이다. 두 비영 구간을 같은 목표로 맞추면 평균제곱이 같다. 앱 부동소수점의 반올림 오차, 서로 다른 목표 레벨, 무음일 때의 대체 분모는 이 결론에 포함되지 않는다. (`js/stim.js` 69, 116–127행) |
| Level · `old_order_power`, `old_order_can_differ` | 경사 전에 RMS를 맞추는 순서 | 최종 평균제곱은 `g²·ms(r·x)`이다. 4표본 반례에서 경사 전에는 두 신호 모두 4였던 평균제곱이 경사 후 5/2와 1로 갈린다. |
| Level · `guard_changes_power` | 피크 제한 후의 세기 | 목표 `T ≠ 0`인 구간에 추가 이득 `s`를 곱하고 `s² ≠ 1`이면 평균제곱은 `T`와 달라진다. 앱에서는 피크가 0.99를 넘을 때 이 경로에 들어간다. (`js/stim.js` 128–133행) |

### 직선 경사와 대역 응답

| 모듈 · 정리 | 수식 또는 규칙 | Lean이 보장하는 범위 |
|---|---|---|
| Ramp · `two_R_pos`, `ramp_pos`, `ramp_lt_one`, `ramp_mono`, `ramp_symm` | 선형 경사 `aᵢ = (i + 0.5)/R` | 양의 경사 길이와 유효한 인덱스에서 `0 < aᵢ < 1`, 엄격한 증가, `aᵢ + a_(R−1−i) = 1`을 증명한다. 사용자 설정에 있는 `cos2` 경사는 별도 식이다. (`js/stim.js` 120–125행) |
| Ramp · `rampLen_half`, `ramp_ends_disjoint`, `rampW_pos`, `rampW_le_one`, `rampW_symm` | 양 끝 경사와 전체 창 | `2R ≤ N`이며 양 끝의 경사 표본이 겹치지 않는다. 모델의 유효한 창에서 양의 길이인 경사 이득은 양수이며, 전체 창의 값은 1 이하이고 앞뒤 대칭이다. |
| Ramp · `rampLen_values` | 지정 프로토콜의 경사 길이 | 10·30 ms가 각각 48 kHz에서 480·1,440표본, 44.1 kHz에서 441·1,323표본이다. |
| Band · `sq_nonneg`, `p4_nonneg`, `sq_mono`, `p4_mono`, `div_anti`, `div_mono`, `den_ge_one` | 필터 부등식의 보조 정리 | 제곱과 네제곱이 0 이상이라는 성질과 음이 아닌 구간에서의 단조성, 양수 분모에 관한 나눗셈 부등식, 대역 응답 분모의 하한 1을 증명한다. |
| Band · `G2_pos`, `G2_le_one`, `G2_at_80`, `G2_at_8500`, `G2_octave_out` | 80–8,500 Hz 대역의 제곱 이득 `G2 = 1/[(1+(80/f)⁴)(1+(f/8500)⁴)]` | `0 < G2 ≤ 1`이다. 80·8,500 Hz에서는 `0.49999 < G2 ≤ 0.5`, 40·17,000 Hz에서는 `G2 ≤ 1/17`이다. 앱의 대역통과 분기는 양의 FFT 주파수 칸에서 이 크기 응답을 사용한다. (`js/stim.js` 75–95행, `js/protocols.js` 32–35행) |
| Band · `G2_lower`, `G2_pass_200_2000`, `G2_pass_2000_5000` | 통과대역 전력 이득 하한 | `0 < a ≤ f ≤ b`에서 분모의 두 항을 각각 `80/a`, `b/8500`로 계산한 하한을 얻는다. 200–2,000 Hz에서는 0.97 이상, 2,000–5,000 Hz에서는 0.89 이상이다. 하드웨어 주파수 응답이나 완성된 잡음 표본의 FFT 측정값은 이 정리의 대상 밖이다. |

### 기대 스펙트럼과 봉우리

모델은 `x = m²`로 해석하고 `modSpec = [S(f) + x·(S(f−fm) + S(f+fm))/4] / (1+x/2)`를 정의로 채택한다. 아래는 이 식에 관한 대수적 결과이다. 실제 가우스 잡음의 확률 과정이나 자극 배열에서 이 식을 도출하는 증명은 없다. 앱에서 관련 파형은 `js/stim.js` 75–115행이 만든다.

| 모듈 · 정리 | 수식 또는 규칙 | Lean이 보장하는 범위 |
|---|---|---|
| Spectrum · `half_pos`, `wide_flat`, `wide_strip` | 광대역 옆띠 | 음이 아닌 `x`에서 분모가 양수이다. 중심과 양옆의 세 스펙트럼 값이 모두 1이면 변조 후에도 1이다. 세 값이 중심 1, 아래 옆띠 0, 위 옆띠 1이면 비율은 `(1+x/4)/(1+x/2)`이다. |
| Spectrum · `strip_ge`, `strip_small_m`, `strip_db` | 가장자리 전력비 | 이 비율은 `0 ≤ x ≤ 1`에서 5/6 이상, `0 ≤ x ≤ 1/10`에서 41/42 이상이다. 5/6에 대응하는 −0.80 ~ −0.79 dB 범위를 정수 거듭제곱 부등식으로 확인한다. |
| Spectrum · `crest_m1`, `crest_m1_db`, `crest_m316` | 포락선 봉우리 전력비 `(1+m)²/(1+m²/2)` | `m = 1`일 때 8/3이고 해당 dB 범위는 4.25–4.26이다. `m = 0.316`에서는 1.64보다 크고 1.66보다 작다. 개별 소리의 실제 최대 디지털 표본값과는 구분된다. |

### 기타 검사 설정, 우연 수준 및 공통 보조 정리

| 모듈 · 정리 | 대응 항목 | Lean이 보장하는 범위 |
|---|---|---|
| Grid · `fine_length`, `fine_mem_iff`, `fine_sorted` | 변조 주파수 격자 | 5–300 Hz의 5 Hz 배수 60개가 엄격한 오름차순이다. 앱은 직접 설정 시 이 격자에 추가 주파수를 합친다. (`js/protocols.js` 55–66행) |
| Grid · `papers_in_fine`, `off_paper_counts` | 프로토콜 주파수 | Won·De Ruiter 목록은 격자의 부분집합이고 Park 목록은 Won의 부분집합이다. Won 및 De Ruiter 목록 밖 격자점은 각각 53개이다. |
| Grid · `interval_samples`, `interval_exact`, `cycles_min` | 자극 길이·변조 주기 | 44.1·48 kHz에서 1·0.5·0.8초의 반올림 표본 수, 1·0.5초의 역산 길이, 격자에서 0.5초당 최소 2.5주기와 1초당 최소 5주기를 증명한다. 재생 스케줄 정확도는 이 산술 범위 밖이다. (`js/stim.js` 107행) |
| Grid · `countMod2_succ`, `countMod2_closed`, `countMod3_succ`, `countMod3_closed`, `target_counts`, `target_bias3` | 정답 구간 선택 | 32비트 전체 입력 중 2구간은 각 2³¹개, 3구간은 0번이 1,431,655,766개, 나머지 각 1,431,655,765개이다. 입력이 균등할 때 0번 확률은 균등값보다 `2/(3·2³²)`만큼 크다. 브라우저 난수의 균등성 또는 예외 시 대체 경로의 분포를 증명한 것은 아니다. (`js/app.js` 457, 677행) |
| Rng · `gamma_eq`, `gamma_coprime`, `state_formula`, `state_injective`, `uniform_range` | 자극 잡음의 32비트 난수 상태 | 증가량 1,831,565,813은 2³²과 서로소다. `k`번 후 상태는 `(seed + k·γ) mod 2³²`이고 처음 2³²개 상태에는 중복이 없다. 출력 단어를 2³²로 나눈 값은 [0,1)에 있다. 상태 비반복은 혼합 출력의 비반복이나 Box–Muller 출력의 정규성을 보장하지 않는다. (`js/stim.js` 47–63행) |
| Chance · `cQ_small` | 우연 수준 판정 보조식 | 조합 계수의 곱셈식을 세 입력에서 정확히 계산한다. (`js/track.js` 8–15행) |
| Chance · `report_uw75_right`, `report_uw100_right`, `report_dr75_right`, `report_dr100_right`, `report_uw75_left2`, `report_uw100_left2` | 0 dB 시행의 단측 이항 꼬리 | 모델에서 28/46, 18/28, 5/11, 6/12, 7/7, 24/41의 꼬리확률을 계산한다. 앞의 두 사례 및 뒤의 두 사례는 2AFC, 나머지 두 사례는 3AFC이다. 7/7의 꼬리확률은 1/128이다. |
| Chance · `report_decisions` | 우연 수준 표시 | `atChanceQ`는 0 dB 시행이 6회 미만이면 판정을 보류하고, 그 외에는 단측 꼬리확률이 0.05보다 큰지를 판정한다. 위 여섯 입력에서 7/7만 거짓이고 나머지는 참이다. 모든 시행 기록에서 JS 판정과 같다는 정리는 없다. 0 dB 오답 누적으로 중지하고 역치를 기록하는 `stop4`와는 별도이다. (`js/track.js` 42–60행) |
| Basic · `sumQ_zero`, `sumQ_succ`, `sumQ_congr`, `sumQ_add`, `sumQ_mul_left`, `sumQ_const` | 평균제곱·포락선 계산의 기초 | 유한합의 초기값과 한 항 추가, 표본별 동등성, 덧셈 분리, 상수배 및 상수의 합을 증명한다. |
| Basic · `le_div_of_pos`, `div_le_of_pos`, `lt_le_trans` | 수식 경계의 보조 정리 | 유리수의 양수 분모를 곱셈 쪽으로 옮기는 비교식과 엄격·비엄격 부등식의 추이성을 제공한다. |

## 앱과 모델을 연결한 실행 검사

| 경로 | 실제로 실행되는 코드 | 검증의 성격 |
|---|---|---|
| 브라우저 검사 | 원본 `index.html`이 JS를 로드한다. `js/app.js` 438행에서 `Stim.make`, 659행에서 `new Track`, 748행에서 `respond`를 사용한다. 352–362행은 Web Audio 재생 경로다. | 검사 앱은 JavaScript와 브라우저 오디오 엔진에서 동작한다. |
| Lean 모델 | `TMTF/Track.lean`이 계단 상태 전이를 정의한다. `Sam`, `Level`, `Ramp`, `Band`, `Spectrum` 등이 자극 수식을 정의한다. | 각 정리의 가정이 성립하는 모델 입력 전체에 대해 해당 결론이 성립한다. |
| 구현 사이의 대조 | `tools/lean/cross_check.js`가 원본과 동일한 `js/protocols.js`, `js/stim.js`, `js/track.js`를 로드한다. `CrossCheck.lean`으로 빌드한 CLI는 모델 출력과 비교용 계산을 직렬화한다. | 두 프로그램에 같은 합성 입력을 주고 기록, 판정, 수치를 비교한다. 모든 입력에서의 동등성을 증명하는 정리는 없다. |

계단 대조에서는 종료·천장·미완료 플래그, 깊이, 연속 정답 수, 방향, 0 dB에서의 시행·정답·오답 수, 반전 깊이와 시행 번호, 제시 깊이 목록, 역치, 우연 판정을 비교했다. 다른 입력은 난수, 경사, 대역, 표본 수와 주파수 선택을 다룬다. 이항 꼬리확률(`PV`)과 대역 제곱 이득비(`GAIN`)는 상대 오차로 비교했다. 최대 상대 차이는 각각 8.55×10⁻¹⁶(허용 10⁻⁹)과 8.42×10⁻⁷(허용 2×10⁻⁵)였다. 12종의 출력에서 한 줄씩 일부러 바꾼 검사도 모두 차이를 검출했다.

Lean 증명의 경계는 모델 정의에서 끝난다. 실제 `Math.sin`, FFT, Box–Muller 잡음 생성, 부동소수점 표본 반올림, 브라우저 재생 시간과 장치 출력 음압은 정리의 결론에 포함되지 않는다. 계단의 종료나 역치 범위에 관한 정리로 청취자의 탐지 능력 또는 검사의 임상적 타당성이 입증되지는 않는다.

## 부록 · 123개 정리별 명제와 공리

각 행은 원본 소스의 명시적 정리 한 개다. **명제** 열은 정리 이름 뒤의 인자, 가정, 결론을 원문에서 가져와 줄바꿈만 정리했다. **공리** 열은 같은 정리에 대한 실제 `#print axioms` 결과다. 파일은 `tools/lean/TMTF/` 아래에 있고, 줄 번호는 1부터 센다.

### Track.lean · 31개

| 정리 · 줄 | 검사 규칙 또는 수식 | 명제 | 공리 |
|---|---|---|---|
| `uw_good` · 115 | 절차 매개변수와 깊이 불변식의 전제 | `: GoodP uwP` | 없음 |
| `dr_good` · 116 | 절차 매개변수와 깊이 불변식의 전제 | `: GoodP drP` | 없음 |
| `clampDb_ok` · 118 | 단계 크기·깊이 제한 | `{x : Int} (h : x % 2 = 0) : -40 ≤ clampDb x ∧ clampDb x ≤ 0 ∧ clampDb x % 2 = 0` | `propext`, `Classical.choice`, `Quot.sound` |
| `markRev_inv` · 121 | 반전 기록 | `{S : TrackS} {d : Int} (h : Inv S) : Inv (markRev S d)` | `propext` |
| `stepOf_even` · 132 | 단계 크기·깊이 제한 | `{P : TrackP} (hP : GoodP P) (S : TrackS) : stepOf P S % 2 = 0` | 없음 |
| `move_inv` · 137 | 단계 크기·깊이 제한 | `{P : TrackP} (hP : GoodP P) {S : TrackS} {d : Int} (hd : d = 1 ∨ d = -1) (h : Inv S) : Inv (move P S d)` | `propext`, `Classical.choice`, `Quot.sound` |
| `tally_inv` · 145 | 0 dB 누적 오답 집계 | `{S : TrackS} {c : Bool} (h : Inv S) : Inv (tally S c)` | 없음 |
| `afterAnswer_inv` · 152 | 2-down 1-up 응답과 전체 계단의 깊이 | `{P : TrackP} (hP : GoodP P) {S : TrackS} {c : Bool} (h : Inv S) : Inv (afterAnswer P S c)` | `propext`, `Classical.choice`, `Quot.sound` |
| `finish_inv` · 159 | 종료 규칙의 불변식 | `{P : TrackP} {S : TrackS} (h : Inv S) : Inv (finish P S)` | 없음 |
| `respond_inv` · 168 | 2-down 1-up 응답과 전체 계단의 깊이 | `{P : TrackP} (hP : GoodP P) {S : TrackS} {c : Bool} (h : Inv S) : Inv (respond P S c)` | `propext`, `Classical.choice`, `Quot.sound` |
| `foldl_inv` · 173 | 응답열에 대한 불변식의 귀납 | `{α β : Type} (f : β → α → β) (I : β → Prop) (hf : ∀ b a, I b → I (f b a)) : ∀ (l : List α) (b : β), I b → I (l.foldl f b)` | 없음 |
| `init_inv` · 180 | 2-down 1-up 응답과 전체 계단의 깊이 | `{P : TrackP} (hP : GoodP P) : Inv (TrackS.init P)` | `propext` |
| `runTrack_inv` · 184 | 2-down 1-up 응답과 전체 계단의 깊이 | `{P : TrackP} (hP : GoodP P) (cs : List Bool) : Inv (runTrack P cs)` | `propext`, `Classical.choice`, `Quot.sound` |
| `markRev_trials` · 189 | 반전 기록 | `(S : TrackS) (d : Int) : (markRev S d).trials = S.trials` | 없음 |
| `move_trials` · 192 | 이동·응답 처리·종료 시 시행 기록 | `(P : TrackP) (S : TrackS) (d : Int) : (move P S d).trials = S.trials` | 없음 |
| `tally_trials` · 195 | 0 dB 누적 오답 집계 | `(S : TrackS) (c : Bool) : (tally S c).trials = S.trials` | 없음 |
| `afterAnswer_trials` · 200 | 이동·응답 처리·종료 시 시행 기록 | `(P : TrackP) (S : TrackS) (c : Bool) : (afterAnswer P S c).trials = S.trials` | 없음 |
| `finish_trials` · 207 | 이동·응답 처리·종료 시 시행 기록 | `(P : TrackP) (S : TrackS) : (finish P S).trials = S.trials` | 없음 |
| `respond_len` · 215 | 이동·응답 처리·종료 시 시행 기록 | `{P : TrackP} {S : TrackS} {c : Bool} (h : S.done = false) : (respond P S c).trials.length = S.trials.length + 1` | `propext` |
| `finish_live` · 224 | 시행 수 상한과 종료 | `(P : TrackP) (S : TrackS) : Live P (finish P S)` | `propext`, `Quot.sound` |
| `respond_live` · 233 | 시행 수 상한과 종료 | `(P : TrackP) (S : TrackS) (c : Bool) (h : Live P S) : Live P (respond P S c)` | `propext`, `Quot.sound` |
| `respond_done` · 238 | 시행 수 상한과 종료 | `{P : TrackP} {S : TrackS} {c : Bool} (h : S.done = true) : respond P S c = S` | `propext` |
| `foldl_done_stays` · 241 | 시행 수 상한과 종료 | `(P : TrackP) : ∀ (cs : List Bool) (S : TrackS), S.done = true → (cs.foldl (respond P) S).done = true` | `propext` |
| `foldl_done` · 247 | 시행 수 상한과 종료 | `(P : TrackP) : ∀ (cs : List Bool) (S : TrackS), Live P S → (S.done = true ∨ P.maxTrials ≤ S.trials.length + cs.length) → (cs.foldl (respond P) S).done = true` | `propext`, `Quot.sound` |
| `runTrack_done` · 274 | 시행 수 상한과 종료 | `(P : TrackP) (hm : 0 < P.maxTrials) (cs : List Bool) (h : P.maxTrials ≤ cs.length) : (runTrack P cs).done = true` | `propext`, `Quot.sound` |
| `sumI_bounds` · 282 | 마지막 반전 평균과 역치 범위 | `: ∀ (l : List Int), (∀ r ∈ l, -40 ≤ r ∧ r ≤ 0) → -40 * (l.length : Int) ≤ sumI l ∧ sumI l ≤ 0` | `propext`, `Quot.sound` |
| `lastK_sub` · 293 | 마지막 반전 평균과 역치 범위 | `(k : Nat) (l : List Int) : ∀ r ∈ lastK k l, r ∈ l` | `propext` |
| `thr_bounds` · 297 | 마지막 반전 평균과 역치 범위 | `{P : TrackP} {S : TrackS} (h : Inv S) {q : Rat} (hq : thrQ P S = some q) : -40 ≤ q ∧ q ≤ 0` | `propext`, `Classical.choice`, `Quot.sound` |
| `levitt_target` · 323 | 2-down 1-up 목표값의 수치 경계 | `: (7071 / 10000 : Rat) * (7071 / 10000) < 1 / 2 ∧ 1 / 2 < (7072 / 10000 : Rat) * (7072 / 10000)` | `propext`, `Classical.choice`, `Quot.sound` |
| `uw_params` · 326 | 시작 깊이·보폭·반전 목표·역치용 반전 수·천장 종료·시행 상한 | `: uwP.startDb = 0 ∧ uwP.big = 4 ∧ uwP.small = 2 ∧ uwP.bigUntil = 4 ∧ uwP.totalRev = 14 ∧ uwP.avgLast = 10 ∧ uwP.stop4 = false ∧ uwP.maxTrials = 160` | 없음 |
| `dr_params` · 329 | 시작 깊이·보폭·반전 목표·역치용 반전 수·천장 종료·시행 상한 | `: drP.startDb = -2 ∧ drP.big = 4 ∧ drP.small = 2 ∧ drP.bigUntil = 2 ∧ drP.totalRev = 8 ∧ drP.avgLast = 6 ∧ drP.stop4 = true ∧ drP.maxTrials = 160` | 없음 |

### Chance.lean · 8개

| 정리 · 줄 | 검사 규칙 또는 수식 | 명제 | 공리 |
|---|---|---|---|
| `cQ_small` · 30 | 우연 수준 판정 보조식 | `: cQ 5 2 = 10 ∧ cQ 10 3 = 120 ∧ cQ 46 23 = 8233430727600` | `propext`, `Classical.choice`, `Quot.sound` |
| `report_uw75_right` · 32 | 0 dB 시행의 단측 이항 꼬리 | `: 919 / 10000 < tailQ 28 46 (1 / 2) ∧ tailQ 28 46 (1 / 2) < 920 / 10000` | `propext`, `Classical.choice`, `Quot.sound` |
| `report_uw100_right` · 33 | 0 dB 시행의 단측 이항 꼬리 | `: 924 / 10000 < tailQ 18 28 (1 / 2) ∧ tailQ 18 28 (1 / 2) < 925 / 10000` | `propext`, `Classical.choice`, `Quot.sound` |
| `report_dr75_right` · 34 | 0 dB 시행의 단측 이항 꼬리 | `: 2889 / 10000 < tailQ 5 11 (1 / 3) ∧ tailQ 5 11 (1 / 3) < 2890 / 10000` | `propext`, `Classical.choice`, `Quot.sound` |
| `report_dr100_right` · 35 | 0 dB 시행의 단측 이항 꼬리 | `: 1777 / 10000 < tailQ 6 12 (1 / 3) ∧ tailQ 6 12 (1 / 3) < 1778 / 10000` | `propext`, `Classical.choice`, `Quot.sound` |
| `report_uw75_left2` · 36 | 0 dB 시행의 단측 이항 꼬리 | `: tailQ 7 7 (1 / 2) = 1 / 128` | `propext`, `Classical.choice`, `Quot.sound` |
| `report_uw100_left2` · 37 | 0 dB 시행의 단측 이항 꼬리 | `: 1744 / 10000 < tailQ 24 41 (1 / 2) ∧ tailQ 24 41 (1 / 2) < 1745 / 10000` | `propext`, `Classical.choice`, `Quot.sound` |
| `report_decisions` · 40 | 우연 수준 표시 | `: atChanceQ 28 46 2 = some true ∧ atChanceQ 18 28 2 = some true ∧ atChanceQ 5 11 3 = some true ∧ atChanceQ 6 12 3 = some true ∧ atChanceQ 7 7 2 = some false ∧ atChanceQ 24 41 2 = some true` | `propext`, `Classical.choice`, `Quot.sound` |

### Sam.lean · 14개

| 정리 · 줄 | 검사 규칙 또는 수식 | 명제 | 공리 |
|---|---|---|---|
| `env_nonneg` · 27 | SAM 포락선 `1 + m·s` | `{m s : Rat} (hm0 : 0 ≤ m) (hm1 : m ≤ 1) (hs0 : -1 ≤ s) : 0 ≤ env m s` | `propext`, `Classical.choice`, `Quot.sound` |
| `env_le_two` · 38 | SAM 포락선 `1 + m·s` | `{m s : Rat} (hm0 : 0 ≤ m) (hm1 : m ≤ 1) (hs1 : s ≤ 1) : env m s ≤ 2` | `propext`, `Classical.choice`, `Quot.sound` |
| `sam_power` · 48 | 포락선의 제곱합 | `{s : Nat → Rat} {n : Nat} (m : Rat) (h1 : sumQ s n = 0) (h2 : sumQ (fun i => s i * s i) n = n / 2) : sumQ (fun i => env m (s i) * env m (s i)) n = n * (1 + m * m / 2)` | `propext`, `Classical.choice`, `Quot.sound` |
| `sine4_moments` · 58 | 표로 준 사인 표본의 예 | `: sumQ sine4 4 = 0 ∧ sumQ (fun i => sine4 i * sine4 i) 4 = (4 : Nat) / 2` | `propext`, `Classical.choice`, `Quot.sound` |
| `sine4_power` · 61 | 표로 준 사인 표본의 예 | `(m : Rat) : sumQ (fun i => env m (sine4 i) * env m (sine4 i)) 4 = (4 : Nat) * (1 + m * m / 2)` | `propext`, `Classical.choice`, `Quot.sound` |
| `sine8_moments` · 75 | 표로 준 사인 표본의 예 | `: momentsOK sine8x2 2 8 = true` | 없음 |
| `sine12_moments` · 76 | 표로 준 사인 표본의 예 | `: momentsOK sine12x2 3 12 = true` | 없음 |
| `one_add_half_sq_pos` · 80 | 진폭을 `A = 1 + m²/2`로 나누는 보정식 | `(m : Rat) : 0 < 1 + m * m / 2` | `propext`, `Classical.choice`, `Quot.sound` |
| `literal_power` · 91 | 진폭을 `A = 1 + m²/2`로 나누는 보정식 | `(m : Rat) : (1 + m * m / 2) * (1 / (1 + m * m / 2)) * (1 / (1 + m * m / 2)) = 1 / (1 + m * m / 2)` | `propext`, `Classical.choice`, `Quot.sound` |
| `literal_lt_one` · 98 | 진폭을 `A = 1 + m²/2`로 나누는 보정식 | `{m : Rat} (hm : m ≠ 0) : 1 / (1 + m * m / 2) < 1` | `propext`, `Classical.choice`, `Quot.sound` |
| `literal_full` · 112 | 진폭을 `A = 1 + m²/2`로 나누는 보정식 | `: (1 : Rat) / (1 + 1 * 1 / 2) = 2 / 3` | `propext`, `Classical.choice`, `Quot.sound` |
| `literal_small` · 115 | 진폭을 `A = 1 + m²/2`로 나누는 보정식 | `{m : Rat} (h0 : 0 ≤ m) (h1 : m ≤ 1 / 10) : 1 - 1 / (1 + m * m / 2) ≤ 1 / 200` | `propext`, `Classical.choice`, `Quot.sound` |
| `sqrt_gain_exact` · 139 | 이론적 제곱근 보정 | `{m g : Rat} (hg : g * g = 1 / (1 + m * m / 2)) : g * g * (1 + m * m / 2) = 1` | `propext`, `Classical.choice`, `Quot.sound` |
| `db_three_halves` · 145 | 진폭을 `A = 1 + m²/2`로 나누는 보정식 | `: 2 ^ 1000 * 10 ^ 176 < 3 ^ 1000 ∧ 3 ^ 1000 < 2 ^ 1000 * 10 ^ 177` | 없음 |

### Level.lean · 7개

| 정리 · 줄 | 검사 규칙 또는 수식 | 명제 | 공리 |
|---|---|---|---|
| `ms_scale` · 23 | 포락선 → 경사 → RMS 보정 | `(c : Rat) (x : Nat → Rat) (n : Nat) : ms (scale c x) n = c * c * ms x n` | `propext`, `Classical.choice`, `Quot.sound` |
| `ms_equalized` · 31 | 포락선 → 경사 → RMS 보정 | `{x : Nat → Rat} {n : Nat} {g T : Rat} (hx : ms x n ≠ 0) (hg : g * g = T / ms x n) : ms (scale g x) n = T` | `propext`, `Classical.choice`, `Quot.sound` |
| `equal_power` · 36 | 포락선 → 경사 → RMS 보정 | `{a b : Nat → Rat} {na nb : Nat} {ga gb T : Rat} (ha : ms a na ≠ 0) (hb : ms b nb ≠ 0) (hga : ga * ga = T / ms a na) (hgb : gb * gb = T / ms b nb) : ms (scale ga a) na = ms (scale gb b) nb` | `propext`, `Classical.choice`, `Quot.sound` |
| `current_order` · 41 | 포락선 → 경사 → RMS 보정 | `{e r x : Nat → Rat} {n : Nat} {g T : Rat} (h : ms (pmul r (pmul e x)) n ≠ 0) (hg : g * g = T / ms (pmul r (pmul e x)) n) : ms (scale g (pmul r (pmul e x))) n = T` | `propext`, `Classical.choice`, `Quot.sound` |
| `old_order_power` · 46 | 경사 전에 RMS를 맞추는 순서 | `(r x : Nat → Rat) (g : Rat) (n : Nat) : ms (pmul r (scale g x)) n = g * g * ms (pmul r x) n` | `propext`, `Classical.choice`, `Quot.sound` |
| `old_order_can_differ` · 57 | 경사 전에 RMS를 맞추는 순서 | `: ms xuEx 4 = 1 ∧ ms xmEx 4 = 4 ∧ ms (scale 2 xuEx) 4 = 4 ∧ ms (scale 1 xmEx) 4 = 4 ∧ ms (pmul rEx (scale 2 xuEx)) 4 = 5 / 2 ∧ ms (pmul rEx (scale 1 xmEx)) 4 = 1` | `propext`, `Classical.choice`, `Quot.sound` |
| `guard_changes_power` · 64 | 피크 제한 후의 세기 | `{x : Nat → Rat} {n : Nat} {s T : Rat} (h : ms x n = T) (hs : s * s ≠ 1) (hT : T ≠ 0) : ms (scale s x) n ≠ T` | `propext`, `Classical.choice`, `Quot.sound` |

### Ramp.lean · 11개

| 정리 · 줄 | 검사 규칙 또는 수식 | 명제 | 공리 |
|---|---|---|---|
| `two_R_pos` · 24 | 선형 경사 `aᵢ = (i + 0.5)/R` | `{R : Nat} (hR : 0 < R) : (0 : Rat) < ((2 * R : Nat) : Rat)` | `propext`, `Classical.choice`, `Quot.sound` |
| `ramp_pos` · 26 | 선형 경사 `aᵢ = (i + 0.5)/R` | `{R i : Nat} (hR : 0 < R) : 0 < rampGain R i` | `propext`, `Classical.choice`, `Quot.sound` |
| `ramp_lt_one` · 32 | 선형 경사 `aᵢ = (i + 0.5)/R` | `{R i : Nat} (hi : i < R) : rampGain R i < 1` | `propext`, `Classical.choice`, `Quot.sound` |
| `ramp_mono` · 37 | 선형 경사 `aᵢ = (i + 0.5)/R` | `{R i j : Nat} (hR : 0 < R) (hij : i < j) : rampGain R i < rampGain R j` | `propext`, `Classical.choice`, `Quot.sound` |
| `ramp_symm` · 43 | 선형 경사 `aᵢ = (i + 0.5)/R` | `{R i : Nat} (hi : i < R) : rampGain R i + rampGain R (R - 1 - i) = 1` | `propext`, `Classical.choice`, `Quot.sound` |
| `rampLen_half` · 53 | 양 끝 경사와 전체 창 | `(fs rampMs N : Nat) : 2 * rampLen fs rampMs N ≤ N` | `propext`, `Quot.sound` |
| `ramp_ends_disjoint` · 56 | 양 끝 경사와 전체 창 | `{R N i : Nat} (h : 2 * R ≤ N) (hi : i < R) : R ≤ N - 1 - i` | `propext`, `Quot.sound` |
| `rampW_pos` · 61 | 양 끝 경사와 전체 창 | `{R N j : Nat} (hR : 0 < R) : 0 < rampW R N j` | `propext`, `Classical.choice`, `Quot.sound` |
| `rampW_le_one` · 69 | 양 끝 경사와 전체 창 | `{R N j : Nat} (h : 2 * R ≤ N) (hj : j < N) : rampW R N j ≤ 1` | `propext`, `Classical.choice`, `Quot.sound` |
| `rampW_symm` · 77 | 양 끝 경사와 전체 창 | `{R N j : Nat} (h : 2 * R ≤ N) (hj : j < N) : rampW R N j = rampW R N (N - 1 - j)` | `propext`, `Classical.choice`, `Quot.sound` |
| `rampLen_values` · 91 | 지정 프로토콜의 경사 길이 | `: rampLen 48000 10 48000 = 480 ∧ rampLen 48000 30 24000 = 1440 ∧ rampLen 44100 10 44100 = 441 ∧ rampLen 44100 30 22050 = 1323` | 없음 |

### Band.lean · 15개

| 정리 · 줄 | 검사 규칙 또는 수식 | 명제 | 공리 |
|---|---|---|---|
| `sq_nonneg` · 22 | 필터 부등식의 보조 정리 | `(x : Rat) : 0 ≤ x * x` | `propext`, `Classical.choice`, `Quot.sound` |
| `p4_nonneg` · 27 | 필터 부등식의 보조 정리 | `(x : Rat) : 0 ≤ p4 x` | `propext`, `Classical.choice`, `Quot.sound` |
| `sq_mono` · 29 | 필터 부등식의 보조 정리 | `{x y : Rat} (hx : 0 ≤ x) (hxy : x ≤ y) : x * x ≤ y * y` | `propext`, `Classical.choice`, `Quot.sound` |
| `p4_mono` · 33 | 필터 부등식의 보조 정리 | `{x y : Rat} (hx : 0 ≤ x) (hxy : x ≤ y) : p4 x ≤ p4 y` | `propext`, `Classical.choice`, `Quot.sound` |
| `div_anti` · 37 | 필터 부등식의 보조 정리 | `{a b c : Rat} (ha : 0 < a) (hab : a ≤ b) (hc : 0 ≤ c) : c / b ≤ c / a` | `propext`, `Classical.choice`, `Quot.sound` |
| `div_mono` · 47 | 필터 부등식의 보조 정리 | `{x y c : Rat} (hc : 0 < c) (hxy : x ≤ y) : x / c ≤ y / c` | `propext`, `Classical.choice`, `Quot.sound` |
| `den_ge_one` · 53 | 필터 부등식의 보조 정리 | `(f : Rat) : 1 ≤ (1 + p4 (80 / f)) * (1 + p4 (f / 8500))` | `propext`, `Classical.choice`, `Quot.sound` |
| `G2_pos` · 60 | 80–8,500 Hz 대역의 제곱 이득 `G2 = 1/[(1+(80/f)⁴)(1+(f/8500)⁴)]` | `(f : Rat) : 0 < G2 f` | `propext`, `Classical.choice`, `Quot.sound` |
| `G2_le_one` · 66 | 80–8,500 Hz 대역의 제곱 이득 `G2 = 1/[(1+(80/f)⁴)(1+(f/8500)⁴)]` | `(f : Rat) : G2 f ≤ 1` | `propext`, `Classical.choice`, `Quot.sound` |
| `G2_at_80` · 72 | 80–8,500 Hz 대역의 제곱 이득 `G2 = 1/[(1+(80/f)⁴)(1+(f/8500)⁴)]` | `: 49999 / 100000 < G2 80 ∧ G2 80 ≤ 1 / 2` | `propext`, `Classical.choice`, `Quot.sound` |
| `G2_at_8500` · 74 | 80–8,500 Hz 대역의 제곱 이득 `G2 = 1/[(1+(80/f)⁴)(1+(f/8500)⁴)]` | `: 49999 / 100000 < G2 8500 ∧ G2 8500 ≤ 1 / 2` | `propext`, `Classical.choice`, `Quot.sound` |
| `G2_octave_out` · 76 | 80–8,500 Hz 대역의 제곱 이득 `G2 = 1/[(1+(80/f)⁴)(1+(f/8500)⁴)]` | `: G2 40 ≤ 1 / 17 ∧ G2 17000 ≤ 1 / 17` | `propext`, `Classical.choice`, `Quot.sound` |
| `G2_lower` · 79 | 통과대역 전력 이득 하한 | `{a b f : Rat} (ha : 0 < a) (haf : a ≤ f) (hfb : f ≤ b) : 1 / ((1 + p4 (80 / a)) * (1 + p4 (b / 8500))) ≤ G2 f` | `propext`, `Classical.choice`, `Quot.sound` |
| `G2_pass_200_2000` · 105 | 통과대역 전력 이득 하한 | `{f : Rat} (h1 : 200 ≤ f) (h2 : f ≤ 2000) : 97 / 100 ≤ G2 f` | `propext`, `Classical.choice`, `Quot.sound` |
| `G2_pass_2000_5000` · 110 | 통과대역 전력 이득 하한 | `{f : Rat} (h1 : 2000 ≤ f) (h2 : f ≤ 5000) : 89 / 100 ≤ G2 f` | `propext`, `Classical.choice`, `Quot.sound` |

### Spectrum.lean · 9개

| 정리 · 줄 | 검사 규칙 또는 수식 | 명제 | 공리 |
|---|---|---|---|
| `half_pos` · 29 | 광대역 옆띠 | `{x : Rat} (hx : 0 ≤ x) : 0 < 1 + x / 2` | `propext`, `Classical.choice`, `Quot.sound` |
| `wide_flat` · 33 | 광대역 옆띠 | `{fN x fm f : Rat} (hx : 0 ≤ x) (h0 : Swide fN f = 1) (h1 : Swide fN (f - fm) = 1) (h2 : Swide fN (f + fm) = 1) : modSpec (Swide fN) x fm f = Swide fN f` | `propext`, `Classical.choice`, `Quot.sound` |
| `wide_strip` · 41 | 광대역 옆띠 | `{fN x fm f : Rat} (h0 : Swide fN f = 1) (h1 : Swide fN (f - fm) = 0) (h2 : Swide fN (f + fm) = 1) : modSpec (Swide fN) x fm f = (1 + x / 4) / (1 + x / 2)` | `propext`, `Classical.choice`, `Quot.sound` |
| `strip_ge` · 48 | 가장자리 전력비 | `{x : Rat} (hx : 0 ≤ x) (h1 : x ≤ 1) : 5 / 6 ≤ (1 + x / 4) / (1 + x / 2)` | `propext`, `Classical.choice`, `Quot.sound` |
| `strip_small_m` · 55 | 가장자리 전력비 | `{x : Rat} (hx : 0 ≤ x) (h1 : x ≤ 1 / 10) : 41 / 42 ≤ (1 + x / 4) / (1 + x / 2)` | `propext`, `Classical.choice`, `Quot.sound` |
| `strip_db` · 68 | 가장자리 전력비 | `: 5 ^ 1000 * 10 ^ 79 < 6 ^ 1000 ∧ 6 ^ 1000 < 5 ^ 1000 * 10 ^ 80` | 없음 |
| `crest_m1` · 73 | 포락선 봉우리 전력비 `(1+m)²/(1+m²/2)` | `: crest 1 = 8 / 3` | `propext`, `Classical.choice`, `Quot.sound` |
| `crest_m1_db` · 77 | 포락선 봉우리 전력비 `(1+m)²/(1+m²/2)` | `: 3 ^ 1000 * 10 ^ 425 < 8 ^ 1000 ∧ 8 ^ 1000 < 3 ^ 1000 * 10 ^ 426` | 없음 |
| `crest_m316` · 80 | 포락선 봉우리 전력비 `(1+m)²/(1+m²/2)` | `: 164 / 100 < crest (316 / 1000) ∧ crest (316 / 1000) < 166 / 100` | `propext`, `Classical.choice`, `Quot.sound` |

### Grid.lean · 14개

| 정리 · 줄 | 검사 규칙 또는 수식 | 명제 | 공리 |
|---|---|---|---|
| `fine_length` · 29 | 변조 주파수 격자 | `: fineFms.length = 60` | 없음 |
| `fine_mem_iff` · 31 | 변조 주파수 격자 | `(f : Nat) : f ∈ fineFms ↔ (5 ≤ f ∧ f ≤ 300 ∧ f % 5 = 0)` | `propext`, `Classical.choice`, `Quot.sound` |
| `fine_sorted` · 38 | 변조 주파수 격자 | `: fineFms.Pairwise (· < ·)` | 없음 |
| `papers_in_fine` · 40 | 프로토콜 주파수 | `: (∀ f ∈ wonFms, f ∈ fineFms) ∧ (∀ f ∈ parkFms, f ∈ wonFms) ∧ (∀ f ∈ drFms, f ∈ fineFms)` | `propext`, `Quot.sound` |
| `off_paper_counts` · 43 | 프로토콜 주파수 | `: (fineFms.filter (fun f => f ∉ wonFms)).length = 53 ∧ (fineFms.filter (fun f => f ∉ drFms)).length = 53` | `propext`, `Quot.sound` |
| `interval_samples` · 49 | 자극 길이·변조 주기 | `: jsRound (44100 * 1) = 44100 ∧ jsRound (48000 * 1) = 48000 ∧ jsRound (44100 * (1 / 2)) = 22050 ∧ jsRound (48000 * (1 / 2)) = 24000 ∧ jsRound (44100 * (8 / 10)) = 35280 ∧ jsRound (48000 * (8 / 10)) = 38400` | `propext`, `Classical.choice`, `Quot.sound` |
| `interval_exact` · 55 | 자극 길이·변조 주기 | `: ((44100 : Int) : Rat) / 44100 = 1 ∧ ((48000 : Int) : Rat) / 48000 = 1 ∧ ((22050 : Int) : Rat) / 44100 = 1 / 2 ∧ ((24000 : Int) : Rat) / 48000 = 1 / 2` | `propext`, `Classical.choice`, `Quot.sound` |
| `cycles_min` · 59 | 자극 길이·변조 주기 | `: ∀ f ∈ fineFms, (5 : Rat) / 2 ≤ (f : Rat) * (1 / 2) ∧ (5 : Rat) ≤ (f : Rat) * 1` | `propext`, `Classical.choice`, `Quot.sound` |
| `countMod3_succ` · 64 | 정답 구간 선택 | `(M r : Nat) : countMod3 (M + 1) r = countMod3 M r + (if M % 3 = r then 1 else 0)` | `propext` |
| `countMod3_closed` · 69 | 정답 구간 선택 | `(M r : Nat) (hr : r < 3) : countMod3 M r = M / 3 + (if r < M % 3 then 1 else 0)` | `propext`, `Quot.sound` |
| `countMod2_succ` · 79 | 정답 구간 선택 | `(M r : Nat) : countMod2 (M + 1) r = countMod2 M r + (if M % 2 = r then 1 else 0)` | `propext` |
| `countMod2_closed` · 84 | 정답 구간 선택 | `(M r : Nat) (hr : r < 2) : countMod2 M r = M / 2 + (if r < M % 2 then 1 else 0)` | `propext`, `Quot.sound` |
| `target_counts` · 91 | 정답 구간 선택 | `: countMod2 4294967296 0 = 2147483648 ∧ countMod2 4294967296 1 = 2147483648 ∧ countMod3 4294967296 0 = 1431655766 ∧ countMod3 4294967296 1 = 1431655765 ∧ countMod3 4294967296 2 = 1431655765` | `propext`, `Quot.sound` |
| `target_bias3` · 102 | 정답 구간 선택 | `: (1431655766 : Rat) / 4294967296 - 1 / 3 = 2 / (3 * 4294967296)` | `propext`, `Classical.choice`, `Quot.sound` |

### Rng.lean · 5개

| 정리 · 줄 | 검사 규칙 또는 수식 | 명제 | 공리 |
|---|---|---|---|
| `gamma_eq` · 22 | 자극 잡음의 32비트 난수 상태 | `: gammaU.toNat = gammaN` | 없음 |
| `uniform_range` · 43 | 자극 잡음의 32비트 난수 상태 | `(u : UInt32) : 0 ≤ uniformQ u ∧ uniformQ u < 1` | `propext`, `Classical.choice`, `Quot.sound` |
| `state_formula` · 53 | 자극 잡음의 32비트 난수 상태 | `(s : UInt32) (k : Nat) : (mbState s k).toNat = (s.toNat + k * gammaN) % 4294967296` | `propext`, `Quot.sound` |
| `gamma_coprime` · 62 | 자극 잡음의 32비트 난수 상태 | `: Nat.Coprime 4294967296 gammaN` | `propext` |
| `state_injective` · 65 | 자극 잡음의 32비트 난수 상태 | `(s : UInt32) {j k : Nat} (hjk : j < k) (hk : k < 4294967296) : mbState s j ≠ mbState s k` | `propext`, `Quot.sound` |

### Basic.lean · 9개

| 정리 · 줄 | 검사 규칙 또는 수식 | 명제 | 공리 |
|---|---|---|---|
| `sumQ_zero` · 18 | 평균제곱·포락선 계산의 기초 | `(f : Nat → Rat) : sumQ f 0 = 0` | `propext`, `Classical.choice`, `Quot.sound` |
| `sumQ_succ` · 19 | 평균제곱·포락선 계산의 기초 | `(f : Nat → Rat) (n : Nat) : sumQ f (n + 1) = sumQ f n + f n` | `propext`, `Classical.choice`, `Quot.sound` |
| `sumQ_congr` · 21 | 평균제곱·포락선 계산의 기초 | `{f g : Nat → Rat} {n : Nat} (h : ∀ i, i < n → f i = g i) : sumQ f n = sumQ g n` | `propext`, `Classical.choice`, `Quot.sound` |
| `sumQ_add` · 26 | 평균제곱·포락선 계산의 기초 | `(f g : Nat → Rat) (n : Nat) : sumQ (fun i => f i + g i) n = sumQ f n + sumQ g n` | `propext`, `Classical.choice`, `Quot.sound` |
| `sumQ_mul_left` · 31 | 평균제곱·포락선 계산의 기초 | `(c : Rat) (f : Nat → Rat) (n : Nat) : sumQ (fun i => c * f i) n = c * sumQ f n` | `propext`, `Classical.choice`, `Quot.sound` |
| `sumQ_const` · 36 | 평균제곱·포락선 계산의 기초 | `(c : Rat) (n : Nat) : sumQ (fun _ => c) n = c * n` | `propext`, `Classical.choice`, `Quot.sound` |
| `le_div_of_pos` · 44 | 수식 경계의 보조 정리 | `{a b c : Rat} (hc : 0 < c) : a ≤ b / c ↔ a * c ≤ b` | `propext`, `Classical.choice`, `Quot.sound` |
| `div_le_of_pos` · 48 | 수식 경계의 보조 정리 | `{a b c : Rat} (hc : 0 < c) : a / c ≤ b ↔ a ≤ b * c` | `propext`, `Classical.choice`, `Quot.sound` |
| `lt_le_trans` · 52 | 수식 경계의 보조 정리 | `{a b c : Rat} (h1 : a < b) (h2 : b ≤ c) : a < c` | `propext`, `Classical.choice`, `Quot.sound` |
