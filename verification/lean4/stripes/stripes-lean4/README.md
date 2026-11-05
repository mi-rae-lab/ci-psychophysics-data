# STRIPES Lean 4 검증 보고서

2026년 11월 4일 재검증 · Lean 4.24.0 · 앱 대조 기준 1.1.0 (2026년 10월 21일)

**Lean이 증명한 대상은 검사 절차를 별도로 구현한 수학 모델이다.** 실제 앱은 JavaScript로 계단을 갱신하고, 미리 만든 MP3를 디코딩해 재생한다. Lean 모델과 앱 구현 사이의 동치 정리, 자극 파형에 관한 정리는 없다.

## 원본과 재현 방법

2026년 10월 16일 작업의 `new-chat/outputs/stripes-lean4`에서 증명 모듈 4개, 진입 모듈 `Stripes.lean`, 공리 검사 파일 `Audit.lean`을 가져왔다. 이 6개 소스와 `lean-toolchain`, `lakefile.toml`은 당시 원본 해시 및 검증 사본과 바이트 단위로 일치한다. `lake-manifest.json`은 같은 작업의 빌드 사본 `new-chat/work/stripes-lean-check`에서 가져왔다. 외부 패키지 목록은 비어 있다. 9개 빌드 입력의 SHA-256은 ZIP 안의 `source-sha256.txt`에 있다.

ZIP을 풀고 `stripes-lean4` 폴더에서 다음을 실행한다. `lean-toolchain`에 지정된 Lean과 Lake를 사용한다.

```sh
lake build
lake env lean Audit.lean
```

| 재검증 항목 | 결과 |
|---|---|
| 빌드 | 기존 `.lake` 캐시 없이 실행. 종료 코드 0. `Build completed successfully (7 jobs).` 빌드 경고 0개. |
| 공리 감사 | 종료 코드 0. 소스의 이름 있는 정리 95개, 감사 대상 95개, 결과 95개가 이름별로 일치. |
| 미완성 증명 | 전체 프로젝트 소스 6개에서 `sorry`, `admit`, `sorryAx` 0건. 95개 정리의 공리 출력에서도 `sorryAx` 0건. 보고할 파일·줄 없음. |
| 공리별 정리 수 | 공리 없음 23개 · `propext`만 13개 · `propext, Quot.sound` 4개 · `propext, Classical.choice, Quot.sound` 55개. |

두 명령의 전체 출력은 별도 파일에서 확인할 수 있다. [빌드 로그](lake-build.txt) · [정리별 공리 출력](print-axioms.txt)

## 계단 규칙과 자극 수식의 증명 범위

아래에서 **일반 정리**는 명시한 가정을 만족하는 모든 입력에 적용된다. **고정 사례**는 특정 응답열에 대한 정리다. **정의**는 모델이 어떤 동작을 하도록 작성했는지 나타낸다. 정리 이름 앞의 `Stripes.Staircase.`는 이 표에서 생략했다.

| 요청 항목 | 모델에서 확인한 내용 | 근거와 범위 |
|---|---|---|
| 2-down 1-up의 방향 | 이 검사에서 밀도 D가 커질수록 어렵다. 유효 정답 2회 연속이면 D를 높이고 연속 횟수를 초기화한다. 유효 오답 1회면 연속 횟수를 0으로 하고 D를 낮추는 이동을 요청한다. 앱은 D축에서 이를 **2-up/1-down**이라 부른다. 경계에서는 요청한 방향으로 더 움직일 수 없다. | `applyResponse` 정의. `fixture_lower_boundary_WWCC`와 `fixture_invalid_keeps_correct_streak`는 고정 사례다. `Statistics.equal_step_balance`는 국소 독립·정상 반응과 같은 양의 단계 크기로 해석할 때 평형식 p² = 1/2을 준다. 유한 계단의 수렴 정리는 없다. |
| 단계 크기 변경 | 반전을 먼저 센다. 실제 반전이 4개 미만이면 요청 폭은 0.5 D, **4번째 반전에서 떠나는 이동부터** 0.2 D다. 경계에서 실제 이동 폭은 줄어들 수 있다. | `applyMove` 정의와 `fixture_reversals`의 고정 사례. 전환 시점을 따로 명시한 전 입력 대상 정리는 없다. |
| 반전 횟수와 종료 | 실제 이동 방향이 직전 실제 이동과 달라지면 이동 **전** 제시값을 기록한다. 첫 이동과 경계에서 막힌 이동은 반전 수를 늘리지 않는다. 8번째 실제 반전에서 끝나며 유효 시행 상한과 겹치면 반전 종료가 우선이다. | `first_move_not_reversal`, `blocked_request_is_no_move`는 일반 정리다. `finishValid`는 종료 우선순위의 정의다. `fixture_reversals`, `fixture_stops_at_sixteen`은 특정 16응답으로 8번을 채우는 정리다. |
| 역치 계산 | 8반전 완주 시 마지막 네 반전의 제시 tick 합을 40으로 나누면 D 단위 역치가 된다. 검증 응답열에서 남은 tick은 18, 16, 18, 16이다. **68/40 = 17/10 = 1.7 D**. | `retained`, `threshold` 정의. `fixture_retained`, `fixture_exact_threshold`, `fixture_threshold_is_seventeen_tenths`는 고정 사례다. `Design.retained_sum_scale_forty`는 4개 × 10 tick/D의 환산 상수를 확인한다. |
| 측정 불가 | 모델에서 반전 목표에 도달한 상태가 아니면 역치는 `none`이다. 무효 응답은 적응 상태를 보존한다. 초기 상태에서 무효 10회면 기술 실패, 전부 오답 200회면 반전 0개로 종료하고 역치는 없다. | `incomplete_has_no_threshold`, `invalid_preserves_adaptive_core`, `fresh_invalid_increments_technical_count`는 일반 정리다. `fixture_ten_invalids`, `fixture_all_incorrect_trial_cap`은 고정 사례다. |
| 자극 밀도와 시간 | 앱 사양은 250–8000 Hz를 1초에 훑으므로 대역폭 B = 5옥타브다. 밀도 D의 시작 간격 δ = 1/D초, 주파수축 밀도 RPO = D/5, 같은 주파수를 다시 지나는 비율은 D Hz다. | **대응 Lean 정리 0개.** 앱은 역치 표시에 RPO = D/5를 계산한다. D 단위의 역치 산술을 증명한 정리가 이 자극 관계까지 증명하지는 않는다. |
| 자극 파형과 rove | 지수 sweep의 순간 주파수와 적분 위상, 여러 sweep을 겹친 파형, rove 격자, MP3 디코딩 및 실제 출력이 대상이다. | **대응 Lean 정리 0개.** 앱은 고정 음원 모음을 사용한다. 첨부 자료의 스펙트로그램 분석은 방향·밀도·rove를 파일에서 추정하며, 이것은 Lean 증명과 별도의 근거다. |

## 앱과 대조했을 때의 차이

- **실행 경로.** `js/app.js:1065–1067`에서 적응 시행이 JavaScript의 `Stair.step`을 호출한다. `js/app.js:955,974,976`은 음원 로드, 시행 버퍼 구성, 재생을 연결한다. `js/bank.js:37–45`는 고정 음원을 읽고 디코딩한다. `Stripes/Staircase.lean:3–16`은 제시된 밀도에 대한 응답을 입력으로 받는 모델의 경계를 명시한다.
- **종료 뒤 새 입력.** Lean의 `step`은 종료 상태를 그대로 돌려준다(`Stripes/Staircase.lean:122–125`). 앱은 새 시행 ID가 종료 뒤 들어오면 오류를 낸다. 앱은 제시 밀도가 계단 상태와 일치하는지도 검사한다(`js/staircase.js:25–31`). 이 차이 때문에 정상 사례의 수치 일치만으로 두 프로그램의 전체 동치를 주장할 수 없다.
- **어떤 결과에 숫자를 붙이는가.** 모델 `threshold`는 성공 종료 상태와 반전 8개 이상을 함께 검사한다(`Stripes/Staircase.lean:142–152`). 앱 `Stair.threshold`는 반전 수로 계산하고 결과 분류를 별도 단계에서 한다(`js/staircase.js:101–109`, `js/analysis.js:60–83`). 앱은 8반전을 채운 측정에 하한·상한 영향이 있으면 표시와 함께 역치를 포함할 수 있다. 참가자 중단의 분류, 기록 대조 실패 시 참고값만 보관하고 평균에서 제외하는 정책, 훈련 실패 뒤 1.1 D 고정 30회 정답률 보고는 이 Lean 계단 모델의 증명 범위 밖이다(`js/analysis.js:102–111,190–205`, `js/staircase.js:146–161`).
- **자극 근거.** `js/protocol.js:12–27,69–72`는 음원 모음과 수식을 기록하고 `js/staircase.js:103–108`은 D를 RPO로 변환한다. `tools/analyze_bank.py:6–15`, `검증.md:27–32`는 실제 음원의 로그 주파수 궤적과 rove 분석 근거다. 기존 기록에서 3,800개 파일의 sweep 방향이 이름과 일치했고, 추정 밀도와 이름의 차이는 최대 0.055 D였다.
- **앱의 기존 검증 기록.** `검증_통과.json`의 2026년 10월 21일 기록은 고정 JavaScript 시험 44개, 서버 시험 19개, 화면 코드 점검 62개의 통과 기록이다. 이 보고서의 Lean 빌드와 공리 감사는 위의 두 명령으로 11월 4일 다시 수행했다.

## 정리별 대응표와 공리

각 행의 정리 이름 앞에 섹션의 네임스페이스를 붙이면 `#print axioms`에 사용한 전체 이름이 된다. 줄 번호는 ZIP에 들어 있는 원본 소스 기준이다. 공리 열의 P는 `propext`, C는 `Classical.choice`, Q는 `Quot.sound`를 뜻한다. ‘없음’은 해당 정리가 어떤 공리에도 의존하지 않는다는 Lean의 출력이다.

### `Stripes.Staircase` · 18개

소스 `Stripes/Staircase.lean`

| 줄 | 정리 | 규칙·대상 | 증명 내용 | 공리 |
|---:|---|---|---|---|
| 156 | `step_bounds` | 밀도 범위 · 일반 | 모든 상태·시행 ID·응답에 대해 한 단계 뒤 밀도는 11~200 tick(1.1~20.0 D)이다. | P, C, Q |
| 161 | `duplicate_ignored` | 중복 시행 · 일반 | 이미 처리한 ID를 다시 입력하면 응답과 관계없이 상태 전체가 유지된다. | P, C, Q |
| 166 | `terminal_absorbing` | 종료 처리 · 일반 | 모델은 종료 상태에서 추가 입력을 받아도 상태 전체를 유지한다. 앱은 종료 뒤 새 ID에 오류를 낸다. | P, C, Q |
| 175 | `invalid_preserves_adaptive_core` | 무효 시행 · 일반 | 무효 응답은 밀도·정답 연속 횟수·마지막 이동 방향·반전 목록·이동 수·유효 시행 수를 보존한다. | P, C, Q |
| 183 | `fresh_invalid_increments_technical_count` | 기술 실패 · 일반 | 진행 중인 상태에서 새 ID의 무효 응답 한 번은 기술 실패 수를 정확히 1 늘린다. | P, C, Q |
| 188 | `blocked_request_is_no_move` | 경계와 반전 · 일반 | 경계 밖으로 향해 막힌 이동 요청은 applyMove의 입력 상태 전체를 유지하여 이동이나 반전을 추가하지 않는다. | P, C, Q |
| 193 | `first_move_not_reversal` | 반전 횟수 · 일반 | 직전 이동 방향이 없으면 이동 요청 뒤에도 반전 목록이 그대로다. | P, C, Q |
| 198 | `incomplete_has_no_threshold` | 측정 불가 · 일반 | 상태가 반전 목표 도달이 아니면 모델의 역치 결과는 none이다. | P |
| 212 | `fixture_reversals` | 반전 횟수·단계 변경 · 고정 사례 | 지정한 16응답에서 반전 제시값은 차례로 [21, 16, 21, 16, 18, 16, 18, 16] tick이다. 4번째 반전을 떠날 때 단계가 바뀌는 정의를 이 응답열에서 간접 확인한다. | P, C, Q |
| 216 | `fixture_retained` | 역치에 쓸 반전 · 고정 사례 | 같은 16응답의 마지막 네 반전은 [18, 16, 18, 16] tick이다. | P, C, Q |
| 219 | `fixture_exact_threshold` | 역치 계산 · 고정 사례 | 같은 응답열의 역치 출력은 정확히 분자 68, 분모 40이다(네 반전의 tick 합과 D 단위 환산). | P, C, Q |
| 224 | `fixture_threshold_is_seventeen_tenths` | 역치 계산 · 고정 사례 | 같은 역치의 분모는 양수이며 교차곱으로 17/10 D와 같음을 증명한다. | P, C, Q |
| 230 | `fixture_stops_at_sixteen` | 반전 종료 · 고정 사례 | 같은 응답열에서 16번째 유효 시행 후 상태는 반전 목표 도달이고 다음 계획 밀도는 18 tick이다. | P, C, Q |
| 236 | `fixture_later_input_ignored` | 반전 종료 후 처리 · 고정 사례 | 이 16응답으로 끝난 상태에 임의의 시행 ID와 응답을 넣어도 모델의 상태는 그대로다. | P, C, Q |
| 241 | `fixture_lower_boundary_WWCC` | 2회 정답·1회 오답 및 경계 · 고정 사례 | 초기 하한에서 오답·오답·정답·정답을 넣으면 실제 이동은 1번, 반전은 0번이며 최종 밀도는 16 tick이다. | P, C, Q |
| 246 | `fixture_invalid_keeps_correct_streak` | 무효 시행과 정답 연속 횟수 · 고정 사례 | 정답·무효·정답은 시도 3회 중 유효 2회이며 실제 이동 1회로 16 tick에 도달한다. | P, C, Q |
| 251 | `fixture_ten_invalids` | 기술 실패 중단 · 고정 사례 | 초기 상태에서 무효 응답 10번이면 기술 실패 상태가 되고 시도 수는 10, 밀도는 11 tick이다. | P, C, Q |
| 257 | `fixture_all_incorrect_trial_cap` | 유효 시행 상한·측정 불가 · 고정 사례 | 초기 상태에서 오답 200번이면 유효 시행 상한으로 끝나고 반전 목록은 비어 있으며 역치는 none이다. | P, C, Q |

### `Stripes.Design` · 42개

소스 `Stripes/Design.lean`

| 줄 | 정리 | 규칙·대상 | 증명 내용 | 공리 |
|---:|---|---|---|---|
| 30 | `choice_outcomes_four` | 양자택일 | 표적과 응답이 각각 A 또는 B이면 가능한 순서쌍은 4개다. | 없음 |
| 32 | `choice_correct_two` | 양자택일 | 표적과 응답이 일치하는 순서쌍은 4개 중 2개다. | 없음 |
| 36 | `chance_is_one_half` | 양자택일 | 네 순서쌍이 등확률일 때 정답 비율은 2/4 = 1/2이다. | 없음 |
| 56 | `gate_words_have_length_five` | 훈련 통과 | 모델이 열거한 한 블록의 모든 응답열은 길이가 5다. | 없음 |
| 59 | `gate_words_have_no_duplicates` | 훈련 통과 | 한 블록의 응답열 목록에는 중복이 없다. | 없음 |
| 61 | `gate_outcomes_32` | 훈련 통과 | 5회 시행의 정답·오답 조합은 32개다. | 없음 |
| 62 | `gate_passes_6` | 훈련 통과 | 5회 중 4회 이상 맞히는 통과 조합은 6개다. | 없음 |
| 63 | `gate_fails_26` | 훈련 통과 | 5회 중 4회 미만 맞히는 실패 조합은 26개다. | 없음 |
| 66 | `exactly_four_successes_5` | 훈련 통과 | 5회 중 정확히 4회를 맞히는 응답열은 5개다. | 없음 |
| 71 | `exactly_five_successes_1` | 훈련 통과 | 5회를 모두 맞히는 응답열은 1개다. | 없음 |
| 75 | `gate_success_partition` | 훈련 통과 | 통과 조합 수는 정확히 4회 정답인 5개와 모두 정답인 1개의 합이다. | 없음 |
| 78 | `gate_chance_three_sixteenths` | 훈련 통과 | 5번을 독립적으로 무작위 추측하면 한 블록 통과 비율은 6/32 = 3/16이다. | 없음 |
| 88 | `wordsFrom_length` | 훈련 반복 | 길이 k의 목록에서 복원 추출로 만든 길이 n인 순서열 목록의 항목 수는 kⁿ이다. | P, Q |
| 104 | `four_blocks_product_space_count` | 훈련 반복 | 네 블록의 결과를 미리 뽑은 모든 순서열 수는 한 블록 결과 수의 네제곱이다. | P, Q |
| 108 | `four_blocks_all_fail_space_count` | 훈련 반복 | 네 블록이 모두 실패하는 순서열 수는 한 블록 실패 조합 수의 네제곱이다. | P, Q |
| 113 | `four_blocks_outcomes` | 훈련 반복 | 네 블록의 전체 결과는 1,048,576가지다. | 없음 |
| 114 | `four_blocks_all_fail` | 훈련 반복 | 네 블록이 모두 실패하는 결과는 456,976가지다. | 없음 |
| 115 | `four_blocks_any_pass` | 훈련 반복 | 네 블록 중 한 번 이상 통과하는 결과는 591,600가지다. | 없음 |
| 118 | `four_blocks_reduced_ratio` | 훈련 반복 | 독립적인 무작위 추측에서 네 블록 이내에 한 번 이상 통과할 비율은 36,975/65,536이다. | 없음 |
| 121 | `fair_guesser_can_pass_gate` | 훈련 통과 | 무작위 추측으로도 한 블록을 통과할 수 있다. 통과 조합 수가 양수다. | 없음 |
| 122 | `fair_guesser_can_pass_by_block_four` | 훈련 반복 | 무작위 추측으로 네 블록 이내에 통과할 수 있다. 해당 결과 수가 양수다. | 없음 |
| 139 | `main_run_count_is_two_or_three` | 본검사 반복 | 정수 눈금 모델에서 필요한 본검사 횟수는 2회 또는 3회다. | P |
| 144 | `main_run_count_bounds` | 본검사 반복 | 정수 눈금 모델에서 필요한 본검사 횟수는 2회 이상 3회 이하다. | P, C, Q |
| 149 | `selected_run_count` | 본검사 반복 | 선택한 본검사 결과의 개수는 반복 규칙으로 정한 검사 횟수와 같다. | P |
| 154 | `gap_exactly_one_D_requests_no_third` | 본검사 반복 | 처음 두 결과의 차이가 정확히 10눈금(1 D)이면 2회로 끝난다. | P |
| 158 | `gap_above_one_D_requests_third` | 본검사 반복 | 처음 두 결과의 차이가 10눈금(1 D)을 초과하면 제3 검사를 요청한다. | P |
| 162 | `concrete_boundary` | 본검사 반복 | 처음 두 결과가 30·40눈금이면 2회로 끝난다. | 없음 |
| 163 | `concrete_above_boundary` | 본검사 반복 | 처음 두 결과가 30·41눈금이면 제3 검사를 요청한다. | 없음 |
| 179 | `practice_is_excluded` | 세션 평균 | 본검사 결과가 같으면 연습 결과를 바꿔도 세션 평균이 같다. | 없음 |
| 182 | `planned_mean_denominator_positive` | 세션 평균 | 선택된 본검사 횟수로 정하는 세션 평균의 분모는 양수다. | P, C, Q |
| 190 | `two_main_measurements_exact_mean` | 세션 평균 | 처음 두 정수 눈금 결과의 차이가 1 D 이하이면 평균은 두 값의 합/2다. | P |
| 196 | `three_main_measurements_exact_mean` | 세션 평균 | 처음 두 정수 눈금 결과의 차이가 1 D를 초과하면 평균은 세 값의 합/3이다. | P |
| 230 | `retained_sum_scale_forty` | 역치 단위 환산 | 보존한 반전 4개의 눈금 합을 D 단위의 회차 역치로 환산하는 분모는 4 × 10 = 40이다. | 없음 |
| 232 | `fractional_run_count_bounds` | 본검사 반복 | 보존한 반전 눈금 합으로 비교해 회차 역치에 소수 눈금을 허용해도 본검사는 2~3회다. | P, C, Q |
| 238 | `fractional_gap_exactly_one_D_requests_no_third` | 본검사 반복 | 처음 두 회차의 반전 눈금 합 차이가 40(회차 역치 차이 1 D)이면 2회로 끝난다. | P |
| 243 | `fractional_gap_above_one_D_requests_third` | 본검사 반복 | 처음 두 회차의 반전 눈금 합 차이가 40을 초과하면 제3 검사를 요청한다. | P |
| 248 | `fractional_two_run_mean` | 세션 평균 | 처음 두 회차의 반전 눈금 합 차이가 40 이하이면 세션 평균은 두 합을 더한 값/80 D이다. | P |
| 255 | `fractional_three_run_mean` | 세션 평균 | 처음 두 회차의 반전 눈금 합 차이가 40을 초과하면 세션 평균은 세 합을 더한 값/120 D이다. | P |
| 262 | `fractional_practice_is_excluded` | 세션 평균 | 각 회차의 반전 눈금 합으로 구하는 세션 평균은 연습 결과에 의존하지 않는다. | 없음 |
| 276 | `equal_measurements_request_two` | 본검사 반복 | 처음 두 결과가 같으면 2회로 끝난다. | P |
| 280 | `equal_measurements_mean` | 세션 평균 | 처음 두 결과가 같은 값 v이면 세션 평균의 분자·분모는 (v + v, 2)다. | P |
| 285 | `arbitrarily_biased_consistent_measurements` | 반복 측정의 편향 | 두 값이 모두 기준값에 임의의 자연수 편향을 더한 값이면 2회로 끝나고 평균에도 그 편향이 남는다. | P, Q |

### `Stripes.Statistics` · 19개

소스 `Stripes/Statistics.lean`

| 줄 | 정리 | 규칙·대상 | 증명 내용 | 공리 |
|---:|---|---|---|---|
| 23 | `movement_block_mass` | 계단 규칙의 확률 모형 | 정답확률 p로 독립 시행을 해석할 때 다음 이동을 만드는 W, CW, CC 세 경우의 확률식 합이 1이다. | P, C, Q |
| 27 | `movement_drift` | 계단 규칙의 확률 모형 | 경계에 막히지 않는 모형에서 이동 1회당 평균 변위 h·p² − e·[(1−p)+p(1−p)]는 (h+e)·p²−e이다. | P, C, Q |
| 37 | `equal_step_balance` | 계단 규칙의 평형 | 양방향 단계 크기가 같은 0 아닌 s이면 평균 변위가 0인 조건은 p²=1/2이다. | P, C, Q |
| 40 | `unequal_step_balance` | 계단 규칙의 평형 | 어려운 방향 단계 h와 쉬운 방향 단계 e에 대해 h+e≠0이면 평균 변위가 0인 조건은 p²=e/(h+e)이다. | P, C, Q |
| 44 | `guessing_lapse_identity` | 강제선택 반응 모형 | p=1/2+(1/2−lapse)·sensitivity이고 lapse≠1/2이면 sensitivity=(p−1/2)/(1/2−lapse)이다. | P, C, Q |
| 50 | `equicorrelated_moment_identity` | 반복 측정의 분산 | n≠0일 때 등분산·등공분산 모형의 평균 분산식은 공분산+(분산−공분산)/n으로 정리된다. | P, C, Q |
| 55 | `three_error_square` | 본 측정 평균의 오차 | 세 오차 평균의 제곱을 개별 제곱과 세 쌍의 교차곱으로 전개한다. | P, C, Q |
| 59 | `four_error_square` | 마지막 네 반전 평균의 오차 | 네 오차 평균의 제곱을 개별 제곱과 여섯 쌍의 교차곱으로 전개한다. | P, C, Q |
| 74 | `shifted_square_sum` | 편향과 오차 | 유한 오차열 e에 공통 편향 b를 더하면 제곱합은 n·b²+2b·Σe+Σe²이다. | P, C, Q |
| 85 | `zero_mean_noise_keeps_bias_square` | 편향과 오차 | 오차 합이 0이면 편향을 더한 제곱합은 n·b²+Σe²이다. | P, C, Q |
| 108 | `conditional_mean_adjustment` | 본 측정의 조건부 반복 | 첫 두 값의 차이가 1 D를 초과하면 두 값의 평균에 (셋째 값−두 값의 평균)/3을 더하고 그 밖에는 원래 평균을 쓴다. | P, C, Q |
| 117 | `asymmetric_single_mean` | 비대칭 반복 측정의 예 | 동일 가중치로 나열한 [4,4,4,8]에서 단일 측정의 평균은 5이다. | P, C, Q |
| 122 | `asymmetric_selected_mean` | 비대칭 반복 측정의 예 | [4,4,4,8]에서 독립적으로 세 값을 뽑은 경우를 모두 세면 조건부 반복 추정값의 평균은 39/8이다. | P, C, Q |
| 127 | `asymmetric_selected_bias` | 비대칭 반복 측정의 예 | 같은 유한 모형에서 조건부 반복 추정값의 평균과 참값 5의 차이는 −1/8이다. | P, C, Q |
| 132 | `symmetric_selected_unbiased` | 대칭 반복 측정의 예 | [4,6]에서 독립적으로 세 값을 뽑으면 조건부 반복 추정값의 평균은 참값 5이다. | P, C, Q |
| 137 | `symmetric_selected_mse` | 대칭 반복 측정의 예 | 같은 [4,6] 모형에서 참값 5에 대한 조건부 반복 추정값의 평균제곱오차는 5/9이다. | P, C, Q |
| 143 | `symmetric_fixed_two_mse` | 대칭 반복 측정의 예 | 같은 [4,6] 모형에서 고정 2회 평균의 평균제곱오차는 1/2이다. | P, C, Q |
| 148 | `symmetric_fixed_three_mse` | 대칭 반복 측정의 예 | 같은 [4,6] 모형에서 고정 3회 평균의 평균제곱오차는 1/3이다. | P, C, Q |
| 154 | `conditional_repeat_can_increase_mse` | 조건부 반복의 반례 | [4,6] 모형에서 조건부 반복의 평균제곱오차 5/9는 고정 2회의 1/2보다 크다. | P, C, Q |

### `Stripes.FiniteRisk` · 16개

소스 `Stripes/FiniteRisk.lean`

| 줄 | 정리 | 규칙·대상 | 증명 내용 | 공리 |
|---:|---|---|---|---|
| 63 | `square_nonnegative` | 오차 제곱 | 유리수 오차 x에 대해 x²는 0 이상이다. | P, C, Q |
| 70 | `square_le_square_of_nonnegative` | 오차 제곱 | 0 ≤ a ≤ b이면 a² ≤ b²이다. | P, C, Q |
| 78 | `squared_error_event_iff` | 허용오차 | ε > 0이면 x² ≥ ε²일 조건은 x ≤ −ε 또는 x ≥ ε이다. | P, C, Q |
| 99 | `secondMoment_nonnegative` | 오차의 이차모멘트 | 각 결과의 가중치가 0 이상이면 오차 제곱의 가중합 M은 0 이상이다. | P, C, Q |
| 113 | `atom_tail_bound` | 꼬리확률의 점별 상한 | 가중치 w ≥ 0인 한 결과에서 q × w × 1[x² ≥ q] ≤ w × x²이다. | P, C, Q |
| 124 | `cutoff_mul_tail_le_secondMoment` | 꼬리확률의 상한 | 음이 아닌 가중치의 유한 목록에서 q × 꼬리 질량 ≤ 오차 제곱의 가중합 M이다. | P, C, Q |
| 139 | `tailMass_nonnegative` | 꼬리 질량 | 음이 아닌 가중치를 쓴 꼬리 질량은 0 이상이다. | P, C, Q |
| 154 | `tailMass_le_mass` | 꼬리 질량 | 음이 아닌 가중치를 쓴 꼬리 질량은 전체 질량 이하이다. | P, C, Q |
| 169 | `tail_probability_bounds` | 꼬리확률 | 전체 질량이 1인 유한 오차 분포에서 꼬리확률은 0 이상 1 이하이다. | P, C, Q |
| 176 | `inside_plus_tail_eq_mass` | 허용범위와 꼬리 | 오차 제곱이 q 미만인 질량과 q 이상인 질량을 더하면 전체 질량이다. | P, C, Q |
| 190 | `coverage_from_tail_bound` | 허용범위 안의 확률 | 정규화된 분포에서 꼬리확률이 α 이하이면 내부 확률은 1−α 이상이다. | P, C, Q |
| 199 | `finite_second_moment_risk_bound` | 오차확률의 상한 | 유한 유리수 분포와 q > 0에 대해 P(오차² ≥ q) ≤ M/q이다. | P, C, Q |
| 210 | `finite_tolerance_risk_bound` | 허용오차 확률 | ε > 0이고 M ≤ αε²이면 P(오차² ≥ ε²) ≤ α이다. | P, C, Q |
| 232 | `fixed_sample_count_risk_bound` | 고정 횟수의 조건부 보장 | n, ε > 0이고 M ≤ V/n 및 V ≤ nαε²를 가정하면 허용오차에 닿거나 벗어날 확률이 α 이하이다. | P, C, Q |
| 248 | `sample_count_condition_iff` | 횟수 조건의 동치 | α, ε > 0이면 V/(αε²) ≤ n일 조건은 V ≤ nαε²이다. | P, C, Q |
| 267 | `fixed_n_risk_and_coverage_from_second_moment` | 고정 횟수의 조건부 보장 | 양의 자연수 n, 양의 α와 ε, M ≤ V/n, n ≥ V/(αε²) 아래에서 꼬리확률 ≤ α와 내부 확률 ≥ 1−α가 함께 성립한다. | P, C, Q |
