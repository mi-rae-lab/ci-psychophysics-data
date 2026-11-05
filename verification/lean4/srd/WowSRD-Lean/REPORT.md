# 와우SRD · Lean 4 검증 보고서

2026-11-04 (KST) · 검사 앱 1.0.7 · Lean 프로젝트 `srd_lean` 0.1.0 · Lean 4.24.0

**증명 대상은 검사 규칙의 Lean 모델이다.** 실제 검사 앱은 브라우저에서 JavaScript를 실행한다. 아래에서 정리는 Lean이 검사한 명제를, 정의는 모델에 직접 적힌 알고리즘이나 설정값을, 실행 대조는 같은 입력을 두 구현에 넣어 비교한 결과를 뜻한다.

## 1. 빌드와 공리 검사

원본 `tools/lean`의 Lean 소스 11개와 `lean-toolchain`, `lakefile.toml`, `lake-manifest.json`을 바이트 그대로 복사했다. 기존 `.lake` 빌드 캐시 없이 Windows x86-64에서 기본 대상 `SRD`와 `crosscheck`를 빌드했다. 외부 Lake 패키지는 0개다. 공개본에 추가한 `PrintAxioms.lean`은 원본 정리를 가져와 공리만 출력한다.

| 실행 | 결과 | ZIP 안의 원출력 |
|---|---|---|
| `lake build` | 종료 코드 0 · 23.25초 · `Build completed successfully (23 jobs).` · 경고·오류 0건 | `verification/lake-build.txt` |
| `lake env lean PrintAxioms.lean` | 소스에 이름을 붙여 선언한 정리 125개 전부의 `#print axioms` 출력 · 종료 코드 0 | `verification/print-axioms.txt` |
| `lake env lean MyAudit.lean` | `SRD` 네임스페이스의 상수 1,103개 검사. 정리 441개(자동 생성 포함), 그 밖의 상수 662개, 공리 선언 0개 · 종료 코드 0 | `verification/environment-audit.txt` |

**미완성 증명(`sorry`)은 0건이다.** 원본 Lean 소스에서 `sorry`가 나오는 곳은 `MyAudit.lean` 11행과 41행의 주석이다. 9행의 `sorryAx`도 감사 방식을 설명하는 주석이다. 공리 감사 결과에도 `sorryAx`가 없었다. 정리와 정의를 포함한 전체 `SRD` 상수의 공리 합집합은 `Classical.choice`, `Quot.sound`, `propext`이고, 이 밖의 공리에 의존하는 상수는 0개다. 부록의 ‘없음’은 해당 정리에 대해 Lean이 공리 의존성을 보고하지 않았다는 뜻이다.

## 2. 계단 규칙과 정리의 대응

**방향은 밀도 칸 `k`를 기준으로 읽는다.** 질문의 ‘2-down 1-up’에 대응하는 응답 규칙은 연속 두 정답이면 더 어렵게, 오답 한 번이면 더 쉽게 가는 것이다. 이 앱은 밀도가 높을수록 어렵기 때문에 두 정답은 `k + 1`, 한 오답은 `k − 1`이고, 이 방향을 ‘2-up 1-down’이라고 표기한다. `rpo`는 옥타브당 리플 수이며 1,000 milli-rpo가 1 rpo다.

| 검사 항목 | 모델에 정의한 규칙과 증명한 범위 | 주요 정리 (`SRD.` 접두어 생략) |
|---|---|---|
| 정답·오답 | 첫 정답은 같은 칸, 두 번째 연속 정답은 한 칸 어렵게, 오답 한 번은 한 칸 쉽게. 양 끝에서 범위 밖으로 가는 요청은 제자리에서 막힌다. | `step_first_correct`, `step_second_correct`, `step_wrong` |
| 단계 크기 변경 | 시작은 칸 1(0.176 rpo). 한 번의 이동은 최대 한 칸이고 도달하는 칸은 0–13이다. 실제 밀도는 근사 √2 간격의 표에서 읽는다. 반전 횟수에 따라 보폭이 바뀌는 규칙이나 인접값의 비가 정확히 √2라는 정리는 없다. | `step_k_near`, `step_k_le`, `run_bounds`, `densMilli_bounds` |
| 반전 횟수 | `isRev`는 직전 **실제** 이동과 방향이 바뀌어야 참이다. 반전 목록에는 이동 전 칸 하나만 추가할 수 있고, 경계에서 막히면 추가하지 않는다. `wonCfg`와 `endCheck`는 유효 시행 직후 반전 13회 도달을 유효 시행 상한보다 먼저 확인한다. | `isRev_moved`, `step_revs`, `step_blocked_no_rev` |
| 종료와 무효 시행 | 무효 시행은 칸·연속 정답·마지막 방향·반전·유효 수를 보존하고 기술 실패 수를 늘린다. 설정은 유효 시행 150회, 기술 실패 10회가 한도다. 160개 이상 응답을 주면 종료됨을 증명했다. 상한 때문에 반전 13회 전에 끝날 수도 있다. | `step_invalid`, `step_inv`, `run_ends` |
| 트랙 역치 | `threshold`는 반전 13회 미만이면 값을 내지 않고, 도달하면 마지막 8개 반전 밀도의 합과 개수를 반환한다. 역치 후보는 그 합을 8,000으로 나눈 산술평균이며, 최종 분류가 숫자의 채택 여부를 결정한다. Won 초기 상태에서 값이 나오면 개수는 8이고 평균은 0.125–11.314 rpo다. | `threshold_bounds`, `run_threshold_bounds`, `classify_thr`, `numeric_thr_bounds` |
| 숫자 역치의 채택 | 정상 종료의 분석 구간은 제5 반전 다음 유효 시행부터, 유효 상한 종료는 마지막 20개 유효 시행이다. `classify`는 최종 상태가 범위 안 완료일 때만 숫자를 반환한다. 수치 완료라면 분석 구간의 양 끝 막힘 횟수는 모두 0이다. | `firstStatus_cases`, `window_some`, `numeric_no_blocks` |
| 양 끝 막힘·범위 밖 | 완료 또는 유효 상한 상태에서 양 끝 모두 막히면 신뢰성 부족이다. 쉬운 끝만 막히고 Fisher에서 쉬운 끝의 성적 저하가 유의하면 신뢰성 부족, 그렇지 않고 하측 검정이 유의하면 하한 미만이다. 어려운 끝만 막히고 상측 검정이 유의하면 상한 초과다. 한쪽만 막혔고 신뢰성 부족과 범위 밖 조건이 모두 충족되지 않으면 끝 막힘 상태로 분류하고 숫자를 보류한다. | `both_ends_unreliable`, `refineCore_props`, `below_iff`, `above_iff`. 분기 정의는 `refineCore` |
| 판정의 통계 근거 | 쉬운 끝의 성적 저하는 단측 Fisher, 하·상한 확인은 목표 정답률 1/√2에서의 단측 이항 꼬리확률을 쓴다. 각각의 유의 기준은 엄격한 `p < 1/20`이다. 별도로 1/3 우연 정답률 검정은 표시용으로 쓰인다. | `fg_frac`, `fgSig_iff`, `belowSig_iff`, `aboveSig_iff`, `geThirdSig_iff` |
| 회기 역치 | 결정된 트랙이 6개 미만이면 잠정이다. 처음 6개의 결정된 트랙이 모두 숫자인 경우에만 확정하며, 확정값은 그 6개 역치의 산술평균이다. | `provisional_iff`, `final_iff`, `final_value` |
| 자극 수식 | Lean 정리가 다루는 것은 표적 위치, 레벨 흔들기 범위, 고정순서 검사의 밀도별 횟수다. 운반음·리플 포락선·합성 파형에 해당하는 정리는 없다. | `plan_targetPos`, `plan_roves`, `clinOrder_count`, `crun_complete_counts`. 수식별 범위는 다음 절 |

원문 정의의 위치는 `tools/lean/SRD/Stair.lean` 24–26행(밀도표), 52행(설정), 89–117행(방향·반전·종료), 154–159행(역치)과 `tools/lean/SRD/Classify.lean` 65–73행(분석 구간), 99–146행(경계 분류·숫자 반환)이다.

## 3. 실제 검사 앱과 자극 수식

실제 앱은 `index.html` 307–318행에서 검사 모듈을 불러온다. `js/app.js` 1025행에서 검사를 초기화하고, 1099–1101행에서 자극 합성을, 1207행에서 응답에 따른 계단 전이를 호출한다. 이에 대응하는 모델 함수는 `SRD.step`, `SRD.threshold`, `SRD.classify` 등이다. 앱이 처리하는 중복 시행 ID와 제시 칸 불일치(`js/staircase.js` 27–31행)는 Lean의 `Outcome` 입력에 들어 있지 않다. ZIP에는 이 대조에 필요한 JS 모듈 5개와 수식 참조용 `js/stim.js`가 들어 있다.

| 자극 요소 | 앱의 수식 또는 절차 | Lean에서 확인한 범위 |
|---|---|---|
| 운반음 주파수 | $f_i = 100\cdot 50^{i/N}$ Hz, $i=0,\ldots,N-1$. 옥타브 좌표 $X_i=i\log_2(50)/N$. $N$은 Won 적응 검사에서 200, Drennan 임상 검사에서 2,555다. | 주파수식에 대한 정리 없음. `js/stim.js:24–35`, `js/protocol.js:40,69` |
| 리플 포락선과 뒤집힘 | 상대 진폭(dB)은 $A_i=30\lvert\sin(\pi R X_i+\theta)\rvert+G(f_i)$, 선형 진폭은 $10^{A_i/20}$이다. $R$은 rpo 단위 밀도이며 $G$는 LTASS 이득(dB)이다. 표준 무늬의 위상은 Won에서 0, Drennan에서 매 시행 $2\pi u/2^{32}$이다. 표적 구간에만 이 값에 $\pi/2$를 더한다. | 포락선·LTASS·위상 차에 대한 정리 없음. `js/stim.js:39–43,63–66,92–98`, `js/analysis.js:15–23` |
| 파형·레벨 | 각 운반음의 위상 $\varphi_i$도 구간별 씨앗에서 뽑는다. $\sum_i 10^{A_i/20}\sin(2\pi f_i t+\varphi_i)$를 44,100 Hz에서 합성한다. 0.5초 파형의 경사 적용 전 RMS를 $-25+\text{rove}$ dBFS에 맞춘 뒤 앞뒤 각각 150 ms의 선형 경사를 적용해 Float32 PCM을 만든다. | 합성·RMS·경사·부동소수 표본·재생 장치 출력에 대한 정리 없음. `js/stim.js:14–19,45,58–89`, `js/protocol.js:19–25` |
| 시행에 넘기는 자극 매개변수 | 세 구간 중 한 곳을 표적 위치로 정하고 각 구간의 레벨 흔들기 값을 뽑는다. | `SRD.plan_targetPos`는 위치가 1–3임을, `SRD.drawRove_bounds`와 `SRD.plan_roves`는 흔들기가 −4…+4 dB의 정수 범위임을 증명한다. 균등분포를 보이는 명제는 없다. `SRD/Rng.lean:107–137` |

### 앱과 모델의 실행 대조

2026-11-04에 새로 빌드한 `crosscheck`와 실제 앱의 JS 함수에 동일한 입력 18,530줄을 넣었다. 난수, 시행 계획, 계단 전이, 역치, 상태 분류, 통계 판정을 포함한 12종의 출력 **177,818줄이 모두 일치했다**. 계단 응답열 3,014개와 같은 응답열의 분류 3,014개가 포함된다. 종류별로 한 줄을 바꾼 시험은 12종 모두 차이를 감지했다. 실행 명령과 종료 코드는 `verification/runs.json`, 종류별 비교 수는 `verification/cross-check.txt`에 있다.

모든 가능한 입력에서 JS와 Lean이 같은 결과를 낸다는 정리는 없다. 예를 들어 Lean 난수 모델은 기각 표집 100회 소진 시 0을 반환하지만 JS는 받아들일 값이 나올 때까지 반복한다. 끝점 판정에서도 Lean은 정수 쌍으로 $1/\sqrt2$ 검정을 계산하고 앱은 부동소수 연산을 사용한다. 참가자 중단, 위치 편향, 브라우저 재생과 실제 출력 장치의 동작은 이 증명의 대상 밖이다. `SRD/Rng.lean:41–50`, `js/rng.js:22–27`, `SRD/Classify.lean:15–16,99–103`, `js/analysis.js:337–346,387–393`.

## 4. 전체 정리별 명제와 공리

표의 각 행은 원본에 명시된 정리 한 개다. 모듈명과 행 번호는 `tools/lean/SRD/` 기준이고 모든 정리명 앞에 `SRD.`가 붙는다. 공리 열은 해당 정리에 `#print axioms`를 실행한 결과다.

### Stair.lean · 26개

| 행 | 정리 | 대응 규칙 | 증명한 명제 | 공리 |
|---:|---|---|---|---|
| 165 | `reqDir_cases` | 응답 규칙 | 요청 방향은 +1(어렵게), 0(유지), −1(쉽게) 중 하나다. | `propext` |
| 168 | `newK_le` | 단계 크기·범위 | 시작 칸이 상한 이하이고 요청 방향이 −1, 0, +1 중 하나이면 새 칸도 상한 이하다. | `propext` · `Quot.sound` |
| 172 | `newK_near` | 단계 크기·범위 | 요청 방향이 −1, 0, +1 중 하나이면 새 칸과 현재 칸의 차이는 최대 1칸이다. | `propext` · `Classical.choice` · `Quot.sound` |
| 176 | `step_k_le` | 단계 크기·범위 | 상한 이하의 칸에서 시작하면 어떤 시행 결과 뒤에도 칸이 상한을 넘지 않는다. | `propext` · `Quot.sound` |
| 182 | `step_k_near` | 단계 크기·범위 | 정답·오답·무효 어느 경우에도 한 시행의 칸 변화는 최대 1칸이다. | `propext` · `Classical.choice` · `Quot.sound` |
| 189 | `step_wrong` | 응답 규칙 | 최솟값이 0일 때 오답은 한 칸 쉽게 이동하고 연속 정답 수를 0으로 돌린다. 칸 0에서는 이동 요청이 막힌다. | `propext` |
| 196 | `step_second_correct` | 응답 규칙 | 정답 2개가 필요한 설정에서 연속 정답 수가 1일 때 정답이면 한 칸 어렵게 이동하고 연속 수를 0으로 돌린다. 이미 상한 이상이면 이동이 막힌다. | `propext` |
| 203 | `step_first_correct` | 응답 규칙 | 정답 2개가 필요한 설정에서 연속 정답 수가 0일 때 정답이면 칸을 유지하고 연속 수가 1이 된다. | `propext` |
| 208 | `step_invalid` | 측정 불가·무효 시행 | 기술적 실패 한 번은 칸, 연속 정답 수, 마지막 방향, 반전 목록, 유효 시행 수를 보존하고 기술적 실패 수를 1 늘린다. | `propext` |
| 213 | `isRev_moved` | 반전 횟수 | 반전 표시가 참이면 실제 이동이다. | `propext` |
| 217 | `moveOf_of_moved` | 반전 횟수 | 실제 이동이 참이면 기록의 이동 종류는 move다. | `propext` |
| 221 | `stepValid_revs` | 반전 횟수 | 유효 시행 뒤 반전 목록은 그대로이거나 이동 전 칸을 담은 기록 하나가 추가된다. 추가된 경우 실제 이동이고 반전 표시가 참이다. | `propext` |
| 232 | `step_revs` | 반전 횟수 | 어떤 시행 뒤에도 반전 목록은 그대로이거나 이동 전 칸을 담은 기록 하나가 추가된다. 추가된 경우 실제 이동이고 반전 표시가 참이다. | `propext` |
| 241 | `step_blocked_no_rev` | 반전 횟수 | 경계에서 막힌 이동은 반전 목록을 바꾸지 않는다. | `propext` |
| 254 | `init_inv` | 종료·측정 불가 | 유효 시행 상한과 기술적 실패 상한이 양수이면 초기 상태가 계수 불변식을 만족한다(시도=유효+실패, 진행 중에는 두 계수 모두 상한 미만). | `propext` |
| 257 | `endCheck_running` | 종료·측정 불가 | 유효 시행 직후 종료 판정이 ‘진행 중’이면 유효 시행 수는 상한 미만이다. | `propext` · `Quot.sound` |
| 265 | `step_attempts` | 종료·측정 불가 | 어떤 시행 결과이든 한 단계를 실행하면 시도 수가 1 늘어난다. | `propext` |
| 268 | `step_inv` | 종료·측정 불가 | 계수 불변식을 만족하는 진행 중 상태는 어떤 시행 결과를 한 번 처리해도 그 불변식을 보존한다. | `propext` · `Quot.sound` |
| 281 | `run_ends_aux` | 종료·측정 불가 | 계수 불변식이 성립하고 입력 응답 수와 기존 시도 수의 합이 두 상한의 합 이상이면 실행 후 상태는 진행 중일 수 없다. | `propext` · `Quot.sound` |
| 301 | `run_ends` | 종료·측정 불가 | Won 초기 상태에 160개 이상의 응답을 주면 실행은 종료 상태에 이른다. 종료 사유는 제한하지 않는다. | `propext` · `Quot.sound` |
| 306 | `densMilli_bounds` | 역치 계산 | 0~13번 칸에 대응하는 표의 밀도는 125~11314 milli-rpo다. | `propext` · `Quot.sound` |
| 311 | `sum_bounds` | 역치 계산 | 모든 반전 칸이 13 이하이면 밀도 합은 125×반전 수 이상이고 11314×반전 수 이하다(milli-rpo). | `propext` · `Quot.sound` |
| 321 | `threshold_bounds` | 역치 계산 | 모든 반전 칸이 13 이하이고 Won 역치가 있으면 사용 개수는 8이고 밀도 합은 125×8 이상 11314×8 이하이다. | `propext` · `Quot.sound` |
| 337 | `step_revs_le` | 반전·단계 범위 | 현재 칸과 이전 반전 칸들이 모두 13 이하이면 한 시행 뒤에도 모든 반전 칸은 13 이하다. | `propext` · `Quot.sound` |
| 347 | `run_bounds` | 반전·단계 범위 | 현재 칸과 이전 반전 칸들이 모두 13 이하이면 어떤 응답열을 실행한 뒤에도 최종 칸과 모든 반전 칸은 13 이하다. | `propext` · `Quot.sound` |
| 357 | `run_threshold_bounds` | 역치 계산 | Won 초기 상태에서 실행해 역치가 나온 경우 평균에 사용된 반전은 8개이고 밀도 합은 125×8~11314×8 milli-rpo다. 평균은 0.125~11.314 rpo다. | `propext` · `Quot.sound` |

### Classify.lean · 10개

| 행 | 정리 | 대응 규칙 | 증명한 명제 | 공리 |
|---:|---|---|---|---|
| 150 | `firstStatus_cases` | 측정 불가·분류 | 1차 분류는 기술적 실패, 유효 시행 상한, 범위 안 완료, 자료 부족 중 하나다. | `propext` |
| 155 | `window_some` | 측정 불가·분석 구간 | 분석 구간이 정의되면 1차 상태는 범위 안 완료 또는 유효 시행 상한이다. | `propext` |
| 165 | `refineCore_props` | 측정 불가·분류 | 1차 상태가 범위 밖·신뢰성 부족·경계 막힘 상태가 아니면, 하한 미만은 판정 활성·쉬운 끝만 막힘·Fisher 비유의·하측 유의와 동치이고, 상한 초과는 활성·어려운 끝만 막힘·상측 유의와 동치다. 활성 시 양 끝 막힘은 신뢰성 부족이며, 원상태를 유지했다면 비활성 또는 두 끝 모두 안 막힌 경우다. | `propext` |
| 176 | `refineCore_complete` | 측정 불가·분류 | 경계 판정 결과가 범위 안 완료이면 처음부터 범위 안 완료였고, 경계 판정이 비활성이거나 양 끝 모두 막힘이 없다. | `propext` |
| 181 | `numeric_no_blocks` | 측정 불가·범위 안 완료 | 최종 분류가 범위 안 완료이고 경계 통계가 있으면 분석 구간의 쉬운 끝·어려운 끝 막힘 수가 모두 0이다. | `propext` |
| 203 | `both_ends_unreliable` | 측정 불가·양 끝 막힘 | 1차 상태가 범위 안 완료 또는 유효 시행 상한이고 분석 구간의 양 끝 막힘 수가 각각 양수이면 ‘신뢰성 부족/양 끝 막힘’으로 분류한다. | `propext` |
| 208 | `below_iff` | 측정 불가·하한 미만 | 하한 미만 분류와 다음 조건의 동치를 보인다. 1차 상태는 완료 또는 유효 시행 상한이고, 쉬운 끝만 막혔으며, 쉬운 끝이 더 나쁘다는 Fisher 판정은 거짓이고 쉬운 끝 하측 검정은 참이다. | `propext` |
| 220 | `above_iff` | 측정 불가·상한 초과 | 상한 초과 분류와 다음 조건의 동치를 보인다. 1차 상태는 완료 또는 유효 시행 상한이고, 어려운 끝만 막혔으며 어려운 끝 상측 검정이 참이다. | `propext` |
| 232 | `classify_thr` | 역치 계산 | 최종 분류가 수치 역치 (합, 개수)를 반환하면 계단의 역치 함수도 같은 쌍을 반환한다. | 없음 |
| 238 | `numeric_thr_bounds` | 역치 계산·분류 | Won 초기 상태에서 얻은 시행과 상태로 분류해 수치 역치가 나오면 개수는 8, 밀도 합은 125×8~11314×8 milli-rpo로 평균은 0.125~11.314 rpo다. | `propext` · `Quot.sound` |

### Summary.lean · 4개

| 행 | 정리 | 대응 규칙 | 증명한 명제 | 공리 |
|---:|---|---|---|---|
| 51 | `provisional_iff` | 회기 역치·측정 불가 | 잠정 결과인 것과 결정된 트랙이 6개 미만인 것은 동치다. | `propext` · `Classical.choice` · `Quot.sound` |
| 64 | `final_iff` | 회기 역치 | 확정 상태인 것과 결정된 트랙이 6개 이상이고 그중 앞 6개가 모두 수치 역치인 것은 동치다. | `propext` · `Classical.choice` · `Quot.sound` |
| 83 | `final_value` | 회기 역치 | 회기 요약이 수치 값을 반환하면 그 값은 앞쪽의 결정된 트랙 6개의 역치 산술평균이다. | `propext` · `Classical.choice` · `Quot.sound` |
| 100 | `mixed_has_num` | 회기 역치·측정 불가 | 혼합이면 앞쪽의 결정된 트랙 6개가 모두 수치인 것도, 모두 쉬운 끝 계열인 것도, 모두 어려운 끝 계열인 것도 아니다. | `propext` · `Classical.choice` · `Quot.sound` |

### Rng.lean · 11개

| 행 | 정리 | 대응 규칙 | 증명한 명제 | 공리 |
|---:|---|---|---|---|
| 50 | `intF_lt` | 시행 난수 | n > 0이면 기각 표집의 남은 시도 수와 초기 난수 상태에 관계없이 반환하는 자연수가 n보다 작다. | `propext` · `Quot.sound` |
| 59 | `int_lt` | 시행 난수 | n > 0이면 최대 100회 시도하는 난수 함수 Xo.int의 결과는 0 이상 n 미만이다. | `propext` · `Quot.sound` |
| 122 | `drawRove_bounds` | 자극 매개변수 | 한 구간의 레벨 흔들기 값은 −4 이상 +4 이하의 정수(dB)다. | `propext` · `Classical.choice` · `Quot.sound` |
| 128 | `plan_targetPos` | 자극 매개변수 | 시행 계획에서 표적 구간의 위치는 1, 2, 3 중 하나다. | `propext` · `Classical.choice` · `Quot.sound` |
| 134 | `plan_roves` | 자극 매개변수 | 시행 계획의 흔들기 목록에 포함된 모든 정수 값은 −4…+4 dB 범위다. | `propext` · `Classical.choice` · `Quot.sound` |
| 144 | `swapL_length` | 임상 자극 순서 | 자연수 목록의 두 위치에 swapL을 적용하면 목록 길이가 보존된다. | `propext` |
| 147 | `swapL_perm` | 임상 자극 순서 | 두 인덱스가 모두 목록의 범위 안이면 그 두 위치를 교환한 목록은 원래 목록의 순열이다. | `propext` · `Quot.sound` |
| 161 | `fy_perm` | 임상 자극 순서 | 시작 인덱스 m이 목록 길이보다 작으면 Fisher–Yates로 섞은 결과는 원래 목록의 순열이다. | `propext` · `Quot.sound` |
| 178 | `baseOrder_count` | 임상 자극 순서 | 섞기 전 임상 자극 목록에서 각 밀도 칸 0…11은 정확히 여섯 번 나온다. | `propext` · `Quot.sound` |
| 182 | `baseOrder_length` | 임상 자극 순서 | 밀도 칸 12개를 여섯 번씩 넣은 기본 임상 목록의 길이는 72다. | 없음 |
| 185 | `clinOrder_count` | 임상 자극 순서 | 어떤 난수 상태에서 시작해도 섞은 임상 목록의 길이는 72이며 각 밀도 칸 0…11이 정확히 여섯 번씩 나온다. | `propext` · `Quot.sound` |

### Clinical.lean · 8개

| 행 | 정리 | 대응 규칙 | 증명한 명제 | 공리 |
|---:|---|---|---|---|
| 60 | `cstep_invalid_same` | 고정순서 임상 검사·무효 | 무효 시행은 순서 위치를 유지하고 현재 위치의 밀도를 기록하며 유효 표시는 거짓이다. | `propext` |
| 65 | `cstep_valid_slot` | 고정순서 임상 검사·유효 | 유효 시행은 현재 순서 위치의 밀도를 기록하고 유효 표시를 참으로 두며 다음 위치로 한 칸 진행한다. | `propext` |
| 71 | `crun_inv` | 고정순서 임상 검사·계수 | 처음에 유효 수=순서 위치, 시도 수=유효 수+기술적 실패 수이면 어떤 응답열을 실행한 뒤에도 두 등식이 유지된다. | `propext` · `Quot.sound` |
| 87 | `cstep_cinv` | 고정순서 임상 검사·종료 | 진행 중 상태가 위치 불변식(진행 중이면 위치<목표, 완료이면 위치=목표)을 만족하면 한 시행 뒤에도 성립한다. | `propext` · `Quot.sound` |
| 98 | `crun_cinv` | 고정순서 임상 검사·종료 | 위치 불변식(진행 중이면 위치<목표, 완료이면 위치=목표)을 만족하는 상태는 어떤 응답열을 실행해도 이 성질을 보존한다. | `propext` · `Quot.sound` |
| 108 | `take_drop_succ` | 고정순서 임상 검사·목록 보조 | 목록에 n번째 원소가 있으면 n개를 건너뛰어 m+1개 취한 목록은 그 n번째 원소와 그 다음부터 최대 m개 취한 목록을 이은 것이다(0부터 셈). | `propext` |
| 114 | `crun_valid_ks` | 고정순서 임상 검사·제시 순서 | 위치 불변식이 성립하고 목표 시행 수가 순서표 길이 이하이면 유효 밀도열은 초기 위치부터 실제 전진한 길이만큼의 순서표와 같다. 최종 위치는 초기 위치 이상이다. | `propext` · `Quot.sound` |
| 148 | `crun_complete_counts` | 고정순서 임상 검사·밀도 횟수 | 목표 72회·기술적 실패 상한 10인 임상 순서가 초기 상태에서 완료되면, 0~11번 밀도가 각각 정확히 6회씩 유효 시행에 나온다. | `propext` · `Quot.sound` |

### Exact.lean · 17개

| 행 | 정리 | 대응 규칙 | 증명한 명제 | 공리 |
|---:|---|---|---|---|
| 22 | `natCast_pow` | 우연 정답률 표시 · 1/3 이항검정 | 자연수 거듭제곱을 유리수로 변환하면 밑을 유리수로 변환해 같은 지수로 거듭제곱한 값과 같다. | `propext` · `Classical.choice` · `Quot.sound` |
| 26 | `three_pow_pos` | 우연 정답률 표시 · 1/3 이항검정 | 모든 자연수 m에 대해 유리수 3ᵐ은 양수이다. | `propext` · `Classical.choice` · `Quot.sound` |
| 29 | `third_pows` | 우연 정답률 표시 · 1/3 이항검정 | 자연수 j,m에 대해 (1/3)ʲ(2/3)ᵐ = 2ᵐ/3ʲ⁺ᵐ이다. | `propext` · `Classical.choice` · `Quot.sound` |
| 65 | `geThirdDen_pos` | 우연 정답률 표시 · 1/3 이항검정 | 1/3 이항검정의 분모 3ⁿ은 양수이다. | 없음 |
| 68 | `geThird_frac` | 우연 정답률 표시 · 1/3 이항검정 | 모델의 정수 분자와 분모로 만든 분수는 성공확률 1/3인 이항분포의 상측 꼬리합 P(X ≥ k)과 같다. | `propext` · `Classical.choice` · `Quot.sound` |
| 86 | `geThirdSig_iff` | 우연 정답률 표시 · 1/3 이항검정 | 모델의 1/3 이항 유의 판정이 참인 것과 상측 꼬리확률이 1/20 미만인 것은 동치이다. | `propext` · `Classical.choice` · `Quot.sound` |
| 91 | `sum_choose_two_pow` | 우연 정답률 표시 · 1/3 이항검정 | j = 0,…,n에 대한 C(n,j)·2ⁿ⁻ʲ의 합은 3ⁿ이다. | `propext` · `Classical.choice` · `Quot.sound` |
| 129 | `geThirdNum_eq` | 우연 정답률 표시 · 1/3 이항검정 | 1/3 이항검정 분자는 k ≤ j ≤ n에서 C(n,j)·2ⁿ⁻ʲ를 더한 값이다. | `propext` · `Classical.choice` · `Quot.sound` |
| 135 | `geThirdNum_le` | 우연 정답률 표시 · 1/3 이항검정 | 모든 n,k에서 1/3 이항검정 분자는 분모 이하이다. | `propext` · `Classical.choice` · `Quot.sound` |
| 139 | `geThirdNum_pos` | 우연 정답률 표시 · 1/3 이항검정 | k ≤ n이면 1/3 이항검정 분자는 양수이다. | `propext` · `Classical.choice` · `Quot.sound` |
| 146 | `geThirdNum_zero` | 우연 정답률 표시 · 1/3 이항검정 | k = 0이면 1/3 이항검정 분자가 분모와 같아 꼬리확률은 1이다. | `propext` · `Classical.choice` · `Quot.sound` |
| 183 | `fgSpecM_eq` | 측정 불가 판정의 근거 · Fisher 단측검정 | 고정 주변합에서 Fisher 상측 꼬리합은 a ≤ x ≤ c₁인 표의 경우의 수를 더해 C(r₁+r₂,c₁)로 나눈 값이다. | `propext` · `Classical.choice` · `Quot.sound` |
| 192 | `fg_window` | 측정 불가 판정의 근거 · Fisher 단측검정 | a ≤ min(r₁,c₁)이면 상측 꼬리 분자의 합은 x = a,…,min(r₁,c₁) 구간만 더해 계산할 수 있다. | `propext` · `Quot.sound` |
| 211 | `fgSpec_degenerate` | 측정 불가 판정의 근거 · Fisher 단측검정 | 행합이나 열합 중 하나가 0인 2×2 표이면 단측 Fisher 명세값은 1이다. | `propext` · `Classical.choice` · `Quot.sound` |
| 240 | `fg_frac` | 측정 불가 판정의 근거 · Fisher 단측검정 | 모든 자연수 2×2 표에서 모델이 계산한 분수는 고정 주변합의 초기하 상측 꼬리확률 P(X ≥ a)와 같다. 주변합이 0인 경우도 포함한다. | `propext` · `Classical.choice` · `Quot.sound` |
| 256 | `fgDen_pos` | 측정 불가 판정의 근거 · Fisher 단측검정 | 모든 자연수 2×2 표에서 모델의 Fisher 검정 분모가 양수이다. | `propext` · `Classical.choice` · `Quot.sound` |
| 263 | `fgSig_iff` | 측정 불가 판정의 근거 · Fisher 단측검정 | 모델의 단측 Fisher 유의 판정이 참인 것과 명세의 꼬리확률이 1/20 미만인 것은 동치이다. | `propext` · `Classical.choice` · `Quot.sound` |

### Target.lean · 15개

| 행 | 정리 | 대응 규칙 | 증명한 명제 | 공리 |
|---:|---|---|---|---|
| 63 | `powList_getD` | 측정 불가 판정의 근거 · 1/√2 목표 정답률 | j ≤ N이면 ℤ[√2] 원소 x의 거듭제곱 목록에서 j번째로 읽은 값은 xʲ이다. | `propext` · `Quot.sound` |
| 67 | `zsum_congr` | 측정 불가 판정의 근거 · 1/√2 목표 정답률 | 두 ℤ[√2] 수열의 처음 n개 항이 각각 같으면 그 합도 같다. | `propext` · `Quot.sound` |
| 83 | `term_with` | 측정 불가 판정의 근거 · 1/√2 목표 정답률 | j ≤ n일 때 파스칼 행과 거듭제곱 배열로 계산한 항은 C(n,j)(√2)ʲ(2−√2)ⁿ⁻ʲ를 표현하는 정수 쌍과 같다. | `propext` · `Classical.choice` · `Quot.sound` |
| 88 | `tailLeWith_eq` | 측정 불가 판정의 근거 · 1/√2 목표 정답률 | 미리 만든 파스칼 행과 거듭제곱 배열을 이용해 계산한 하측 꼬리합은 직접 정의한 tailLe와 같다. | `propext` · `Classical.choice` · `Quot.sound` |
| 95 | `tailGeWith_eq` | 측정 불가 판정의 근거 · 1/√2 목표 정답률 | 미리 만든 파스칼 행과 거듭제곱 배열을 이용해 계산한 상측 꼬리합은 직접 정의한 tailGe와 같다. | `propext` · `Classical.choice` · `Quot.sound` |
| 105 | `tailLe_eq_tailLeFast` | 측정 불가 판정의 근거 · 1/√2 목표 정답률 | 하측 꼬리합 함수 tailLe와 최적화한 tailLeFast는 모든 입력에서 같다. | `propext` · `Classical.choice` · `Quot.sound` |
| 108 | `tailGe_eq_tailGeFast` | 측정 불가 판정의 근거 · 1/√2 목표 정답률 | 상측 꼬리합 함수 tailGe와 최적화한 tailGeFast는 모든 입력에서 같다. | `propext` · `Classical.choice` · `Quot.sound` |
| 138 | `intCast_pos_iff` | 측정 불가 판정의 근거 · 1/√2 목표 정답률 | 정수 A를 유리수로 변환한 값이 양수인 것과 정수 A가 양수인 것은 동치이다. | `propext` · `Classical.choice` · `Quot.sound` |
| 142 | `intCast_neg_iff` | 측정 불가 판정의 근거 · 1/√2 목표 정답률 | 정수 A를 유리수로 변환한 값이 음수인 것과 정수 A가 음수인 것은 동치이다. | `propext` · `Classical.choice` · `Quot.sound` |
| 146 | `sq_div` | 측정 불가 판정의 근거 · 1/√2 목표 정답률 | 유리수 y ≠ 0이면 (x/y)² = x²/y²이다. | `propext` · `Classical.choice` · `Quot.sound` |
| 148 | `negZ2_iff` | 측정 불가 판정의 근거 · 1/√2 목표 정답률 | 정수 쌍 (A,B)의 음수 판정 함수 negZ2는 A+B√2의 부호를 유리수 자름으로 정의한 isNegQ와 동치이다. | `propext` · `Classical.choice` · `Quot.sound` |
| 207 | `isNegQ_scale` | 측정 불가 판정의 근거 · 1/√2 목표 정답률 | 양의 유리수 c를 두 계수 a,b에 곱해도 a+b√2의 음수 여부는 같다. | `propext` · `Classical.choice` · `Quot.sound` |
| 244 | `lt_twentieth_iff` | 측정 불가 판정의 근거 · 1/√2 목표 정답률 | D > 0이면 (A+B√2)/D < 1/20인 것과 정수 쌍 (20A−D,20B)이 음수를 나타내는 것은 동치이다. | `propext` · `Classical.choice` · `Quot.sound` |
| 263 | `belowSig_iff` | 측정 불가 판정의 근거 · 1/√2 목표 정답률 | 목표 정답률 1/√2에서 belowSig가 참인 것과 정수 쌍으로 계산한 하측 꼬리합 tailLe/2ⁿ이 1/20 미만인 것은 동치이다. | `propext` · `Classical.choice` · `Quot.sound` |
| 269 | `aboveSig_iff` | 측정 불가 판정의 근거 · 1/√2 목표 정답률 | 목표 정답률 1/√2에서 aboveSig가 참인 것과 정수 쌍으로 계산한 상측 꼬리합 tailGe/2ⁿ이 1/20 미만인 것은 동치이다. | `propext` · `Classical.choice` · `Quot.sound` |

### Arith.lean · 34개

| 행 | 정리 | 대응 규칙 | 증명한 명제 | 공리 |
|---:|---|---|---|---|
| 33 | `sumTo_zero` | 검정 공통 · 유한합 | 자연수 수열에서 처음 0개 항의 합은 0이다. | 없음 |
| 34 | `sumTo_succ` | 검정 공통 · 유한합 | 자연수 수열에서 처음 n+1개 항의 합은 처음 n개 항의 합에 f(n)을 더한 값이다. | 없음 |
| 35 | `sumQ_zero` | 검정 공통 · 유한합 | 유리수 수열에서 처음 0개 항의 합은 0이다. | `propext` · `Classical.choice` · `Quot.sound` |
| 36 | `sumQ_succ` | 검정 공통 · 유한합 | 유리수 수열에서 처음 n+1개 항의 합은 처음 n개 항의 합에 f(n)을 더한 값이다. | `propext` · `Classical.choice` · `Quot.sound` |
| 37 | `sumZ_zero` | 검정 공통 · 유한합 | 정수 수열에서 처음 0개 항의 합은 0이다. | 없음 |
| 38 | `sumZ_succ` | 검정 공통 · 유한합 | 정수 수열에서 처음 n+1개 항의 합은 처음 n개 항의 합에 f(n)을 더한 값이다. | 없음 |
| 40 | `sumTo_congr` | 검정 공통 · 유한합 | 두 자연수 수열의 처음 n개 항이 각각 같으면 그 합도 같다. | `propext` · `Quot.sound` |
| 46 | `sumQ_congr` | 검정 공통 · 유한합 | 두 유리수 수열의 처음 n개 항이 각각 같으면 그 합도 같다. | `propext` · `Classical.choice` · `Quot.sound` |
| 52 | `sumTo_add` | 검정 공통 · 유한합 | 두 자연수 수열을 항별로 더한 뒤 합하면 각 수열을 따로 합해 더한 값과 같다. | `propext` · `Quot.sound` |
| 58 | `sumTo_le` | 검정 공통 · 유한합 | 처음 n개 항에서 각각 f(x) ≤ g(x)이면 f의 합은 g의 합 이하이다. | `propext` · `Quot.sound` |
| 67 | `sumTo_eq_zero` | 검정 공통 · 유한합 | 처음 n개 항이 모두 0인 자연수 수열의 해당 합은 0이다. | `propext` · `Quot.sound` |
| 72 | `le_sumTo` | 검정 공통 · 유한합 | x < n이면 자연수 항 f(x)는 처음 n개 항의 합 이하이다. | `propext` · `Quot.sound` |
| 83 | `sumTo_split` | 검정 공통 · 유한합 | 처음 m+n개 자연수 항의 합은 앞 m개 항의 합과 이어지는 n개 항의 합을 더한 값이다. | `propext` · `Quot.sound` |
| 90 | `sumTo_succ'` | 검정 공통 · 유한합 | 처음 n+1개 자연수 항의 합은 첫 항 f(0)과 그 뒤 n개 항의 합을 더한 값이다. | `propext` · `Quot.sound` |
| 99 | `sumQ_div` | 검정 공통 · 유한합 | 각 유리수 항을 같은 d로 나눈 뒤 합한 값은 전체 합을 d로 나눈 값과 같다. | `propext` · `Classical.choice` · `Quot.sound` |
| 105 | `natCast_sumTo` | 검정 공통 · 유한합 | 자연수 합을 유리수로 변환하면 각 항을 유리수로 변환해 더한 값과 같다. | `propext` · `Classical.choice` · `Quot.sound` |
| 113 | `div_le_div_iff_of_pos` | 검정 공통 · 분수 비교 | 양의 유리수 d에 대해 a/d ≤ b/d와 a ≤ b는 동치이다. | `propext` · `Classical.choice` · `Quot.sound` |
| 124 | `div_lt_div_iff_of_pos` | 검정 공통 · 분수 비교 | 양의 유리수 d에 대해 a/d < b/d와 a < b는 동치이다. | `propext` · `Classical.choice` · `Quot.sound` |
| 128 | `frac_lt_twentieth` | 검정 공통 · 분수 비교 | 자연수 분자 n과 양의 자연수 분모 d에 대해 n/d < 1/20과 20n < d는 동치이다. | `propext` · `Classical.choice` · `Quot.sound` |
| 137 | `natCast_ite` | 검정 공통 · 분수 비교 | 자연수 조건식의 결과를 유리수로 바꾸는 것은 같은 조건으로 두 유리수 값 중 하나를 선택하는 것과 같다. | `propext` |
| 142 | `ite_div_eq` | 검정 공통 · 분수 비교 | 조건이 참이면 a/d, 거짓이면 0인 유리수는 조건에 따라 자연수 a 또는 0을 고른 뒤 d로 나눈 값과 같다. | `propext` · `Classical.choice` · `Quot.sound` |
| 156 | `choose_zero_right` | 검정 공통 · 이항계수 | 모든 자연수 n에 대해 C(n,0) = 1이다. | 없음 |
| 157 | `choose_zero_succ` | 검정 공통 · 이항계수 | 모든 자연수 k에 대해 C(0,k+1) = 0이다. | 없음 |
| 158 | `choose_succ_succ` | 검정 공통 · 이항계수 | 파스칼 점화식 C(n+1,k+1) = C(n,k) + C(n,k+1)이 성립한다. | 없음 |
| 160 | `choose_eq_zero_of_lt` | 검정 공통 · 이항계수 | n < k이면 C(n,k) = 0이다. | `propext` · `Quot.sound` |
| 168 | `choose_self` | 검정 공통 · 이항계수 | 모든 자연수 n에 대해 C(n,n) = 1이다. | `propext` · `Quot.sound` |
| 172 | `choose_pos` | 검정 공통 · 이항계수 | k ≤ n이면 C(n,k)는 양수이다. | `propext` · `Quot.sound` |
| 181 | `vandermonde` | 검정 공통 · 이항계수 | x = 0,…,c에 대한 C(r₁,x)·C(r₂,c−x)의 합은 C(r₁+r₂,c)이다. | `propext` · `Quot.sound` |
| 216 | `zipWith_add_getD` | 검정 공통 · 이항계수 | 같은 길이의 자연수 목록을 항별로 더한 뒤 i번째 값을 읽으면 각 목록의 i번째 값을 더한 결과와 같다. 범위 밖의 값은 0이다. | `propext` · `Classical.choice` · `Quot.sound` |
| 226 | `append_zero_getD` | 검정 공통 · 이항계수 | 자연수 목록 끝에 0을 붙여도 범위 밖 기본값을 0으로 읽는 모든 위치의 값은 같다. | `propext` · `Classical.choice` · `Quot.sound` |
| 232 | `pascalRow_length` | 검정 공통 · 이항계수 | 파스칼 삼각형 n번째 행에는 항이 n+1개 있다. | `propext` · `Quot.sound` |
| 240 | `pascalRow_getD` | 검정 공통 · 이항계수 | 파스칼 삼각형 n번째 행의 x번째 값은 C(n,x)이고 범위 밖에서 기본값 0을 사용한다. | `propext` · `Classical.choice` · `Quot.sound` |
| 257 | `arr_getD` | 검정 공통 · 이항계수 | 목록을 배열로 바꿔 같은 인덱스와 기본값으로 읽으면 목록에서 읽은 값과 같다. | `propext` |
| 263 | `choose_eq_chooseFast` | 검정 공통 · 이항계수 | 재귀식 choose와 파스칼 행을 사용하는 chooseFast는 모든 입력에서 같다. | `propext` · `Classical.choice` · `Quot.sound` |
