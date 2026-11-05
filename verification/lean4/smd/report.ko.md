# 와우SMD Lean 4 검증 보고서

**검증 대상은 검사 절차를 옮겨 쓴 별도 Lean 모델이다.** Lean은 모델 안에서 응답을 하나 적용했을 때의 변화, 임의의 응답열에 대한 종료 조건과 역치 범위, 숫자 역치를 보고할 수 있는 조건 등을 증명한다. 실제 JavaScript 검사 앱과의 연결은 두 구현에 같은 입력을 넣고 출력을 비교한 실행 시험이다. 소리 합성식과 재생 파형에는 Lean 정리가 없다.

검증일은 2026-11-04이며, 대조한 앱의 버전은 `1.1.1 (2026-11-02)`이다. 아래의 깊이 `h`는 0.5 dB 단위 정수다. Won 계단은 20 dB에서 시작하고 범위는 0–60 dB이다.

## 규칙별로 무엇을 증명했나

정리 이름의 접두사는 모두 `SMD.`이다. 전체 158개 정리의 명제·소스 줄·공리는 [정리 대응표](정리-대응표.md)에 있다.

| 규칙 | 정의 또는 대표 정리 | 증명 범위 |
|---|---|---|
| 2-down 1-up | `step_first_correct`, `step_second_correct`, `step_wrong` | 첫 정답은 깊이를 유지한다. 연속 두 번째 정답은 한 단계 낮추고 오답 한 번은 한 단계 높인다. 두 경우 모두 연속 정답 수를 0으로 돌린다. 이미 해당 경계이면 이동이 막힌다. |
| 단계 크기 변경 | `step_size_rule`, `wonCfg_switchFrom`, `run_no_clamp` | **이번 이동에서 생기는 반전까지** 센다. 반전 수가 4 미만이면 2 dB, 제4반전을 기록하는 이동부터 0.5 dB다. 초기 상태에서 실제로 이동한 시행은 요청한 폭만큼 이동한다. |
| 반전 횟수·종료 | 정의 `isRev`, `newRevs`, `endCheck` / 정리 `step_revs`, `step_blocked_no_rev`, `run_ends` | 직전 실제 이동과 방향이 달라져야 반전이다. 한 번에 최대 한 건을 추가하고 이동 **전** 깊이를 기록한다. 경계에서 막히면 반전 수가 늘지 않는다. 설정은 14반전이 목표다. 유효 200회 또는 기술적 실패 10회로도 끝나며, 210개 이상의 응답을 주면 종료 상태임이 증명돼 있다. |
| 트랙 역치 | 정의 `threshold` / 정리 `run_threshold_bounds`, `classify_thr`, `numeric_thr_bounds` | 14반전 미만이면 원시 역치가 없다. 14반전에 도달하면 정의가 마지막 10개 반전의 깊이 합과 개수를 반환한다. 초기 상태에서 값이 있을 때 개수는 10, 합은 1,200 이하이다. 보고된 숫자는 그 쌍과 같고, dB 값은 **합/20**으로 0–60이다. |
| 숫자를 보고할 조건 | `numeric_iff` / 정의 `classify` | 분석 구간이 있는 재판정에서 숫자 상태의 필요충분조건은 최초 완료, 0 dB 경보 없음, 구간 안 천장·바닥 막힘 모두 0회, 구간 정답률이 목표보다 낮다는 유의한 증거 없음이다. 최종 상태가 숫자 상태일 때만 `thr`를 반환한다. |
| 신뢰성 부족·측정 범위 초과 | `zero_alarm_unreliable`, `both_ends_unreliable`, `above_iff` | 최초 완료 또는 유효 시행 상한에서 0 dB 경보가 있으면 신뢰성 부족이다. 경보가 없고 양끝 모두 막혀도 신뢰성 부족이다. **>60 dB** 판정은 같은 최초 상태에서 경보가 없고 천장만 막히며, 천장이 낮은 깊이보다 나쁘다는 Fisher 유의 결과가 없고 천장 정답률이 목표보다 낮다는 유의 결과가 있을 때와 동치이다. |
| 기술적 실패·경계·자료 부족 | `step_invalid`, `firstStatus_cases`, `refineCore_cases` / 정의 `refineCore` | 무효 시행은 깊이·반전·유효 횟수 등을 보존하고 기술적 실패 횟수를 1 늘린다. 초기 분류는 기술적 실패·유효 상한·완료·자료 부족 중 하나다. 경계 근처, 분석 구간에서 수렴 미확인 등 세부 결과는 분기 정의에서 확인할 수 있다. `refineCore_cases`는 일곱 조건의 128개 조합에서 숫자 판정, 범위 초과, 두 종류의 신뢰성 부족에 관한 결론을 증명한다. |
| 반복 측정의 역치 | `third_needed_iff`, `two_final_close`, `final_all_num` | 숫자 트랙 두 개의 차이가 **3 dB를 초과**할 때 셋째를 요구한다. 정확히 3 dB이면 앞 둘로 확정한다. 확정값은 사용한 숫자 트랙 2개 또는 3개의 산술평균이다. |
| 측정 불가 판정에 쓰는 통계식 | `geThirdSig_iff`, `fgSig_iff`, `belowSig_iff` | 우연 정답률 1/3에 대한 이항 검정과 한쪽 Fisher 검정의 정수 판정이 정확한 꼬리확률 < 1/20과 동치다. 목표 정답률 1/√2의 아래쪽 꼬리는 정수 쌍과 유리수 비교로 판정한다. 이 정리들은 응답 데이터의 판정 기준을 다룬다. |
| 자극 제시 계획·QSMD 순서 | `plan_targetPos`, `plan_roves`, `qsmdOrder_each_once`, `crun_complete` | 모델에서 표적 위치는 세 구간 중 하나이고 구간별 음량 변화는 −2~+2 dB다. QSMD가 완료되면 60개 파일 번호가 한 번씩, 10개 밀도×깊이 조합이 여섯 번씩 나타난다. |
| Won 음향 자극 수식 | 해당 정리 없음 | 운반음 주파수, 스펙트럼 포락선, 정현파 합, RMS 보정, 램프, 최종 PCM 표본은 Lean 증명 범위 밖이다. |

완료 트랙의 분석 구간은 제4반전 다음 유효 시행부터 끝까지다. 유효 시행 상한으로 끝난 경우는 마지막 최대 20개의 유효 시행을 쓴다. 0 dB 경보는 그 깊이에서 모은 **전체 유효 시행**을 대상으로 우연 정답률 1/3보다 높다는 한쪽 검정의 p값이 0.05 미만일 때 켜진다.

## 실제 앱과 Lean의 경계

| 실제 앱 소스 | 대응하는 모델 또는 시험 |
|---|---|
| `js/protocol.js`, `js/staircase.js` | 절차 상수, 계단 상태 갱신, 반전 기록, 역치 계산을 `SMD/Stair.lean`에 옮겼다. |
| `js/analysis.js` | `SMD/Classify.lean`, `Summary.lean`, `Const.lean`은 트랙·회기·QSMD 판정을 모델링한다. `Exact.lean`, `Target.lean`은 관련 통계식을 다룬다. 앱의 참가자 중단, 자리 편향 순열검정, 화면 흐름은 별도 영역이다. |
| `js/rng.js` | 모델의 `Xo.int`는 기각 표집 시 최대 100번 뽑고 한도를 소진하면 0을 돌려준다. JavaScript의 `int`는 수락할 때까지 반복한다. `int_lt`의 결론은 추출값의 범위이다. 모든 씨앗에서 두 구현이 동등하다는 증명은 없다. |
| `js/stim.js` 21–40, 61–94행 | Won 자극에서 `xᵢ = 4i/2554`, `fᵢ = (1000·2^(−1.5))·2^xᵢ`, `D = h/2` dB이다. 포락선 `Eᵢ = (D/2) sin(2πΩxᵢ + Φ)`를 선형 진폭 `aᵢ = 10^(Eᵢ/20)`으로 바꾸고 `Σᵢ aᵢ sin(2πfᵢt + φᵢ)`를 계산해 RMS 이득과 램프를 적용한다. 이 코드의 수치 오차, 재생 장치 출력, QSMD 녹음 파일의 실제 파형에 대응하는 Lean 정리는 없다. |

## 실행 결과와 공리

원본의 빌드 캐시를 가져오지 않고 Windows에서 `leanprover/lean4:v4.24.0`과 Lake 5.0.0을 사용했다. `lake-manifest.json`의 외부 패키지 목록은 비어 있다.

| 명령 | 종료 코드 | 결과 |
|---|---:|---|
| `lake build` | 0 | `Build completed successfully (23 jobs).` 경고와 오류 0개. 기본 대상은 라이브러리 `SMD`와 실행 파일 `crosscheck`이다. [전체 출력](lake-build.txt) |
| `lake env lean PrintAxioms.lean` | 0 | 소스에서 이름을 붙인 정리 158개에 대해 `#print axioms`를 직접 실행했다. [정리별 원문 출력](print-axioms.txt) |
| `lake env lean MyAudit.lean` | 0 | `SMD`의 전체 상수 1,252개, 그중 정리 529개, 공리 선언 0개, 비표준 공리에 의존하는 선언 0개. |
| `lake env lean scratch/T1.lean` | 0 | 기본 빌드 대상 밖에 있는 익명 예제 3개도 검사했다. 출력은 비어 있다. |

158개는 사람이 소스에 이름을 붙인 정리 수다. 환경 감사의 529개에는 Lean이 만든 보조 정리도 포함된다. 원본 12개 `.lean` 파일에서 증명 자리를 채우는 `sorry` 또는 `admit`는 발견되지 않았다. `MyAudit.lean` 9행의 `sorryAx`, 11행과 41행의 `sorry`는 감사 방법을 설명하는 주석이다. 158개 정리 출력과 1,252개 선언의 공리 합집합에도 `sorryAx`는 없다.

| 직접 출력된 공리 의존성 | 원본 정리 수 |
|---|---:|
| 없음 | 19 |
| `propext` | 34 |
| `propext`, `Quot.sound` | 41 |
| `propext`, `Classical.choice`, `Quot.sound` | 64 |

## JavaScript 대조 결과

2026-11-04에 앱 버전 1.1.1에서 가져온 다섯 JS 파일과 이번에 빌드한 Lean 실행 파일을 원본 대조기로 실행했다. 입력 17,875줄에서 얻은 출력 **194,863줄이 일치했고 차이는 0줄**이었다. 13개 출력 종류에서 각각 한 줄을 바꾼 대조 시험도 13개 모두 검출했다. 유형별 결과는 ZIP의 `evidence/js-cross-check.txt`에 있다.

대조 대상에는 계단, 트랙 분류, QSMD, 요약, 통계가 포함된다. 계단·분류의 응답열은 준비된 유한 집합이고, 모든 가능한 응답열에 대한 두 구현의 동치는 별도로 증명되지 않았다. 대조기는 자리 순열검정을 비교하지 않아 앱 코드를 메모리에 읽을 때 해당 반복 수를 2,000에서 20으로 줄인다. `js/stim.js`는 이 대조에 들어가지 않는다.

## 재현 방법

ZIP을 푼 뒤 `SMD-Lean` 폴더를 기준으로 아래 명령을 실행한다. Lean 4.24.0 도구 체인과 그에 맞는 `lake`가 필요하다.

```sh
cd tools/lean
lake build
lake env lean PrintAxioms.lean
lake env lean MyAudit.lean
lake env lean scratch/T1.lean
```

원본 Lean 파일 12개, `lean-toolchain`, `lakefile.toml`, `lake-manifest.json`은 원본과 바이트 단위로 같다. 공개본에서 추가한 `PrintAxioms.lean`은 정리별 공리 출력용이다. ZIP 루트에는 원문 로그와 전체 대응표를, `evidence/`에는 전체 환경 감사 출력과 소스 해시를 담았다. 개인 PC의 경로가 들어간 기존 설명서는 이 보고서로 대체했다.

**선택적 앱 대조 재현.** Lean 빌드에는 앱이 필요하지 않다. JS 대조도 재현하려면 앱 1.1.1의 `rng.js`, `official.js`, `protocol.js`, `staircase.js`, `analysis.js`를 ZIP 루트의 `js/` 폴더에 둔다. ZIP에는 원본 대조기 `tools/lean/cross_check.js`가 들어 있다. 이번 대조에는 Deno 2.7.14를 썼다. 아래 명령으로 `tools/lean`에서 같은 대조를 재현할 수 있다. 중간 파일은 현재 폴더에 생성된다.

```sh
deno run --allow-read --allow-write cross_check.js input cases.txt js-result.txt
lake exe crosscheck cases.txt lean-result.txt
deno run --allow-read cross_check.js check js-result.txt lean-result.txt
```
