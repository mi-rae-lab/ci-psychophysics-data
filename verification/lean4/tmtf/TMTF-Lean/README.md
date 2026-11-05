# 와우TMTF Lean 4 검증 공개본

와우TMTF 3.3.3의 계단 규칙과 자극 수식을 별도의 Lean 모델로 표현한 프로젝트다. 원본에 명시된 정리 123개, 주요 규칙의 정확한 증명 범위, 앱과의 교차검증 결과는 [한국어 검증 보고서](VERIFICATION.ko.md)에 있다.

| 폴더 또는 파일 | 내용 |
|---|---|
| `tools/lean/` | 원본 Lean 소스 13개, `lean-toolchain`, `lakefile.toml`, `lake-manifest.json`, JS 대조 스크립트. 원래의 폴더 구조와 소스 바이트를 보존했다. |
| `tools/lean/PrintAxioms.lean` | 공개본에서 추가한 감사 입력. 원본에서 이름을 붙여 선언한 정리마다 `#print axioms`를 실행한다. |
| `js/` | 교차검증이 직접 읽는 실제 앱 파일 `track.js`, `stim.js`, `protocols.js`. |
| `verification/` | 빌드 로그, 명시적 정리별 공리 원문, 전체 모델 공리 감사, 소스 검색 결과, 버전과 JS 교차검증 실행 기록. |
| `SHA256SUMS.txt` | 파일별 SHA-256. 자기 자신을 제외한 ZIP 내 모든 파일을 수록한다. |

## Lean 빌드와 감사

ZIP을 풀고 `TMTF-Lean` 폴더에서 다음 명령을 실행한다. `lean-toolchain`은 `leanprover/lean4:v4.24.0`을 지정한다. 검증 환경은 Lean 4.24.0 및 Lake 5.0.0-src+797c613이고, manifest의 외부 패키지 목록은 비어 있다.

```sh
cd tools/lean
lean --version
lake --version
lake build
lake env lean PrintAxioms.lean
lake env lean MyAudit.lean
```

빌드와 두 감사 명령은 모두 종료 코드 0을 반환했다. 빌드 로그의 마지막 줄은 `Build completed successfully (27 jobs).`이다. `MyAudit.lean`의 마지막 줄은 `NONSTANDARD 0`이다. 각 명령의 원문은 각각 [빌드 로그](verification/lake-build.txt), [정리별 공리](verification/print-axioms.txt), [전체 모델 감사](verification/environment-audit.txt)에 있다.

## 실제 앱 JS와 대조하기

Lean 빌드 뒤 ZIP 최상위 `TMTF-Lean` 폴더에서 실행한다. 이번 검사에는 Windows와 Deno 2.7.14를 사용했다. 입력과 비교용 출력은 아래 명령이 다시 생성한다.

```powershell
New-Item -ItemType Directory -Force check | Out-Null
deno run --allow-read --allow-write tools/lean/cross_check.js input check/input.txt check/js.txt
./tools/lean/.lake/build/bin/crosscheck.exe check/input.txt check/lean.txt
deno run --allow-read tools/lean/cross_check.js check check/js.txt check/lean.txt
```

마지막 줄 `판정: 통과`와 종료 코드 0을 확인한다. 이번 실행은 12종의 1,174개 출력행을 비교했고 계단 360개 사례가 포함됐다. [교차검증 원문](verification/cross-check.txt)
