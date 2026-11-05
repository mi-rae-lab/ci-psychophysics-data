# 와우SRD Lean 4 공개 검증본

와우SRD 검사 앱의 계단·역치·결과 분류 규칙을 옮겨 쓴 Lean 모델과 2026-11-04에 다시 실행한 검증 결과다. 규칙별 보장 범위, 앱의 자극 수식과의 대응, 정리 125개의 공리 의존성은 [검증 보고서](REPORT.md)에 있다.

## Lean 재현

Lean 4.24.0과 Lake가 설치된 환경에서 압축을 풀고 `WowSRD-Lean` 폴더에서 시작한다. 프로젝트는 `lean-toolchain`으로 버전을 고정하며 외부 Lake 패키지를 사용하지 않는다.

```sh
cd tools/lean
lake build
lake env lean PrintAxioms.lean
lake env lean MyAudit.lean
```

기본 빌드는 증명 라이브러리 `SRD`와 JS 대조용 실행 파일 `crosscheck`를 만든다. 공리 검사는 뒤의 두 명령으로 실행한다. 원본 Lean 파일 11개와 Lake 설정 3개는 원본과 바이트 단위로 같다. `PrintAxioms.lean`은 공개본에서 추가한 출력용 파일이다.

## JS 대조 재현

Deno와 위에서 빌드한 실행 파일을 사용한다. 새 터미널에서 `WowSRD-Lean` 폴더를 작업 디렉터리로 두고 다음 세 줄을 차례로 실행한다. Windows PowerShell 예시다.

```powershell
deno run --allow-read --allow-write tools/lean/cross_check.js input cross-input.txt cross-js.txt
./tools/lean/.lake/build/bin/crosscheck.exe cross-input.txt cross-lean.txt
deno run --allow-read tools/lean/cross_check.js check cross-js.txt cross-lean.txt
```

Linux·macOS에서는 둘째 줄의 실행 파일 이름에서 `.exe`를 뺀다. 비교기는 원본 앱에서 가져온 `js/rng.js`, `ltass.js`, `protocol.js`, `staircase.js`, `analysis.js`를 읽는다. `js/stim.js`는 보고서에서 다루는 파형 수식을 확인할 수 있도록 함께 실었다. 이 파일은 위 비교기의 입력이 아니다.

## 파일 안내

| 파일 또는 폴더 | 내용 |
|---|---|
| `tools/lean/` | 원본 Lean 프로젝트, 원본 JS 비교기, 공개본의 `PrintAxioms.lean` |
| `js/` | 실제 앱에서 발췌한 대조용 모듈 5개와 자극 수식 참조용 모듈 1개 |
| `REPORT.md` | 규칙·자극 수식별 증명 범위와 전체 정리 대응표 |
| `verification/` | 빌드, 공리 감사, JS 대조 원출력과 명령별 종료 코드·소요 시간(`runs.json`) |
| `source-sha256.txt` | 압축본에 실은 원본 소스·설정 파일들의 SHA-256 값. 경로는 이 폴더 기준 |

