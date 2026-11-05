와우SMRT | Lean 4 검증 공개본
원본 앱 버전 1.3 · 검증 재실행 2026-11-04 (KST)

wowSMRT-Lean4-report.html을 브라우저에서 열면 두 검사의 규칙 비교와
정리 169개 각각의 명제, 원본 소스 위치, 사용 공리를 확인할 수 있습니다.
보고서는 오프라인에서 열립니다.

재현
  1. ZIP의 폴더 구조를 유지하여 압축을 풉니다.
  2. elan을 사용하는 환경에서 lean-toolchain이 있는 이 폴더로 이동합니다.
     지정 버전은 leanprover/lean4:v4.24.0입니다. 별도 Lean 패키지 의존성은 없습니다.
  3. 다음 세 명령을 순서대로 실행합니다.

     lake build
     lake env lean PrintAxioms.lean
     lake env lean MyAudit.lean

내용
  원본 소스              SMRT.lean, SMRT/*.lean, CrossCheck.lean, MyAudit.lean
  원본 설정              lean-toolchain, lakefile.toml, lake-manifest.json
  공개본에 추가한 파일    PrintAxioms.lean, 이 안내서, HTML 보고서, evidence/

evidence/
  build.txt              lake build 전체 출력
  print-axioms.txt       직접 선언한 정리 169개의 #print axioms 전체 출력
  environment-audit.txt  SMRT 이름공간의 공리 감사 전체 출력
  *-run.txt              각 실행의 명령, 시각, 도구 버전, 소요 시간, 종료 코드
  original-files.sha256  복사한 원본 파일 16개의 SHA-256 (프로젝트 루트 기준)
  source-scan.txt        원본 Lean 파일에서 증명 자리표시자를 검사한 결과

증명 범위
  원본 tools/lean의 모델을 검증한 것입니다. SMRT 밀도 검사는 1-down 1-up,
  크기 구별 검사는 2-down 1-up입니다. 실제 앱의 JavaScript와 모델의 관계는
  원본 교차검사에서 같은 입력에 대해 얻은 출력으로 확인했습니다.
  앱 실행 코드, 검사 기록, WAV 파일, .lake 빌드 캐시는 이 공개본의 구성에
  포함되지 않습니다. 자극 파형의 수식은 별도의 Python 수치 대조 대상입니다.
