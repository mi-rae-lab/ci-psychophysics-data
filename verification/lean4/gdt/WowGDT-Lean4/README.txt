와우GDT | Lean 4 검증 소스와 재현 방법

이 폴더에는 원본 tools/lean의 .lean 파일 전체와 Lake 설정 3개가 들어 있다.
PrintAxioms.lean은 이번 배포에서 추가한 조회 전용 파일이다.
보고서와 빌드·공리 출력은 verification/에서 확인할 수 있다.

Lean 4.24.0과 Lake를 사용할 수 있는 환경에서 이 폴더로 이동해 차례로 실행한다.

    lake build
    lake env lean PrintAxioms.lean
    lake env lean MyAudit.lean

기본 빌드는 GDT 라이브러리와 crosscheck 실행 파일을 함께 만든다.
manifest에 외부 Lean 패키지는 없다. .lake는 빌드할 때 생성된다.
PrintAxioms.lean은 소스에 명시된 모든 정리를 조회한다.
MyAudit.lean은 컴파일러 생성 항목까지 포함해 GDT 이름공간을 검사한다.

이 소스는 검사 앱의 규칙을 Lean으로 모델링한 것이다. CrossCheck.lean은
입력에 대한 모델 출력을 생성한다. JS 앱과의 대조에는 별도의 앱 소스와
원본 tools/lean/cross_check.js가 필요하다. 이 배포의 검증 명령은 위 세 가지다.
