와우STM · Lean 4 검증 프로젝트

검증 대상은 검사 앱의 기본 계단, 역치 계산, 분류 및 자극의 일부 산술을 옮긴 별도 모델이다.
검증 범위와 정리별 표는 verification.html에서 확인할 수 있다.

재현
Lean 4.19.0과 함께 제공되는 Lake를 사용한다. 프로젝트 폴더(stm-lean4)에서 아래 순서대로 실행한다.
별도의 Lake 패키지 의존성은 없다. 첫 명령은 기본 라이브러리, 두 번째는 비교용 JSON 실행 파일을 빌드한다.
Witness는 기본 빌드 대상 밖에 있어 네 번째 명령으로 컴파일한 뒤 공리 출력에서 불러온다.

lake build
lake build stmCheck
lake env lean -t 0 Audit.lean
lake env lean -t 0 -o .lake/build/lib/lean/Witness.olean Witness.lean
lake env lean -t 0 PrintAxioms.lean

정상 결과는 위 다섯 명령 모두 종료 코드 0이다. 실제 출력은 results/에 있다.
results/print-axioms.txt에는 본체의 명명 정리 161개와 증인 정리 7개에 대한 #print axioms 원문이 있다.
results/stm-audit.txt에는 자동 생성 보조 정리 등을 포함한 Stm 이름공간의 감사 결과가 있다.

감사 장치 자체를 시험하려면 아래 세 명령을 각각 따로 실행한다. 세 테스트 모두 종료 코드 1이 정상이다.
이 파일들은 모델이 불러오지 않는다. 첫 파일의 6행에 의도적으로 넣은 sorry가 있다.

lake env lean -t 0 audit-controls/NegativeControlSorry.lean
lake env lean -t 0 audit-controls/NegativeControlForeignAxiom.lean
lake env lean -t 0 audit-controls/NegativeControlNative.lean

출처
2026-10-19 와우STM 검증본의 stm-mathematical-methodology/formalization 폴더를 사용했다.
이 폴더의 .lean 파일 9개와 lean-toolchain, lake-manifest.json을 그대로 복사했다.
lakefile.lean은 .lean 파일 9개에 포함된다. 최초 stm-lean4 검증본과 공통인 소스와 설정은 바이트 단위로 동일하다.
Witness.lean은 후속 검증에 추가된 파일이다. 별도 보관된 감사 대조 파일 3개는 audit-controls/에 두었다.
이번 공개본에 추가한 PrintAxioms.lean은 기존 정리의 공리를 출력한다.
SHA256SUMS.txt는 자기 자신을 제외한 공개 파일들의 SHA-256 목록이다.
