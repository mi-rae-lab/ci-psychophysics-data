와우GDT — 기록에서 뺀 회기 (2026-11-03T11:32:23.426Z)

무엇: 2026-11-01 22:26 (UTC 2026-11-01T13:26:24.081Z) Xie 2022 회기 mvxv5s291ntdw3, 귀 R, 앱 1.0.2 (2026-11-01)
  측정 3개: rmvxv6e67ybxelb 25.67 ms (35시행) · rmvxv9tcdkz47r8 25.00 ms (36) · rmvxvdd06uq0m7g 21.67 ms (30) → 회기 값 24.11 ms
왜: 사용자 요청 “이때 날에 한 3가지 다 삭제해줘. 프로그램 오류가 있었어” (범위 = 11-01 Xie 측정 3개, 앱 기록 + 보고서)
  같은 날 Claude 의 기록 점검(소리 다시 합성 · 절차 해시 · 안내 문구)에서는 앱 오류를 찾지 못함 — 빼는 것은 사용자 판단
어떻게: 앱 창을 닫은 뒤 서버 API(POST /api/db, 판 번호 확인)로 DB 에서 회기 1개 · 측정 3개를 빼고
  DB.decisions 에 'delete-session' 줄(id d_delete-session_mvxv5s291ntdw3)을 남김. 판 1106 → 1107.
  journal 3개는 이 폴더 journal\ 로 옮김 (앱이 시작할 때 data\journal 의 journal 로 측정을 되살리므로).
이 폴더: removed.json (뺀 회기 · 측정 그대로) · db.before.json (빼기 직전 db.json 그대로) · journal\*.jsonl
그대로 둔 것: data\runs-log.jsonl (지워지지 않는 기록) · data\backup\ · data\db.prev.json (빼기 직전 판)
되돌리기: 앱 창을 모두 닫고 journal\ 의 3개를 data\journal\ 로 되돌린 뒤,
  removed.json 의 session · runs 를 db.json 의 sessions · runs 에 다시 넣음.
