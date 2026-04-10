# Overview

정적 분석기가 false alarm을 발생시키는 프로그램을 합성하는 프로젝트.

프로그램 자체가 아니라 **Big-Step semantics의 proof tree를 합성**하여,
while문이 포함된 경우에도 **유한 시간 내 합성**을 보장한다.

---

# Key Idea

- 합성 단위: 프로그램 ❌ → proof tree ⭕
- 결과: proof tree의 결론에 해당하는 프로그램

---

# Size

proof tree의 크기:

- `prog_size`: 결론 프로그램 크기
- `proof_size`: 노드 수

단일 기준(proof_size)만 사용할 경우,
dead branch에 큰 프로그램이 포함되어 **완전 열거가 깨짐**

→ `(prog_size, proof_size)`를 **대각선 순서로 열거**

---

# Goal

분석기에서 **false alarm을 유발하는 프로그램**을 합성

---

# Status

- Syntax / Parser / Lexer
- 실행 의미 정의
- 간단한 분석기
- Big-Step proof tree
  - 생성 함수
  - 유효성 검사
  - size 정의

---

# TODO

- `(prog_size, proof_size)` partition
- `synthesizer.ml` 이해 및 정리
- `main.ml`에 합성 연결

---

# Modules

- Syntax / Parser / Analyzer / BigStep / Synthesis

---

# Constraints

- complete enumeration
- termination 보장
- dead branch explosion 방지