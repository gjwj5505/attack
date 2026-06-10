# Attack

작은 명령형 언어를 대상으로 정적 분석기를 공격하는 프로그램을 합성하는 프로젝트입니다.

프로그램 syntax만 만드는 것이 아니라 Big-Step proof tree를 bottom-up으로 함께 합성하고, proof tree의 결론에 있는 프로그램을 분석기에 넣어 concrete 실행보다 덜 정밀한 분석 결과가 나오는지 확인합니다.

## 빌드

```sh
dune build
```

빌드하면 루트에 실행 파일이 생깁니다.

```sh
./attack
```

dune을 통해 직접 실행할 수도 있습니다.

```sh
dune exec attack -- <options>
```

## 기본 사용법

라벨이 붙은 프로그램 출력:

```sh
./attack -pp examples/260522-unary-guard-square-top.g
```

분석기 실행:

```sh
./attack -analyze examples/260522-unary-guard-square-top.g
```

각 라벨 위치의 분석 결과를 프로그램 왼쪽에 함께 출력:

```sh
./attack -analyze -v examples/260522-unary-guard-square-top.g
```

Big-Step proof tree 출력:

```sh
./attack -big examples/260522-unary-guard-square-top.g
```

## 공격 합성

공격 프로그램을 합성합니다.

```sh
./attack -attack
```

공격 목표를 지정할 수 있습니다.

```sh
./attack -attack -objective top
./attack -attack -objective nonsingleton
./attack -attack -objective unbounded
./attack -attack -objective unsound
```

크기 bound를 줄 수 있습니다. 순서는 `(program size, proof size)`입니다.

```sh
./attack -attack -objective top -bound 13 16
```

휴리스틱, 분석기 버전, random seed는 CLI 옵션이 아니라
`lib/config/config.ml`의 `Config_util.attack ()`에서 설정합니다.

현재 가능한 이름은 heuristic `none|random1|random2`, analyzer `260417|260528`입니다.

## 현재 휴리스틱

휴리스틱은 `lib/config/config.ml`의 `heuristic_name`으로 선택합니다.
`none`은 score/cap을 사용하지 않고, `random1`과 `random2`는 같은 임시
random score 기반 pruning 구현입니다.

- 각 size bucket은 score 상위 1000개 component만 유지합니다.
- binary rule은 각 입력 bucket에서 상위 32개씩만 조합합니다.
- ternary rule은 각 입력 bucket에서 상위 10개씩만 조합합니다.

이 방식은 실험용입니다. 이후에는 random score 대신 분석기 결과를 반영한 priority, diversity, 그리고 언젠가는 성공을 보장할 수 있는 탐색 schedule로 바꿔갈 예정입니다.

## 참고 파일

- `lib/synthesis/attack.ml`: 공격 탐색 루프와 size schedule
- `lib/synthesis/grow_prog.ml`: syntax component 생성
- `lib/synthesis/grow_proof.ml`: Big-Step proof tree 생성
- `lib/synthesis/component_pool/`: component wrapper, metadata, cap
- `lib/analyzer/`: interval analyzer와 analyzer visualizer
- `examples/`: 날짜별 공격 성공 프로그램
- `.agents/analyzer-attack-log.md`: 성공한 공격 분석 로그
