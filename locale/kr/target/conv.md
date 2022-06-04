전략 모드로 전환
=========================

전략 블록 안에서 `conv` 키워드를 사용하여 전환 모드로 들어갈 수 있습니다. 이 모드를 사용하면 가정과 목표 속과 심지어 함수 추상화 및 종속 화살표 내부를 이동하여 다시쓰기 또는 단순화 단계를 적용할 수 있습니다.

기본 탐색 및 다시쓰기
-------

첫 번째 예로서 `(a b c : Nat) : a * (b * c) = a * (c * b)` 예제를 증명해 봅시다. (다른 전술로 이 예제를 즉시 끝낼 수 있기에 이것은 다소 인위적입니다.) 첫 순진한 시도는 전략 모드로 들어가 `rw [Nat.mul_comm]`을 시도하는 것입니다. 그러나 이것은 항에 나타나는 맨 처음 곱셈을 교환한 뒤 목표를 `b * c * a = a * (c * b)`로 바꿉니다. 이 문제를 해결하는 방법에는 여러 가지가 있으며 한 가지 방법은 보다 정밀한 도구인 전환 모드를 사용하는 것입니다. 다음 코드 블록은 각 줄 뒤에 있는 현재 대상을 보여줍니다.

```lean
example (a b c : Nat) : a * (b * c) = a * (c * b) := by
  conv =>
    -- |- a * (b * c) = a * (c * b)
    lhs
    -- |- a * (b * c)
    congr
    -- 2 goals : |- a and |- b * c
    skip
    -- |- b * c
    rw [Nat.mul_comm]
```

위의 자투리는 세 가지 탐색 명령을 보여줍니다.

- `lhs`는 관계식의 좌변으로 이동하고(여기서는 등호), 우변으로 이동하는 `rhs`도 있습니다.
- `congr`은 현재 머리 함수 (여기서 머리 함수은 곱셈)에 대한 (비의존적 및 명시적) 인수만큼 많은 대상을 생성합니다.
- `skip`는 다음 대상으로 이동합니다.

일단 연관된 대상에 도달하면 일반 전략 모드처럼 `rw`를 사용할 수 있습니다.

전환 모드를 사용하는 두 번째 주요 이유는 결합자 아래에서 다시쓰기 위한 것입니다. 예제 `(fun x : Nat => 0 + x) = (fun x => x)`을 증명하고 싶다고 해봅시다.
첫 순진한 시도는 전략 모드로 들어가 `rw [zero_add]`를 시도하는 것입니다. 그러나 이것은 좌절과 함께 실패합니다.

```
오류: '다시 쓰기' 전술이 실패했습니다. 패턴의 개체를 찾지 못했습니다.(error: tactic 'rewrite' failed, did not find instance of the pattern)
       대상 표현식에서
  0 + ?n
⊢ (fun x => 0 + x) = fun x => x
```

해결책은

```lean
example : (fun x : Nat => 0 + x) = (fun x => x) := by
  conv =>
    lhs
    intro x
    rw [Nat.zero_add]
```

여기서 `intro x`는 `fun` 결합자 내부로 들어가는 탐색 명령입니다.
이 예제는 다소 인위적이며 누군가는 다음과 같이 할 수 있음을 보세요.

```lean
example : (fun x : Nat => 0 + x) = (fun x => x) := by
  funext x; rw [Nat.zero_add]
```

아니면 그냥

```lean
example : (fun x : Nat => 0 + x) = (fun x => x) := by
  simp
```

이 모든 것은 `conv at h`를 사용하여 지역 상황에서 가정 `h`를 다시쓰기 하는 데에도 이용할 수 있습니다.

패턴 매칭
-------

위 명령을 사용한 탐색은 지루할 수 있습니다. 누군가는 다음과 같이 패턴 매칭을 사용하여 그것을 손쉽게 할 수 있습니다.

```lean
example (a b c : Nat) : a * (b * c) = a * (c * b) := by
  conv in b * c => rw [Nat.mul_comm]
```

이것은 다음에 대한 문법적 설탕입니다.

```lean
example (a b c : Nat) : a * (b * c) = a * (c * b) := by
  conv =>
    pattern b * c
    rw [Nat.mul_comm]
```

당연히 와일드카드도 허용됩니다.

```lean
example (a b c : Nat) : a * (b * c) = a * (c * b) := by
  conv in _ * c => rw [Nat.mul_comm]
```

전환 전술 구조화하기
-------

중괄호와 `.`은 전략을 구조화하기위해 `conv` 모드에서도 사용될 수 있습니다.

```lean
example (a b c : Nat) : (0 + a) * (b * c) = a * (c * b) := by
  conv =>
    lhs
    congr
    . rw [Nat.zero_add]
    . rw [Nat.mul_comm]
```

전환 모드 속 다른 전략
----------

- `arg i`는 적용의 `i`번째 비의존적인 명시적 인수를 입력합니다.

```lean
example (a b c : Nat) : a * (b * c) = a * (c * b) := by
  conv =>
    -- |- a * (b * c) = a * (c * b)
    lhs
    -- |- a * (b * c)
    arg 2
    -- |- b * c
    rw [Nat.mul_comm]
```

- `args` `congr`의 대체 이름

- `simp`는 현재 목표에 단순화기를 적용합니다. 보통의 전략 모드에서 사용할 수 있는 것과 동일한 옵션을 지원합니다.

```lean
def f (x : Nat) :=
  if x > 0 then x + 1 else x + 2

example (g : Nat → Nat) (h₁ : g x = x + 1) (h₂ : x > 0) : g x = f x := by
  conv =>
    rhs
    simp [f, h₂]
  exact h₁
```

- `enter [1, x, 2, y]` 주어진 인수로 `arg` 및 `intro`를 반복합니다. 이것은 그저 매크로입니다.

```
syntax enterArg := ident <|> num
syntax "enter " "[" (colGt enterArg),+ "]": conv
macro_rules
  | `(conv| enter [$i:numLit]) => `(conv| arg $i)
  | `(conv| enter [$id:ident]) => `(conv| ext $id)
  | `(conv| enter [$arg:enterArg, $args,*]) => `(conv| (enter [$arg]; enter [$args,*]))
```

- 미해결 목표가 있으면 `done`이 실패합니다.

- `traceState`는 현재 전략 상태를 표시합니다.

- `whnf`은 항를 약한 머리 정규 형식에 둡니다.

- ` tactic => <tactic sequence>`는 보통의 전략 모드로 되돌아갑니다. 이는 `conv` 모드에서 지원되지 않는 목표를 실행하고 사용자 정의 합동 및 확장 보조정리를 적용하는 데 유용합니다.

```lean
example (g : Nat → Nat → Nat)
        (h₁ : ∀ x, x ≠ 0 → g x x = 1)
        (h₂ : x ≠ 0)
        : g x x + x = 1 + x := by
  conv =>
    lhs
    -- |- g x x + x
    arg 1
    -- |- g x x
    rw [h₁]
    -- 2 goals: |- 1, |- x ≠ 0
    . skip
    . tactic => exact h₂
```

- `apply <term>`은 `tactic => apply <term>`에 대한 문법 설탕입니다.

```lean
example (g : Nat → Nat → Nat)
        (h₁ : ∀ x, x ≠ 0 → g x x = 1)
        (h₂ : x ≠ 0)
        : g x x + x = 1 + x := by
  conv =>
    lhs
    arg 1
    rw [h₁]
    . skip
    . apply h₂
```
