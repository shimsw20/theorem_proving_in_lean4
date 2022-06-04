귀납과 재귀
=======================

이전 장에서 우리는 귀납적 정의가 린의 새 유형을 도입하는 강력한 수단을 제공함을 보았습니다. 게다가 생성자와 재귀자는 이 유형에 대한 함수 정의의 유일한 수단을 제공합니다. 유형으로써 명제 대응에 따르면 이것은 귀납은 증명의 기초적인 방식임을 의미합니다.

린은 재귀적인 함수를 정의하는 자연스러운 방법을 제공하고, 패턴 매치를 수행하고, 귀납적 정의를 작성합니다. 이는 여러분이 그것이 만족해야 하는 방정식을 명시함으로써 함수를 정의하도록 해줍니다. 그리고 이것은 일어날 수 있는 다양한 경우를 어떻게 다뤄야 하는지 나타내줌으로써 여러분이 정리를 증명하게 해줍니다. 막의 뒤에서 이 설명은 "방정식 컴파일러"라고 부르는 절차를 사용하여 기초적인 재귀자로 "컴파일되어" 내려갑니다. 방정식 컴파일러는 신뢰받는 코드 기반의 일부가 아닙니다. 그것의 출력은 커널에 의해 독립적으로 검증된 항으로 구성됩니다.

패턴 매칭
----------------

도식적인 패턴의 해석은 컴파일 과정의 첫 단계입니다. 재귀적으로 정의된 유형에 연관된 생성자를 따라 우리는 ``casesOn`` 재귀자가 함수를 정의하고 경우를 나눠 정리를 증명하는데 사용될 수 있음을 보았습니다. 그러나 복잡해진 정의는 몇 단계로 중첩하여 ``casesOn``를 사용할 수도 있습니다. 그리고 읽고 이해하기 어렵게 될 것입니다. 패턴 매칭은 더 편리한 접근법과 함수형 프로그래밍 언어의 사용자에게 친숙한 접근법을 제공합니다.

자연수의 재귀적으로 정의된 유형을 고려해보세요. 모든 자연수는 ``zero``이거나 ``succ x``입니다. 그래서 여러분은 각 경우에 대한 값을 나타내줌으로써 자연수에서 임의의 유형으로 가는 함수를 정의할 수 있습니다.

```lean
open Nat

def sub1 : Nat → Nat
  | zero   => zero
  | succ x => x

def isZero : Nat → Bool
  | zero   => true
  | succ x => false
```

방정식들은 정의상으로 성립하는 이 함수들을 정의하는데 사용됩니다.

```lean
# open Nat
# def sub1 : Nat → Nat
#   | zero   => zero
#   | succ x => x
# def isZero : Nat → Bool
#   | zero   => true
#   | succ x => false
example : sub1 0 = 0 := rfl
example (x : Nat) : sub1 (succ x) = x := rfl

example : isZero 0 = true := rfl
example (x : Nat) : isZero (succ x) = false := rfl

example : sub1 7 = 6 := rfl
example (x : Nat) : isZero (x + 3) = false := rfl
```

``zero``과 ``succ`` 대신 우리는 더 친숙한 기호를 사용할 수 있습니다.

```lean
def sub1 : Nat → Nat
  | 0   => 0
  | x+1 => x

def isZero : Nat → Bool
  | 0   => true
  | x+1 => false
```

왜냐하면 덧셈과 0 기호는 ``[matchPattern]`` 특성이 할당되어 있기에 그들은 패턴 매칭에 사용될 수 있습니다. 린은 단순히 이 표현식들을 생성자 ``zero``과 ``succ``이 드러날 때까지 정규화합니다.

패턴 매칭은 곱과 옵션 유형 같은 임의의 재귀형과 동작합니다.

```lean
def swap : α × β → β × α
  | (a, b) => (b, a)

def foo : Nat × Nat → Nat
  | (m, n) => m + n

def bar : Option Nat → Nat
  | some n => n + 1
  | none   => 0
```

여기서 우리는 이것을 함수를 정의하는 것과 경우에 따른 증명을 수행하는데에도 사용합니다.

```lean
# namespace Hidden
def not : Bool → Bool
  | true  => false
  | false => true

theorem not_not : ∀ (b : Bool), not (not b) = b
  | true  => rfl  -- proof that not (not true) = true
  | false => rfl  -- proof that not (not false) = false
# end Hidden
```

패턴 매칭은 재귀적으로 정의된 명제를 파괴하는 데에도 사용될 수 있습니다.

```lean
example (p q : Prop) : p ∧ q → q ∧ p
  | And.intro h₁ h₂ => And.intro h₂ h₁

example (p q : Prop) : p ∨ q → q ∨ p
  | Or.inl hp => Or.inr hp
  | Or.inr hq => Or.inl hq
```

이것은 논리연결사가 사용된 가정을 펼치는 간소한 방식을 제공합니다.

이 모든 에제에서 패턴 매칭은 한 경우의 구별을 수행하는데 사용됩니다. 더 흥미롭게도 패턴은 다음 예제에 있는 중첩된 생성자에도 관여할 수 있습니다.

```lean
def sub2 : Nat → Nat
  | 0   => 0
  | 1   => 0
  | x+2 => x
```

방정식 컴파일러는 우선 입력이 ``zero``인지 ``succ x``의 꼴인지에 따라 경우를 나눕니다.  그 뒤 ``x``가 ``zero``인지 ``succ x``의 꼴인지에 따라 경우를 나눕니다.  이것은 그것에 제시된 패턴에 필요한 경우를 나누는 것을 결정하고, 패턴이 경우를 처리하는데 실패하면 오류를 발생시킵니다. 다시 한 번 우리는 산술적 기호를 아래 버전에서 처럼 사용할 수 있습니다. 각 경우에서 정의한 방정식들은 정의로 인해 성립합니다.

```lean
# def sub2 : Nat → Nat
#   | 0   => 0
#   | 1   => 0
#   | x+2 => x
example : sub2 0 = 0 := rfl
example : sub2 1 = 0 := rfl
example : sub2 (x+2) = x := rfl

example : sub2 5 = 3 := rfl
```

여러분은 ``#print sub2``를 써 어떻게 함수가 재귀자로부터 컴파일되었는지 볼 수 있습니다. (린은 여러분에게 ``sub2``가 내부의 보조 함수 ``sub2.match_1``에 대해서 정의되었다고 말할 것입니다. 그러나 여러분은 그것도 출력해볼 수 있습니다.) 린은 이 보조 함수를 `match` 표현식을 컴파일하는데 사용합니다.
실제로 위 정의는 다음과 같이 확장됩니다.

```lean
def sub2 : Nat → Nat :=
  fun x =>
    match x with
    | 0   => 0
    | 1   => 0
    | x+2 => x
```

여기 중첩된 패턴 매칭에 대한 몇 가지 추가 예제가 있습니다.

```lean
example (p q : α → Prop)
        : (∃ x, p x ∨ q x) → (∃ x, p x) ∨ (∃ x, q x)
  | Exists.intro x (Or.inl px) => Or.inl (Exists.intro x px)
  | Exists.intro x (Or.inr qx) => Or.inr (Exists.intro x qx)

def foo : Nat × Nat → Nat
  | (0, n)     => 0
  | (m+1, 0)   => 1
  | (m+1, n+1) => 2
```

이 방정식 컴파일러는 다수의 인수를 순차적으로 처리할 수 있습니다. 예를 들어 이전 예제를 두 인수를 받는 함수로 정의하는 것이 더 자연스럽습니다.

```lean
def foo : Nat → Nat → Nat
  | 0,   n   => 0
  | m+1, 0   => 1
  | m+1, n+1 => 2
```

여기 또 다른 예제가 있습니다.

```lean
def bar : List Nat → List Nat → Nat
  | [],      []      => 0
  | a :: as, []      => a
  | [],      b :: bs => b
  | a :: as, b :: bs => a + b
```

패턴이 콤마로 나뉜 것에 주목하세요.

다른 인수들도 패턴의 리스트 사이에 포함되어 있음에도 다음의 각 예제에서 분할은 첫 번째 인수에만 일어납니다.

```lean
# namespace Hidden
def and : Bool → Bool → Bool
  | true,  a => a
  | false, _ => false

def or : Bool → Bool → Bool
  | true,  _ => true
  | false, a => a

def cond : Bool → α → α → α
  | true,  x, y => x
  | false, x, y => y
# end Hidden
```

인수의 값은 정의에서 필요하지 않음도 주목하세요. 여러분은 대신 밑줄 문자를 쓸 수 있습니다. 이 밑줄 문자는 *와일드카드 패턴(wildcard pattern)*혹은 *익명 변수(anonymous variable)*로 알려져 있습니다. 방정식 컴파일러 밖에서의 사용과 대조적으로 여기서 밑줄 문자는 암시적인 인수를 지칭하지 *않습니다.* 와일드카드에 대한 밑줄 문자의 사용은 함수형 프로그래밍 언어에서 흔합니다. 그래서 린은 이 표기를 채택합니다. [와일드카드와 중복된 패턴 섹션](#wildcards_and_overlapping_patterns)은 와일드카드에 대한 개념을 넓히고 [접근할 수 없는 패턴 섹션](#inaccessible_terms)은 여러분이 어떻게 패턴속에서도 암시적인 인수를 사용할 수 있는지 설명합니다.

[재귀형 장](./inductive_types.md)에서 설명했다시피 재귀 데이터형은 매개변수에 의존합니다. 다음 예제는 패턴 매칭을 사용해 ``tail`` 함수를 정의합니다. 인수 ``α : Type``은 매개변수이고 패턴 매칭에 참여하지 않음을 지칭하는 콜론 앞에 있습니다.
린은 매개변수가 ``:`` 뒤에서 나타나는 것도 허용합니다. 그러나 이들에 대해 패턴 매칭은 할 수 없습니다.

```lean
def tail1 {α : Type u} : List α → List α
  | []      => []
  | a :: as => as

def tail2 : {α : Type u} → List α → List α
  | α, []      => []
  | α, a :: as => as
```

이 두 예제에서 매개변수 ``α``의 다른 배치에도 불구하고 두 경우 모두 같은 방식으로 다뤄집니다. 그러므로 이것은 경우 분할에 참여하지 않습니다.

린은 인수가 다양한 경우에 대해 추가적인 제약을 의존 유형에 부여하는 것 같은 패턴 매칭의 더 복잡한 형태도 다룰 수 있습니다. 그런 *종속적인 패턴 매칭*의 예제는 [종속적인 패턴 매칭 섹션](#dependent_pattern_matching)에서 다뤄집니다.

와일드카드와 중복되는 패턴
----------------------------------

지난 섹션의 예제 중 하나를 고려해 봅시다.

```lean
def foo : Nat → Nat → Nat
  | 0,   n   => 0
  | m+1, 0   => 1
  | m+1, n+1 => 2
```

```lean
def foo : Nat → Nat → Nat
  | 0, n => 0
  | m, 0 => 1
  | m, n => 2
```

두 번째 나타남에서 패턴은 겹칩니다. 예를 들어 인수의 쌍 ``0 0``은 세 경우 모두 일치합니다. 그러나 린은 활용할 수 있는 첫 방정식을 사용하여 모호성을 해소합니다. 그래서 이 예제에서 최종 결과는 같습니다. 특히 다음 방정식은 정의로부터 성립합니다.

```lean
# def foo : Nat → Nat → Nat
#   | 0, n => 0
#   | m, 0 => 1
#   | m, n => 2
example : foo 0     0     = 0 := rfl
example : foo 0     (n+1) = 0 := rfl
example : foo (m+1) 0     = 1 := rfl
example : foo (m+1) (n+1) = 2 := rfl
```

``m``과 ``n``의 값은 필요하지 않으므로 우리는 와일드카드 패턴을 대신 사용하여도 됩니다.

```lean
def foo : Nat → Nat → Nat
  | 0, _ => 0
  | _, 0 => 1
  | _, _ => 2
```

여러분은 ``foo``의 정의가 이전처럼 같은 정의 항등식을 만족하는 것을 확인할 수 있습니다.

어떤 함수형 프로그래밍 언어는 *불완전한 패턴* 기능을 지원합니다. 이 언어들에서 인터프리터는 예외을 만들거나 불완전한 경우에 대한 임의의 값을 반환합니다. 우리는 ``Inhabited`` 유형 클래스를 사용하여 임의값 접근법을 모사할 수 있습니다. 대략적으로 ``Inhabited α``의 원소는 ``α``의 원소가 있다는 사실의 목격자입니다. [유형 클래스 장](./type_classes.md)에서 우리는 린이 적절한 기반 유형이 머물러 있고, 자동적으로 다른 생성 유형이 머물러 있는지 추론하는 것을 배울 수 있음을 볼 예정입니다. 이 기초로부터 표준 라이브러리는 임의의 거주 유형에 대해 기본 원소 ``defaulty``를 제공합니다.

우리는 불완전한 패턴을 모사하려고 ``Option α``형을 사용할 수도 있습니다.
이 아이디어는 제공받은 패턴에 대해 ``some a``를 반환하는 것입니다. 그리고 불완전한 경우에 대해 ``none``을 사용합니다. 다음 예제는 두 접근법을 보여줍니다.

```lean
def f1 : Nat → Nat → Nat
  | 0, _  => 1
  | _, 0  => 2
  | _, _  => default  -- the "incomplete" case

example : f1 0     0     = 1       := rfl
example : f1 0     (a+1) = 1       := rfl
example : f1 (a+1) 0     = 2       := rfl
example : f1 (a+1) (b+1) = default := rfl

def f2 : Nat → Nat → Option Nat
  | 0, _  => some 1
  | _, 0  => some 2
  | _, _  => none     -- the "incomplete" case

example : f2 0     0     = some 1 := rfl
example : f2 0     (a+1) = some 1 := rfl
example : f2 (a+1) 0     = some 2 := rfl
example : f2 (a+1) (b+1) = none   := rfl
```

방정식 컴파일러는 영리합니다. 여러분이 다음 정의에서 어떤 경우라도 빠트리면, 오류 메시지가 어떤 것이 다뤄지지 못했는지 알릴 것입니다.

```lean
def bar : Nat → List Nat → Bool → Nat
  | 0,   _,      false => 0
  | 0,   b :: _, _     => b
  | 0,   [],     true  => 7
  | a+1, [],     false => a
  | a+1, [],     true  => a + 1
  | a+1, b :: _, _     => a + b
```

이것은 적절한 상황에서 ``casesOn`` 대신  "if ... then ... else"을 사용할 수도 있습니다.

```lean
def foo : Char → Nat
  | 'A' => 1
  | 'B' => 2
  | _   => 3

#print foo.match_1
```

구조적 재귀와 귀납
----------------------------------

방정식 컴파일러를 강력하게 만드는 것은 재귀적인 정의를 지원한다는 점입니다. 다음 세 섹션에서 우리는 개별적으로 설명할 예정입니다.

- 구조적으로 재귀적인 정의
- 잘 세워진 재귀적 정의
- 상호적으로 재귀적인 정의

폭넓게 말하자면, 방정식 컴파일러는 다음 형태의 입력을 처리합니다.

```
def foo (a : α) : (b : β) → γ
  | [patterns₁] => t₁
  ...
  | [patternsₙ] => tₙ
```

여기서 ``(a : α)``는 매개변수의 나열입니다. 패턴 매칭이 일어나는 ``(b : β)``은 인수의 나열입니다. 그리고 ``γ``는 ``a``와 ``b``에 의존할 수 있는 임의의 유형입니다. 각 줄은 ``β``의 각 원소에 대해 한 개씩 같은 수의 패턴을 포함해야 합니다. 우리가 봤던 것처럼 패턴은 생성자가 다른 패턴을 적용한 변수이거나 그 형태를 무언가로 정규화한 표현식입니다. (여기서 비생성자는 ``[matchPattern]`` 속성으로 표시되었습니다.) 생성자의 출현은 제시된 변수로 표현된 생성자에 대한 인수로 경우를 신속히 나눕니다. 이들이 패턴 매칭에 핵심 역할을 하지 않더라도 [의존적인 패턴 매칭 섹션](#dependent_pattern_matching)에서 우리는 이것이 때때로 표현식 유형 확인을 만드는데 필요한 패턴에 대해 명시적으로 포함될 필요가 있음을 볼 것입니다. 이들은 이런 이유로 "접근할 수 없는 패턴"으로 불립니다. 그러나 우리는 [의존적인 패턴 매칭 섹션](#dependent_pattern_matching) 전까지 그런 접근할 수 없는 패턴을 사용할 필요는 없을 것입니다.

우리가 지난 섹션에서 보았듯이, 항 ``t₁, ..., tₙ``은 대응되는 패턴에서 도입된 임의의 변수 뿐만 아니라 임의의 매개변수 ``a``를 사용할 수 있게 만듭니다. 재귀와 귀납을 가능하게 만드는 것은 이들이 ``foo``에 대한 재귀적인 호출을 포함할 수 있다는 점 입니다. 이 섹션에서 우리는 *구조적 재귀*를 다룰 예정입니다. 여기서 ``foo``에 대한 인수는 좌변에 대한 패턴의 부분항인 ``:=``의 우변에서 나타납니다. 아이디어는 이들이 구조적으로 더 작고 그러므로 앞 단에서 귀납형으로 나타날 수 있다는 것입니다. 이제 방정식 컴파일러를 사용해 정의될 마지막 장의 구조적 재귀에 대한 몇 가지 예제가 있습니다.

```lean
open Nat
def add : Nat → Nat → Nat
  | m, zero   => m
  | m, succ n => succ (add m n)

theorem add_zero (m : Nat)   : add m zero = m := rfl
theorem add_succ (m n : Nat) : add m (succ n) = succ (add m n) := rfl

theorem zero_add : ∀ n, add zero n = n
  | zero   => rfl
  | succ n => congrArg succ (zero_add n)

def mul : Nat → Nat → Nat
  | n, zero   => zero
  | n, succ m => add (mul n m) n
```

``zero_add``의 증명은 귀납적 증명은 실제로 린에서 재귀의 한 형태라는 점을 명확히 합니다.

위 예제에서 ``add``에 대해 정의한 방정식은 정의로부터 성립함을 보여줍니다. 그리고 ``mul``에서 같은 방식으로 참이 됨을 보입니다. 방정식 컴파일러는 직관적인 구조적 재귀와 같은 한 언제든 이것이 성립함을 보장하려고 시도합니다. 하지만 다른 상황에서 축약은 *명제적으로*만 성립합니다. 즉, 명시적으로 적용해야 하는 등식 정리입니다. 방정식 컴파일러는 그런 정리를 내부적으로 생성합니다. 이들은 사용자로부터 직접 사용되기 위한 것이 아니라 오히려 `simp` 전략이 필요할 때 사용되도록 설정됩니다. 따라서 `zero_add`의 다음 증명들은 모두 작동합니다.

```lean
open Nat
# def add : Nat → Nat → Nat
#   | m, zero   => m
#   | m, succ n => succ (add m n)
theorem zero_add : ∀ n, add zero n = n
  | zero   => by simp [add]
  | succ n => by simp [add, zero_add]
```

<!--
In fact, because in this case the defining equations hold
definitionally, we can use `dsimp`, the simplifier that uses
definitional reductions only, to carry out the first step.

.. code-block:: lean

    namespace hidden

    inductive nat : Type
    | zero : nat
    | succ : nat → nat

    namespace nat

    def add : nat → nat → nat
    | m zero     := m
    | m (succ n) := succ (add m n)

    local infix ` + ` := add

    -- BEGIN
    theorem zero_add : ∀ n, zero + n = n
    | zero     := by dsimp [add]; reflexivity
    | (succ n) := by dsimp [add]; rw [zero_add n]
    -- END

    end nat
    end hidden
-->

패턴 매칭의 정의에서처럼 구조적 재귀나 귀납에 대한 매개변수는 콜론 앞에 나타날 수 있습니다. 그런 매개변수들은 단순히 정의가 처리되기 전에 지역 상황에 추가됩니다. 예를 들어 덧셈의 정의는 다음과 같이 작성될 수 있습니다.

```lean
open Nat
def add (m : Nat) : Nat → Nat
  | zero   => m
  | succ n => succ (add m n)
```

여러분은 `match`를 사용해 위의 예제를 쓸 수도 있습니다.

```lean
open Nat
def add (m n : Nat) : Nat :=
  match n with
  | zero   => m
  | succ n => succ (add m n)
```

구조적 재귀의 더 흥미로운 예제는 피보나치 함수 ``fib``로부터 제시됩니다.

```lean
def fib : Nat → Nat
  | 0   => 1
  | 1   => 1
  | n+2 => fib (n+1) + fib n

example : fib 0 = 1 := rfl
example : fib 1 = 1 := rfl
example : fib (n + 2) = fib (n + 1) + fib n := rfl

example : fib 7 = 21 := rfl
```

여기서 (정의로 인해 ``succ (succ n)``과 같은)``n + 2``에서 ``fib``의 함수값은 (``succ n``와 정의로 인해 동등한)``n + 1`` 에서의 값과 ``n``에서 값에 대하여 정의되었다. 이것은 계산 시간이 ``n``에 대해 지수적인 피보나치 함수를 계산하는 악명높게 비효율적인 방식이지만 여기 더 나은 방식이 있습니다.

```lean
def fibFast (n : Nat) : Nat :=
  (loop n).1
where
  loop : Nat → Nat × Nat
    | 0   => (0, 1)
    | n+1 => let p := loop n; (p.2, p.1 + p.2)

#eval fibFast 100
```

`where` 대신 `let rec`을 사용한 같은 정의가 있습니다.

```lean
def fibFast (n : Nat) : Nat :=
  let rec loop : Nat → Nat × Nat
    | 0   => (0, 1)
    | n+1 => let p := loop n; (p.2, p.1 + p.2)
  (loop n).1
```

두 경우 모두에 대해 린은 부가 함수 `fibFast.loop`를 만듭니다.

구조적 재귀를 다루려고 방정식 컴파일러는 각 귀납적으로 정의된 유형으로부터 자동적으로 생성된 상수 ``below``와 ``brecOn``을 사용하여 *course-of-values*재귀를 사용합니다. 여러분은 ``Nat.below``과 ``Nat.brecOn``의 유형을 봄으로써 이것이 어떻게 동작하는지에 대해 감을 얻을 수 있습니다.

```lean
variable (C : Nat → Type u)

#check (@Nat.below C : Nat → Type u)

#reduce @Nat.below C (3 : Nat)

#check (@Nat.brecOn C : (n : Nat) → ((n : Nat) → @Nat.below C n → C n) → C n)
```

``@Nat.below C (3 : nat)``형은 ``C 0``, ``C 1``과 ``C 2``의 원소를 저장하는 데이터 구조입니다.
course-of-values 재귀는 ``Nat.brecOn``로 구현됩니다. 이것은 ``@Nat.below C n``의 원소로 나타났던 함수의 모든 이전의 값들로 특정 입력 ``n``에 대해 ``(n : Nat) → C n``형의 종속함수의 값을 정의할 수 있게 해줍니다. 

course-of-values 재귀의 사용은 방정식 컴파일러가 함수를 끝내는 린 커널을 정당화하는데 사용하는 한 기법입니다. 다른 함수형 프로그래밍 언어의 컴파일러와 마찬가지로 이것은 재귀 함수를 컴파일하는 코드 생성기에 영향을 끼치지 않습니다. `#eval fib <n>`가 `<n>`에 대해 지수적이었음을 기억하세요.
다른 한편 `#reduce fib <n>`는 `brecOn` 생성자에 기반한 커널에 보내져 정의를 사용하기 때문에 효율적입니다.

```lean
def fib : Nat → Nat
  | 0   => 1
  | 1   => 1
  | n+2 => fib (n+1) + fib n

-- #eval fib 50 -- slow
#reduce fib 50  -- fast

#print fib
```

재귀적 정의의 또 다른 좋은 예제는 리스트 ``append`` 함수입니다.

```lean
def append : List α → List α → List α
  | [],    bs => bs
  | a::as, bs => a :: append as bs

example : append [1, 2, 3] [4, 5] = [1, 2, 3, 4, 5] := rfl
```

여기 또 다른 것이 있습니다. 이것은 둘 중의 한 리스트의 원소가 소진될 때까지 첫 리스트의 원소를 두 번째 리스트의 원소와 더합니다.

```lean
def listAdd [Add α] : List α → List α → List α
  | [],      _       => []
  | _,       []      => []
  | a :: as, b :: bs => (a + b) :: listAdd as bs

#eval listAdd [1, 2, 3] [4, 5, 6, 6, 9, 10]
-- [5, 7, 9]
```

여러분은 아래 연습에서 비슷한 예제로 실험해보길 권유합니다.

잘 세워진 재귀와 귀납
------------------------------------

종속 유형론은 잘 세워진 재귀를 부호화하고 정당화하기에 충분히 강력합니다. 우선 이것이 어떻게 동작하는지 이해하는데 필요한 논리적 배경으로 시작합시다.

린의 표준 라이브러리는 두 술어 ``Acc r a``과 ``WellFounded r``을 정의합니다. 여기서 ``r``은 ``α``형에 대한 이항 관계이고 ``a``는 ``α``형 원소입니다.

```lean
variable (α : Sort u)
variable (r : α → α → Prop)

#check (Acc r : α → Prop)
#check (WellFounded r : Prop)
```

우선 ``Acc``은 귀납적으로 정의된 술어입니다. 이것의 정의에 따르면 ``Acc r x``는 ``∀ y, r y x → Acc r y``과 동등합니다. 여러분이 ``r y x``을 순서 관계 ``y ≺ x``의 일종으로 나타났다고 생각한다면 ``Acc r x``는 ``x``가 아래로부터 접근가능하다고 말합니다. 이 관점으로부터 그것의 모든 전임자들은 접근가능합니다. 특히 ``x``의 전임자가 없다면 그것은 접근가능합니다. 임의의 유형 ``α``에 대해서 우리는 그것의 모든 전임자들을 우선으로 값을 할당하여 ``α``의 각 접근 가능한 원소에 값을 재귀적으로 할당할 수 있어야 합니다.

``WellFounded r``로 표시되어 잘 세워진 명제 ``r``는 바로 그 유형의 모든 원소가 접근 가능한 명제입니다. 위의 고려로부터 만약 ``r``이 ``α``형에 대해 잘 세워진 관계이면, 우리는 관계 ``r``에 대해서 ``α``에 대해 잘 세워진 재귀의 원리를 가져야 합니다. 그리고 물론 우리는 이를 갖습니다. 표준 라이브러리는 바로 그 목적을 담당하는 ``WellFounded.fix``를 정의합니다.

```lean
set_option codegen false
def f {α : Sort u}
      (r : α → α → Prop)
      (h : WellFounded r)
      (C : α → Sort v)
      (F : (x : α) → ((y : α) → r y x → C y) → C x)
      : (x : α) → C x := WellFounded.fix h F
```

여기 문자의 긴 캐스트가 있지만 우리는 이미 유형 ``α``, 관계 ``r`` 그리고 가정 ``h``으로 된 첫 블럭을 봤습니다. 여기서 ``r``은 잘 세워진 것입니다. 변수 ``C``는 재귀적 정의의 동기를 나타냅니다. 각 원소 ``x : α``에 대하여 우리는 ``C x``의 원소를 생성하고자 합니다. 함수 ``F``는 그것을 하는데 귀납적인 요리법을 제공합니다. 이것은 ``x``의 각 선행자 ``y``에 대해``C y``의  원소가 주어진 경우 원소 ``C x``를 생성하는 법을 우리에게 말해줍니다.

``WellFounded.fix``는 귀납 원리와 같이 동등하게 동작함을 주목하세요. 이것은 만약 ``≺``이 잘 세워졌고 여러분이 ``∀ x, C x``을 증명하기 원한다고 말하면, 이는 임의의  ``x``에 대해 우리가 ``∀ y ≺ x, C y``이면 ``C x``임을 보이는 것으로 충분합니다.

위의 예제에서 우리는 옵션 `codegen`이 실패하도록 설정했습니다. 왜냐하면 코드 생성기는 현재  `WellFounded.fix`를 지원하지 않기 때문입니다. 함수 `WellFounded.fix`은 린이 함수 종료를 정당화하는데 사용하는 또 다른 도구입니다.

린은 자연수에 대한 평상시 순서 ``<``가 잘 세워졌다는 것을 압니다. 이것도 다른 것으로부터 새로운 잘 세워진 순서를 생성하는 많은 방법을 알고 있습니다. 예를 들어 사전적 순서를 사용하는 것입니다.

여기 있는 것은 본질적으로 표준 라이브러리에서 찾을 수 있는 자연수에 대한 나눗셈 정의입니다.

```lean
open Nat

theorem div_rec_lemma {x y : Nat} : 0 < y ∧ y ≤ x → x - y < x :=
  fun h => sub_lt (Nat.lt_of_lt_of_le h.left h.right) h.left

def div.F (x : Nat) (f : (x₁ : Nat) → x₁ < x → Nat → Nat) (y : Nat) : Nat :=
  if h : 0 < y ∧ y ≤ x then
    f (x - y) (div_rec_lemma h) y + 1
  else
    zero

set_option codegen false
def div := WellFounded.fix (measure id).wf div.F

#reduce div 8 2 -- 4
```

정의는 무언가 헤아리기가 어렵습니다. 여기서 재귀는 ``x``에 있습니다. 그리고 ``div.F x f : Nat → Nat``는 고정된 ``x``에 대해 "``y``로 나눔" 함수를 반환합니다. 여러분은 재귀를 위한 요리법인 ``div.F``의 두 번째 인수가 ``x``보다 작은 모든 ``x₁``값에 대한 ``y`` 함수로 나눠진 것을 반환하기로 한 함수임을 기억해야만 합니다.

방정식 컴파일러는 이 같은 정의를 만드는 데 더 편리하도록 설계되었습니다. 이것은 다음을 받습니다.

**할 것: 린4가 지원하는 잘 세워진 식을 대기하기**

.. code-block:: lean

    namespace hidden
    open nat
    
    -- BEGIN
    def div : ℕ → ℕ → ℕ
    | x y :=
      if h : 0 < y ∧ y ≤ x then
        have x - y < x,
          from sub_lt (lt_of_lt_of_le h.left h.right) h.left,
        div (x - y) y + 1
      else
        0
    -- END
    
    end hidden

방정식 컴파일러가 재귀적 정의를 만날 때, 는 처음 구조적 재귀를 시도하고 그게 실패했을 때 잘 세워진 재귀로 대체됩니다. 이 경우 자연수에 대한 잘 세워진 재귀의 가능성을 감지하여 순서쌍 ``(x, y)``에 대해 평범한 사전적 순서를 사용합니다. 방정식 컴파일러의 속과 그 자체는 주어진 가정 하에서 ``x -y``가 ``x``보다 작다는 것을 유도할만큼 영리하지 않습니다. 그러나 우리는 그것을 지역 맥락에 이 사실을 넣음으로써 도울 수 있습니다. 방정식 컴파일러는 그런 정보에 대해 지역 맥락에서 보고 그것을 찾을 때 사용하기 좋게 둡니다.

``div`` 로 방정식을 정의하는 것은 정의로부터 성립하지 *않습니다.* 그래도 방정식은 ``rewrite``와 ``simp``를 사용할 수 있습니다.  단순화기는 여러분이 맹목적으로 적용한다면 무한루프를 돌 것입니다. 그러나 ``rewrite``는 트릭을 씁니다.

.. code-block:: lean

    namespace hidden
    open nat
    
    def div : ℕ → ℕ → ℕ
    | x y :=
      if h : 0 < y ∧ y ≤ x then
        have x - y < x,
          from sub_lt (lt_of_lt_of_le h.left h.right) h.left,
        div (x - y) y + 1
      else
        0
    
    -- BEGIN
    example (x y : ℕ) :
      div x y = if 0 < y ∧ y ≤ x then div (x - y) y + 1 else 0 :=
    by rw [div]
    
    example (x y : ℕ) (h : 0 < y ∧ y ≤ x) :
      div x y = div (x - y) y + 1 :=
    by rw [div, if_pos h]
    -- END
    
    end hidden

다음 예제는 이것이 어떤 자연수를 이진 표현식으로 바꾸고 0과 1의 리스트로 나타낸다는 점에서 비슷합니다. 우리는 방정식 컴파일러에게 재귀호출이 감소한다는 증거를 주어야 합니다. 여기서 우리는 ``sorry``로 했습니다. ``sorry``는 바이트코드 평가기가 함수를 성공적으로 평가하는 것을 막지 못합니다.

.. code-block:: lean

    def nat_to_bin : ℕ → list ℕ
    | 0       := [0]
    | 1       := [1]
    | (n + 2) :=
      have (n + 2) / 2 < n + 2, from sorry,
      nat_to_bin ((n + 2) / 2) ++ [n % 2]
    
    #eval nat_to_bin 1234567

마지막 예제로 우리는 Ackermann 함수가 직접적으로 정의되는 것을 관찰합니다. 왜냐하면 이것은 자연수에 대해 사전적 순서로 잘 세워짐으로 정당활 될 수 있기 때문입니다.

.. code-block:: lean

    def ack : nat → nat → nat
    | 0     y     := y+1
    | (x+1) 0     := ack x 1
    | (x+1) (y+1) := ack x (ack (x+1) y)
    
    #eval ack 3 5

린의 잘 세워진 관계식을 추론하는 메커니즘과 재귀적인 호출이 줄어든다는 증명은 여전히 기초적인 상태입니다. 그들은 시간이 지나면서 개선될 것입니다. 그들이 동작할 때, 그들은 수동적으로 ``WellFounded.fix``를 사용하는 것보다 함수를 정의하는 훨씬 더 편리한 방법을 제공합니다. 그들이 동작하지 않을 때 후자는 백업으로 항상 사용할 수 있습니다.

.. 할 것: 결국, 잘 세워진을 사용하는 것을 기술하기.

.. 중접되고 상호적인 재귀

상호적인 재귀
----------------

**할 것: 린4가 지원하는 잘 세워진 식을 대기하기**

린도 상호적인 재귀적 정의를 지원합니다. numref`상호적이고 재귀적인 귀납형`에서 기술한 바처럼 문법은 상호 귀납적인 유형에 대한 것과 비슷합니다. 여기 예제가 있습니다.

.. code-block:: lean

    mutual def even, odd
    with even : nat → bool
    | 0     := tt
    | (a+1) := odd a
    with odd : nat → bool
    | 0     := ff
    | (a+1) := even a
    
    example (a : nat) : even (a + 1) = odd a :=
    by simp [even]
    
    example (a : nat) : odd (a + 1) = even a :=
    by simp [odd]
    
    lemma even_eq_not_odd : ∀ a, even a = bnot (odd a) :=
    begin
      intro a, induction a,
      simp [even, odd],
      simp [*, even, odd]
    end

이를 상호적인 정의로 만드는 것은 ``even``이``odd``에 대해 재귀적으로 정의되었고, 한편 ``odd``는 ``even``에 대해 재귀적으로 정의되었다는 점이다. 후드 아래에서 이것은 단일 재귀적 정의로 컴파일된다. 내부적으로 정의된 함수는 인수로써 ``even``의 입력으로나 ``odd``의 입력으로 합 유형의 원소로 받습니다. 그럼 이것은 입력에 대한 적절한 출력을 반환합니다. 이런 함수를 정의하려면 린은 적절히 잘 세워진 척도를 사용합니다. 내부는 사용자로부터 숨겨지도록 의도되었습니다. 그런 정의를 만들어 사용하는 정식 방법은 ``rewrite``나 ``simp``를 우리가 위에서 했던 것처럼 사용하는 것입니다.

상호적으로 재귀적인 정의도 :numref:`상호적이고 중첩된 재귀형`에서 설명한 것처럼 상호적이고  중첩된 귀납형을 다루는 자연스러운 방식을 제공합니다.  ``even``과 ``odd``을 상호적으로 귀납적인 술어의 정의로 호출한다면 다음 예제와 같이 나타날 것입니다.

.. code-block:: lean

    mutual inductive even, odd
    with even : ℕ → Prop
    | even_zero : even 0
    | even_succ : ∀ n, odd n → even (n + 1)
    with odd : ℕ → Prop
    | odd_succ : ∀ n, even n → odd (n + 1)

생성자 ``even_zero``, ``even_succ``과 ``odd_succ``은 수가 짝수인지 홀수인지 보이는데 긍정적인 수단을 제공한다. 우리는 귀납형이 0은 홀수가 아니다는 것, 그리고 후자는 두 함의의 역이라는 것이 생성자들에 의해 만들어졌다는 사실을 이용할 필요가 있습니다. 평소처럼, 생성자는 유형이 정의된 이름을 딴 이름공간에 남아있고, 명령  ``open even odd``는 우리가 그들에게 더 편리하게 접근하도록 해줍니다.

.. code-block:: lean

    mutual inductive even, odd
    with even : ℕ → Prop
    | even_zero : even 0
    | even_succ : ∀ n, odd n → even (n + 1)
    with odd : ℕ → Prop
    | odd_succ : ∀ n, even n → odd (n + 1)
    
    -- BEGIN
    open even odd
    
    theorem not_odd_zero : ¬ odd 0.
    
    mutual theorem even_of_odd_succ, odd_of_even_succ
    with even_of_odd_succ : ∀ n, odd (n + 1) → even n
    | _ (odd_succ n h) := h
    with odd_of_even_succ : ∀ n, even (n + 1) → odd n
    | _ (even_succ n h) := h
    -- END

또 다른 예제에서 우리가 중접된 귀납형을 재귀적으로 항들의 집합을 정의하고자 사용한다고 합시다. 그러면 항은 (문자열로 이름이 주어진)상수이거나 상수의 리스트에 상수를 적용한 결과입니다.

.. code-block:: lean

    inductive term
    | const : string → term
    | app   : string → list term → term

그럼 우리는 상호적으로 재귀적인 정의를 항의 리스트에서 나타나는 수 뿐만 아니라 항 속의 상수의 수를 세는데 사용할 수 있습니다.

.. code-block:: lean

    inductive term
    | const : string → term
    | app   : string → list term → term
    
    -- BEGIN
    open term
    
    mutual def num_consts, num_consts_lst
    with num_consts : term → nat
    | (term.const n)  := 1
    | (term.app n ts) := num_consts_lst ts
    with num_consts_lst : list term → nat
    | []      := 0
    | (t::ts) := num_consts t + num_consts_lst ts
    
    def sample_term := app "f" [app "g" [const "x"], const "y"]
    
    #eval num_consts sample_term
    -- END


의존적 패턴 매칭
--------------------------

패턴 매칭의 모든 예제로부터 우리는 :numref:`패턴 매칭`에서 ``cases_on``과 ``rec_on``를 사용해 쉽게 쓸 수 있음을 고려했습니다. 하지만 이것은 ``vector α n`` 같이 인덱스된 귀납형 군의 경우에는 적용이 안됩니다. 왜냐하면 경우를 나누기는 인덱스의 값에 제약을 부과하기 때문입니다. 방정식 컴파일러가 없다면 우리는 ``map``, ``zip``과 ``unzip``같은 아주 단순한 함수를 재귀자를 사용해서 정의하려면 아주 많은 보일러 플레이트 코드가 필요할 것입니다. 어려움을 이해하려면 벡터 ``v : vector α (succ n)``를 받고 첫 번째 원소를 삭제하는 함수 ``tail``를 정의하는데 무엇이 필요한지 고려해보세요. 첫 고려사항은 ``casesOn`` 함수를 사용하는 것입니다.

```lean
inductive Vector (α : Type u) : Nat → Type u
  | nil  : Vector α 0
  | cons : α → {n : Nat} → Vector α n → Vector α (n+1)

namespace Vector

#check @Vector.casesOn
/-
  {α : Type u}
  → {motive : (a : Nat) → Vector α a → Sort v} →
  → {a : Nat} → (t : Vector α a)
  → motive 0 nil
  → ((a : α) → {n : Nat} → (a_1 : Vector α n) → motive (n + 1) (cons a a_1))
  → motive a t
-/

end Vector
```

그러나 ``nil`` 경우에 우리가 돌려줘야 하는 값은 무엇인가요? 무언가 재밌는 일이 일어나고 있습니다. 만약  ``v``가 ``Vector α (succ n)``형이고 그것은 nil일 *일 수 없습니다.* 그러나 ``casesOn``에 대해 구별하는 법이 명확하지 않습니다.

우리의 방법은 부가적인 함수를 정의하는 것입니다.

```lean
# inductive Vector (α : Type u) : Nat → Type u
#   | nil  : Vector α 0
#   | cons : α → {n : Nat} → Vector α n → Vector α (n+1)
# namespace Vector
def tailAux (v : Vector α m) : m = n + 1 → Vector α n :=
  Vector.casesOn (motive := fun x _ => x = n + 1 → Vector α n) v
    (fun h : 0 = n + 1 => Nat.noConfusion h)
    (fun (a : α) (m : Nat) (as : Vector α m) =>
     fun (h : m + 1 = n + 1) =>
       Nat.noConfusion h (fun h1 : m = n => h1 ▸ as))

def tail (v : Vector α (n+1)) : Vector α n :=
  tailAux v rfl
# end Vector
```

``nil`` 경우에서 ``m``은 ``0``으로 개체화되고 ``noConfusion``은 ``0 = succ n``이 일어날 수 없다는 사실을 사용하게 만듭니다.  그렇지 않으면 ``v``는 ``a :: w``꼴이고 길이 ``m``의 벡터에서 길이 ``n``의 벡터로 이를 바꾼 후에 우리는 단순히 ``w``를 반환할 수 있습니다.

``tail``을 정의하는데 어려움은 인덱스 사이의 관계를 유지해야 한다는 것입니다.
 ``tailAux``의 가정 ``e : m = n + 1``은 ``n``과 작은 전제와 연관된 인덱스 사이의 관계를 소통하는데 사용됩니다.
게다가 ``zero = n + 1`` 경우는 도달할 수 없고 정식 방법으로 이 경우를 버리려면 ``noConfusion``을 사용합니다.

하지만 ``tail`` 함수는 재귀적인 방정식을 사용해 정의하기 쉽습니다. 그리고 방정식 컴파일러는 모든 보일러 플레이트 코드를 우리를 위해 자동적으로 만들어 줍니다. 여기 비슷한 예제가 많이 있습니다.


```lean
# inductive Vector (α : Type u) : Nat → Type u
#   | nil  : Vector α 0
#   | cons : α → {n : Nat} → Vector α n → Vector α (n+1)
# namespace Vector
def head : {n : Nat} → Vector α (n+1) → α
  | n, cons a as => a

def tail : {n : Nat} → Vector α (n+1) → Vector α n
  | n, cons a as => as

theorem eta : ∀ {n : Nat} (v : Vector α (n+1)), cons (head v) (tail v) = v
  | n, cons a as => rfl

def map (f : α → β → γ) : {n : Nat} → Vector α n → Vector β n → Vector γ n
  | 0,   nil,       nil       => nil
  | n+1, cons a as, cons b bs => cons (f a b) (map f as bs)

def zip : {n : Nat} → Vector α n → Vector β n → Vector (α × β) n
  | 0,   nil,       nil       => nil
  | n+1, cons a as, cons b bs => cons (a, b) (zip as bs)
# end Vector
```

우리는 재귀 방정식을 ``head nil`` 같이 "도달할 수 없는" 경우에 대해 생략할 수 있음을 주목하세요. 인덱스된 군을 위한 자동적으로 생성된 정의는 직관과는 거리가 멉니다. 예를 들어

```lean
# inductive Vector (α : Type u) : Nat → Type u
#   | nil  : Vector α 0
#   | cons : α → {n : Nat} → Vector α n → Vector α (n+1)
# namespace Vector
def map (f : α → β → γ) : {n : Nat} → Vector α n → Vector β n → Vector γ n
  | 0,   nil,       nil       => nil
  | n+1, cons a as, cons b bs => cons (f a b) (map f as bs)

#print map
#print map.match_1
# end Vector
```

심지어 ``map`` 함수는 ``tail`` 함수보다 손으로 정의하기에는 더 번거롭습니다. 우리는 여러분이 이를 ``recOn``, ``casesOn``과 ``noConfusion``을 사용해 시도해보길 권합니다.

접근할 수 없는 패턴
------------------

떄때로 종속 매칭 패턴에서 인수는 정의에 반드시 필요하지 않습니다. 그럼에도 표현식의 유형을 적절하게 특수화하는데 포함될 필요가 있습니다. 린은 사용자가 그런 부분항을 패턴 매칭에 대해 *inaccessible*으로 표시하도록 허용합니다. 이 주석은 필수적입니다. 예를 들어 좌변에서 나타나는 항이 변수도 생성자 적용도 아닐 때, 이들은 패턴 매칭에 적적한 대상이 아니기 때문입니다. 우리는 그런 접속불가한 패턴을 패턴의 "신경쓰지 않는" 성분의 관점으로 볼 수 있습니다. 여러분은 ``.(t)``와 같이 작성하여 접근불가한 부분항을 선언할 수 있습니다. 만약 접근불가능한 패턴이 추론될 수 있다면 ``_``와 같이 쓸 수 있습니다.

다음 예제에서 우리는 "``f``의 이미지에 있음" 속성을 정의하는 귀납형을 선언합니다. 여러분은 ``ImageOf f b``형 원소를 ``b``가 ``f``의 이미지에 있다는 증거로 볼 수 있습니다. 이로써 생성자 ``imf``는 그런 증거를 만드는데 사용됩니다. 그런 다음 ``f``의 이미지에서 매핑된 요소로 가져오는 "역"함수가 있는 임의의 함수 ``f``를 정의할 수 있습니다. 입력 규칙은 우리가 첫 인수에 대해 ``f a``로 쓰도록 합니다. 그러나 이 항은 변수도 생성자 적용도 아닙니다. 그리고 패턴 매칭 정의에서 어떤 역할도 하지 않습니다. 아래에서 함수 ``inverse``를 정의하려면 우리는 ``f a``를 접근 불가한 것으로 표시*해야만* 합니다.

```lean
inductive ImageOf {α β : Type u} (f : α → β) : β → Type u where
  | imf : (a : α) → ImageOf f (f a)

open ImageOf

def inverse {f : α → β} : (b : β) → ImageOf f b → α
  | .(f a), imf a => a

def inverse' {f : α → β} : (b : β) → ImageOf f b → α
  | _, imf a => a
```

위 예제에서 접근불가 주석은 ``f``가 패턴 매칭 변수가 *아님*을 명확히 합니다.

접근불가한 패턴은 명확성과 종속 패턴 매칭을 활용하는 정의 제어를 위해 사용될 수 있습니다. 유형의 원소의 두 벡터를 더하는 함수 ``Vector.add,``의 다음 정의를 고려해보세요. 그 유형은 연관된 덧셈함수를 가지고 있다고 가정합니다.

```lean
inductive Vector (α : Type u) : Nat → Type u
  | nil  : Vector α 0
  | cons : α → {n : Nat} → Vector α n → Vector α (n+1)

namespace Vector

def add [Add α] : {n : Nat} → Vector α n → Vector α n → Vector α n
  | 0,   nil,       nil       => nil
  | n+1, cons a as, cons b bs => cons (a + b) (add as bs)

end Vector
```

인수``{n : Nat}`` 은 콜론 뒤에 나타납니다. 왜냐하면 이것은 정의 전체에 대해 고정될 수 없기 때문입니다.  이 정의를 구현할 때 방정식 컴파일러는 첫 번째 인수가 ``0``이거나 ``n+1``의 꼴인지를 구분하도록 경우를 구분하는 것으로 시작합니다.  이것은 다음 두 인수에 대한 중첩된 경우 분할을 따르고 각 경우에서 방정식 컴파일러는 첫 번째 패턴과 적합하지 않은 경우를 배제합니다.

그러나 사실 경우 분할은 첫 번째 인수에 대해 필요하지 않습니다. 두 번째 인수에 대해 경우를 나누었을 때 ``Vector``를 위한 ``casesOn`` 제거자가 자동적으로 이 인수를 추출하고 그것을 ``0``과 ``n + 1``으로 대체합니다.  접근 불가한 패턴을 사용하여 우리는 방정식 컴파일러가 ``n``에 대해 경우를 나누는 것을 즉시 막도록 할 수 있습니다.

```lean
# inductive Vector (α : Type u) : Nat → Type u
#   | nil  : Vector α 0
#   | cons : α → {n : Nat} → Vector α n → Vector α (n+1)
# namespace Vector

def add [Add α] : {n : Nat} → Vector α n → Vector α n → Vector α n
  | .(_),   nil,       nil       => nil
  | .(_), cons a as, cons b bs => cons (a + b) (add as bs)

# end Vector
```

접근 불가한 패턴으로 위치를 표시하는 것은 우선 방정식 컴파일러에게 인수의 모양이 다른 인수에 부과된 제약으로부터 추론될 수 있어야 한다고 말합니다. 그리고 두 번째로 첫 인수가 패턴 매칭에 참여하지 *않아야* 합니다.

접근 불가한 패턴 `.(_)`은 편의상 `_`로 쓸 수 있습니다.

```lean
# inductive Vector (α : Type u) : Nat → Type u
#   | nil  : Vector α 0
#   | cons : α → {n : Nat} → Vector α n → Vector α (n+1)
# namespace Vector

def add [Add α] : {n : Nat} → Vector α n → Vector α n → Vector α n
  | _,   nil,       nil       => nil
  | _, cons a as, cons b bs => cons (a + b) (add as bs)

# end Vector
```

위에서 언급했듯이 인수 ``{n : Nat}``은 패턴 매칭의 일부입니다. 왜냐하면 이것은 정의 전체에 대해 고정될 수 없기 때문입니다. 린의 이전 버전에서 사용자는 이 별도의 구별자를 포함시켜야 하는 것이 종종 성가신 일임을 알았습니다. 따라서 린4에서 별도의 구별자를 자동적으로 포함시켜주는 새로운 기능 *discriminant refinement*을 구현했습니다.

```lean
# inductive Vector (α : Type u) : Nat → Type u
#   | nil  : Vector α 0
#   | cons : α → {n : Nat} → Vector α n → Vector α (n+1)
# namespace Vector

def add [Add α] {n : Nat} : Vector α n → Vector α n → Vector α n
  | nil,       nil       => nil
  | cons a as, cons b bs => cons (a + b) (add as bs)

# end Vector
```

*암시적인 자동 결합(auto bound implicits)* 기능과 결합할 때 여러분은 선언을 더 단순화 해 작성할 수 있습니다.

```lean
# inductive Vector (α : Type u) : Nat → Type u
#   | nil  : Vector α 0
#   | cons : α → {n : Nat} → Vector α n → Vector α (n+1)
# namespace Vector

def add [Add α] : Vector α n → Vector α n → Vector α n
  | nil,       nil       => nil
  | cons a as, cons b bs => cons (a + b) (add as bs)

# end Vector
```

이 새로운 기능을 사용하면 여러분은 이전에 정의한 다른 벡터 함수들을 다음과 같이 더 간결하게 쓸 수 있습니다.

```lean
# inductive Vector (α : Type u) : Nat → Type u
#   | nil  : Vector α 0
#   | cons : α → {n : Nat} → Vector α n → Vector α (n+1)
# namespace Vector
def head : Vector α (n+1) → α
  | cons a as => a

def tail : Vector α (n+1) → Vector α n
  | cons a as => as

theorem eta : (v : Vector α (n+1)) → cons (head v) (tail v) = v
  | cons a as => rfl

def map (f : α → β → γ) : Vector α n → Vector β n → Vector γ n
  | nil,       nil       => nil
  | cons a as, cons b bs => cons (f a b) (map f as bs)

def zip : Vector α n → Vector β n → Vector (α × β) n
  | nil,       nil       => nil
  | cons a as, cons b bs => cons (a, b) (zip as bs)
# end Vector
```

매치 표현식
-----------------

린도 많은 함수형 언어에서 발견되다시피 컴파일러에게 *match-with* 표현식을 줍니다.

```lean
def isNotZero (m : Nat) : Bool :=
  match m with
  | 0   => false
  | n+1 => true
```

이것은 평범한 패턴 매칭 정의와 아주 달라보이지 않지만 ``match``가 임의의 인수로 표현식의 어디서든 사용될 수 있다는 점이 다릅니다.

```lean
def isNotZero (m : Nat) : Bool :=
  match m with
  | 0   => false
  | n+1 => true

def filter (p : α → Bool) : List α → List α
  | []      => []
  | a :: as =>
    match p a with
    | true => a :: filter p as
    | false => filter p as

example : filter isNotZero [1, 0, 0, 3, 0] = [1, 3] := rfl
```

여기 또 다른 예제가 있습니다.

```lean
def foo (n : Nat) (b c : Bool) :=
  5 + match n - 5, b && c with
      | 0,   true  => 0
      | m+1, true  => m + 7
      | 0,   false => 5
      | m+1, false => m + 3

#eval foo 7 true false

example : foo 7 true false = 9 := rfl
```

린은 시스템의 모든 부분에서 내부적으로 패턴 매칭을 구현하고자 ``match`` 생성을 사용합니다.
따라서 이 모든 네 정의들은 동일한 알짜 효과를 갖습니다.

```lean
def bar₁ : Nat × Nat → Nat
  | (m, n) => m + n

def bar₂ (p : Nat × Nat) : Nat :=
  match p with
  | (m, n) => m + n

def bar₃ : Nat × Nat → Nat :=
  fun (m, n) => m + n

def bar₄ (p : Nat × Nat) : Nat :=
  let (m, n) := p; m + n
```

이 변수들은 명제를 파괴하는데 똑같이 유용합니다.

```lean
variable (p q : Nat → Prop)

example : (∃ x, p x) → (∃ y, q y) → ∃ x y, p x ∧ q y
 | ⟨x, px⟩, ⟨y, qy⟩ => ⟨x, y, px, qy⟩

example (h₀ : ∃ x, p x) (h₁ : ∃ y, q y)
        : ∃ x y, p x ∧ q y :=
  match h₀, h₁ with
  | ⟨x, px⟩, ⟨y, qy⟩ => ⟨x, y, px, qy⟩


example : (∃ x, p x) → (∃ y, q y) → ∃ x y, p x ∧ q y :=
  fun ⟨x, px⟩ ⟨y, qy⟩ => ⟨x, y, px, qy⟩

example (h₀ : ∃ x, p x) (h₁ : ∃ y, q y)
        : ∃ x y, p x ∧ q y :=
  let ⟨x, px⟩ := h₀
  let ⟨y, qy⟩ := h₁
  ⟨x, y, px, qy⟩
```

지역적인 재귀 선언
---------

여러분은 지역적으로 재귀 선언을 `let rec` 키워드를 사용해 정의할 수 있습니다.

```lean
def replicate (n : Nat) (a : α) : List α :=
  let rec loop : Nat → List α → List α
    | 0,   as => as
    | n+1, as => loop n (a::as)
  loop n []

#check @replicate.loop
-- {α : Type} → α → Nat → List α → List α
```

린은 각 `let rec`에 대해 부가 선언을 만듭니다. 위 예제에서 `replicate`에서 생긴 `let rec loop`에 대해 `replicate.loop` 선언을 만듭니다.
린이 추가적인 매개변수로 `let rec` 선언에서 생긴 임의의 지역변수를 추가함으로써 선언이 닫힌다는 점을 주목하세요. 예를 들어 지역변수 `a`는 `let rec loop`에 나타납니다.

여러분도 전략 모드에서 귀납법으로 증명을 만들 때에 `let rec`을 사용할 수 있습니다.

```lean
# def replicate (n : Nat) (a : α) : List α :=
#  let rec loop : Nat → List α → List α
#    | 0,   as => as
#    | n+1, as => loop n (a::as)
#  loop n []
theorem length_replicate (n : Nat) (a : α) : (replicate n a).length = n := by
  let rec aux (n : Nat) (as : List α)
              : (replicate.loop a n as).length = n + as.length := by
    match n with
    | 0   => simp [replicate.loop]
    | n+1 => simp [replicate.loop, aux n, Nat.add_succ, Nat.succ_add]
  exact aux n []
```

여러분도 부가적인 재귀 선언을 여러분의 정의 뒤에 `where` 절을 사용해서 도입할 수 있습니다.
린은 그들을 `let rec`으로 바꿉니다.

```lean
def replicate (n : Nat) (a : α) : List α :=
  loop n []
where
  loop : Nat → List α → List α
    | 0,   as => as
    | n+1, as => loop n (a::as)

theorem length_replicate (n : Nat) (a : α) : (replicate n a).length = n := by
  exact aux n []
where
  aux (n : Nat) (as : List α)
      : (replicate.loop a n as).length = n + as.length := by
    match n with
    | 0   => simp [replicate.loop]
    | n+1 => simp [replicate.loop, aux n, Nat.add_succ, Nat.succ_add]
```

연습문제
---------

1. 이름공간``Hidden``을 열어 이름 충돌을 피하세요. 그리고 방정식 컴파일러로 덧셈, 곱셈 그리고 거듭제곱을 자연수에 대해 정의하세요. 그 뒤 방정식 컴파일러를 그들의 기본 성질 몇 가지를 유도하는데 사용하세요.

2. 마찬가지로 방정식 컴파일러를 리스트에 대한 몇 가지 기본 연산(``reverse`` 함수 같은)을 정의하는데 사용하세요. 그리고 귀납법으로 리스트에 대한 정리(임의의 리스트 ``xs``에 대해 ``reverse (reverse xs) = xs``이라는 사실 같은 것)를 증명하세요.

3. 자연수에 대해 재귀의 과정(course-of-value recursion)을 수행하는 여러분만의 함수를 정의하세요. 마찬가지로 여러분은 여러분 스스로 ``WellFounded.fix``을 정의하는 법을 알아낼 수 있는지 볼 것입니다.

4. [종속 패턴 매칭 섹션](#dependent_pattern_matching)의 다음 예제는 벡터에 벡터를 추가하는 함수를 정의합니다.
   이것은 교활해서 여러분은 부가함수를 정의해야만 할 것입니다.

5. 다음의 산술적 표현식 유형을 고려하세요. 이해를 돕자면 ``var n``는 변수, ``vₙ``와 ``const n``은 값이 ``n``인 상수이다.

```lean
inductive Expr where
  | const : Nat → Expr
  | var : Nat → Expr
  | plus : Expr → Expr → Expr
  | times : Expr → Expr → Expr
  deriving Repr

open Expr

def sampleExpr : Expr :=
  plus (times (var 0) (const 7)) (times (const 2) (var 1))
```

여기서 ``sampleExpr``이 ``(v₀ * 7) + (2 * v₁)``을 나타냅니다.

각 ``var n``을 ``v n``으로 계산하는 표현식을 계산하는 함수를 작성하세요.

```lean
# inductive Expr where
#   | const : Nat → Expr
#   | var : Nat → Expr
#   | plus : Expr → Expr → Expr
#   | times : Expr → Expr → Expr
#   deriving Repr
# open Expr
# def sampleExpr : Expr :=
#   plus (times (var 0) (const 7)) (times (const 2) (var 1))
def eval (v : Nat → Nat) : Expr → Nat
  | const n     => sorry
  | var n       => v n
  | plus e₁ e₂  => sorry
  | times e₁ e₂ => sorry

def sampleVal : Nat → Nat
  | 0 => 5
  | 1 => 6
  | _ => 0

-- 시도해 보세요. 여러분은 여기서 47을 얻어야 합니다.
-- #eval eval sampleVal sampleExpr
```

"상수 융합,"의 구현은 ``5 + 7`` to ``12``같은 부분항을 단순화하는 절차이다. 보조 함수 ``simpConst``를 사용하여 함수 "fuse"를 정의하세요. 더하기와 곱하기를 간단히 하기 위해서 인수를 재귀적으로 단순화하세요. 그 뒤 ``simpConst``을 결과를 단순화하는데 적용하세요.

```lean
# inductive Expr where
#   | const : Nat → Expr
#   | var : Nat → Expr
#   | plus : Expr → Expr → Expr
#   | times : Expr → Expr → Expr
#   deriving Repr
# open Expr
# def eval (v : Nat → Nat) : Expr → Nat
#   | const n     => sorry
#   | var n       => v n
#   | plus e₁ e₂  => sorry
#   | times e₁ e₂ => sorry
def simpConst : Expr → Expr
  | plus (const n₁) (const n₂)  => const (n₁ + n₂)
  | times (const n₁) (const n₂) => const (n₁ * n₂)
  | e                           => e

def fuse : Expr → Expr := sorry

theorem simpConst_eq (v : Nat → Nat)
        : ∀ e : Expr, eval v (simpConst e) = eval v e :=
  sorry

theorem fuse_eq (v : Nat → Nat)
        : ∀ e : Expr, eval v (fuse e) = eval v e :=
  sorry
```

마지막 두 정리는 정의가 값을 보존함을 보이는 것입니다.
