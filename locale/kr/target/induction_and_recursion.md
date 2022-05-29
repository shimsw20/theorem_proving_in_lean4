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

Here, the value of the ``fib`` function at ``n + 2`` (which is
definitionally equal to ``succ (succ n)``) is defined in terms of the
values at ``n + 1`` (which is definitionally equivalent to ``succ n``)
and the value at ``n``. This is a notoriously inefficient way of
computing the fibonacci function, however, with an execution time that
is exponential in ``n``. Here is a better way:

```lean
def fibFast (n : Nat) : Nat :=
  (loop n).1
where
  loop : Nat → Nat × Nat
    | 0   => (0, 1)
    | n+1 => let p := loop n; (p.2, p.1 + p.2)

#eval fibFast 100
```

Here is the same definition using a `let rec` instead of a `where`.

```lean
def fibFast (n : Nat) : Nat :=
  let rec loop : Nat → Nat × Nat
    | 0   => (0, 1)
    | n+1 => let p := loop n; (p.2, p.1 + p.2)
  (loop n).1
```

In both cases, Lean generates the auxiliary function `fibFast.loop`.

To handle structural recursion, the equation compiler uses
*course-of-values* recursion, using constants ``below`` and ``brecOn``
that are automatically generated with each inductively defined
type. You can get a sense of how it works by looking at the types of
``Nat.below`` and ``Nat.brecOn``:

```lean
variable (C : Nat → Type u)

#check (@Nat.below C : Nat → Type u)

#reduce @Nat.below C (3 : Nat)

#check (@Nat.brecOn C : (n : Nat) → ((n : Nat) → @Nat.below C n → C n) → C n)
```

The type ``@Nat.below C (3 : nat)`` is a data structure that stores elements of ``C 0``, ``C 1``, and ``C 2``.
The course-of-values recursion is implemented by ``Nat.brecOn``. It enables us to define the value of a dependent
function of type ``(n : Nat) → C n`` at a particular input ``n`` in terms of all the previous values of the function,
presented as an element of ``@Nat.below C n``.

The use of course-of-values recursion is one of the techniques the equation compiler uses to justify to
the Lean kernel that a function terminates. It does not affect the code generator which compiles recursive
functions as other functional programming language compilers. Recall that `#eval fib <n>` is exponential on `<n>`.
On the other hand, `#reduce fib <n>` is efficient because it uses the definition sent to the kernel that
is based on the `brecOn` construction.

```lean
def fib : Nat → Nat
  | 0   => 1
  | 1   => 1
  | n+2 => fib (n+1) + fib n

-- #eval fib 50 -- slow
#reduce fib 50  -- fast

#print fib
```

Another good example of a recursive definition is the list ``append`` function.

```lean
def append : List α → List α → List α
  | [],    bs => bs
  | a::as, bs => a :: append as bs

example : append [1, 2, 3] [4, 5] = [1, 2, 3, 4, 5] := rfl
```

Here is another: it adds elements of the first list to elements of the second list, until one of the two lists runs out.

```lean
def listAdd [Add α] : List α → List α → List α
  | [],      _       => []
  | _,       []      => []
  | a :: as, b :: bs => (a + b) :: listAdd as bs

#eval listAdd [1, 2, 3] [4, 5, 6, 6, 9, 10]
-- [5, 7, 9]
```

You are encouraged to experiment with similar examples in the exercises below.

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

There is a long cast of characters here, but the first block we have
already seen: the type, ``α``, the relation, ``r``, and the
assumption, ``h``, that ``r`` is well founded. The variable ``C``
represents the motive of the recursive definition: for each element
``x : α``, we would like to construct an element of ``C x``. The
function ``F`` provides the inductive recipe for doing that: it tells
us how to construct an element ``C x``, given elements of ``C y`` for
each predecessor ``y`` of ``x``.

Note that ``WellFounded.fix`` works equally well as an induction
principle. It says that if ``≺`` is well founded and you want to prove
``∀ x, C x``, it suffices to show that for an arbitrary ``x``, if we
have ``∀ y ≺ x, C y``, then we have ``C x``.

In the example above we set the option `codegen` to false because the code
generator currently does not support `WellFounded.fix`. The function
`WellFounded.fix` is another tool Lean uses to justify that a function
terminates.

Lean knows that the usual order ``<`` on the natural numbers is well
founded. It also knows a number of ways of constructing new well
founded orders from others, for example, using lexicographic order.

Here is essentially the definition of division on the natural numbers that is found in the standard library.

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

The definition is somewhat inscrutable. Here the recursion is on
``x``, and ``div.F x f : Nat → Nat`` returns the "divide by ``y``"
function for that fixed ``x``. You have to remember that the second
argument to ``div.F``, the recipe for the recursion, is a function
that is supposed to return the divide by ``y`` function for all values
``x₁`` smaller than ``x``.

The equation compiler is designed to make definitions like this more
convenient. It accepts the following:

**TODO: waiting for well-founded support in Lean 4**

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

When the equation compiler encounters a recursive definition, it first
tries structural recursion, and only when that fails, does it fall
back on well-founded recursion. In this case, detecting the
possibility of well-founded recursion on the natural numbers, it uses
the usual lexicographic ordering on the pair ``(x, y)``. The equation
compiler in and of itself is not clever enough to derive that ``x -
y`` is less than ``x`` under the given hypotheses, but we can help it
out by putting this fact in the local context. The equation compiler
looks in the local context for such information, and, when it finds
it, puts it to good use.

The defining equation for ``div`` does *not* hold definitionally, but
the equation is available to ``rewrite`` and ``simp``. The simplifier
will loop if you apply it blindly, but ``rewrite`` will do the trick.

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

The following example is similar: it converts any natural number to a
binary expression, represented as a list of 0's and 1's. We have to
provide the equation compiler with evidence that the recursive call is
decreasing, which we do here with a ``sorry``. The ``sorry`` does not
prevent the bytecode evaluator from evaluating the function
successfully.

.. code-block:: lean

    def nat_to_bin : ℕ → list ℕ
    | 0       := [0]
    | 1       := [1]
    | (n + 2) :=
      have (n + 2) / 2 < n + 2, from sorry,
      nat_to_bin ((n + 2) / 2) ++ [n % 2]
    
    #eval nat_to_bin 1234567

As a final example, we observe that Ackermann's function can be
defined directly, because it is justified by the well foundedness of
the lexicographic order on the natural numbers.

.. code-block:: lean

    def ack : nat → nat → nat
    | 0     y     := y+1
    | (x+1) 0     := ack x 1
    | (x+1) (y+1) := ack x (ack (x+1) y)
    
    #eval ack 3 5

Lean's mechanisms for guessing a well-founded relation and then
proving that recursive calls decrease are still in a rudimentary
state. They will be improved over time. When they work, they provide a
much more convenient way of defining functions than using
``WellFounded.fix`` manually. When they don't, the latter is always
available as a backup.

.. TO DO: eventually, describe using_well_founded.

.. nested_and_mutual_recursion:

Mutual Recursion
----------------

**TODO: waiting for well-founded support in Lean 4**

Lean also supports mutual recursive definitions. The syntax is similar to that for mutual inductive types, as described in :numref:`mutual_and_nested_inductive_types`. 여기 예제가 있습니다.

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

What makes this a mutual definition is that ``even`` is defined recursively in terms of ``odd``, while ``odd`` is defined recursively in terms of ``even``. Under the hood, this is compiled as a single recursive definition. The internally defined function takes, as argument, an element of a sum type, either an input to ``even``, or an input to ``odd``. It then returns an output appropriate to the input. To define that function, Lean uses a suitable well-founded measure. The internals are meant to be hidden from users; the canonical way to make use of such definitions is to use ``rewrite`` or ``simp``, as we did above.

Mutual recursive definitions also provide natural ways of working with mutual and nested inductive types, as described in :numref:`mutual_and_nested_inductive_types`. Recall the definition of ``even`` and ``odd`` as mutual inductive predicates, as presented as an example there:

.. code-block:: lean

    mutual inductive even, odd
    with even : ℕ → Prop
    | even_zero : even 0
    | even_succ : ∀ n, odd n → even (n + 1)
    with odd : ℕ → Prop
    | odd_succ : ∀ n, even n → odd (n + 1)

The constructors, ``even_zero``, ``even_succ``, and ``odd_succ`` provide positive means for showing that a number is even or odd. We need to use the fact that the inductive type is generated by these constructors to know that the zero is not odd, and that the latter two implications reverse. As usual, the constructors are kept in a namespace that is named after the type being defined, and the command ``open even odd`` allows us to access them move conveniently.

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

For another example, suppose we use a nested inductive type to define a set of terms inductively, so that a term is either a constant (with a name given by a string), or the result of applying a constant to a list of constants.

.. code-block:: lean

    inductive term
    | const : string → term
    | app   : string → list term → term

We can then use a mutual recursive definition to count the number of constants occurring in a term, as well as the number occurring in a list of terms.

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


Dependent Pattern Matching
--------------------------

All the examples of pattern matching we considered in
:numref:`pattern_matching` can easily be written using ``cases_on``
and ``rec_on``. However, this is often not the case with indexed
inductive families such as ``vector α n``, since case splits impose
constraints on the values of the indices. Without the equation
compiler, we would need a lot of boilerplate code to define very
simple functions such as ``map``, ``zip``, and ``unzip`` using
recursors. To understand the difficulty, consider what it would take
to define a function ``tail`` which takes a vector
``v : vector α (succ n)`` and deletes the first element. A first thought might be to
use the ``casesOn`` function:

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

But what value should we return in the ``nil`` case? Something funny
is going on: if ``v`` has type ``Vector α (succ n)``, it *can't* be
nil, but it is not clear how to tell that to ``casesOn``.

One solution is to define an auxiliary function:

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

In the ``nil`` case, ``m`` is instantiated to ``0``, and
``noConfusion`` makes use of the fact that ``0 = succ n`` cannot
occur.  Otherwise, ``v`` is of the form ``a :: w``, and we can simply
return ``w``, after casting it from a vector of length ``m`` to a
vector of length ``n``.

The difficulty in defining ``tail`` is to maintain the relationships between the indices.
The hypothesis ``e : m = n + 1`` in ``tailAux`` is used to communicate the relationship
between ``n`` and the index associated with the minor premise.
Moreover, the ``zero = n + 1`` case is unreachable, and the canonical way to discard such
a case is to use ``noConfusion``.

The ``tail`` function is, however, easy to define using recursive
equations, and the equation compiler generates all the boilerplate
code automatically for us. Here are a number of similar examples:


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

Note that we can omit recursive equations for "unreachable" cases such
as ``head nil``. The automatically generated definitions for indexed
families are far from straightforward. 예를 들어

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

The ``map`` function is even more tedious to define by hand than the
``tail`` function. We encourage you to try it, using ``recOn``,
``casesOn`` and ``noConfusion``.

Inaccessible Patterns
------------------

Sometimes an argument in a dependent matching pattern is not essential
to the definition, but nonetheless has to be included to specialize
the type of the expression appropriately. Lean allows users to mark
such subterms as *inaccessible* for pattern matching. These
annotations are essential, for example, when a term occurring in the
left-hand side is neither a variable nor a constructor application,
because these are not suitable targets for pattern matching. We can
view such inaccessible patterns as "don't care" components of the
patterns. You can declare a subterm inaccessible by writing
``.(t)``. If the inaccessible pattern can be inferred, you can also write
``_``.

The following example, we declare an inductive type that defines the
property of "being in the image of ``f``". You can view an element of
the type ``ImageOf f b`` as evidence that ``b`` is in the image of
``f``, whereby the constructor ``imf`` is used to build such
evidence. We can then define any function ``f`` with an "inverse"
which takes anything in the image of ``f`` to an element that is
mapped to it. The typing rules forces us to write ``f a`` for the
first argument, but this term is neither a variable nor a constructor
application, and plays no role in the pattern-matching definition. To
define the function ``inverse`` below, we *have to* mark ``f a``
inaccessible.

```lean
inductive ImageOf {α β : Type u} (f : α → β) : β → Type u where
  | imf : (a : α) → ImageOf f (f a)

open ImageOf

def inverse {f : α → β} : (b : β) → ImageOf f b → α
  | .(f a), imf a => a

def inverse' {f : α → β} : (b : β) → ImageOf f b → α
  | _, imf a => a
```

In the example above, the inaccessible annotation makes it clear that
``f`` is *not* a pattern matching variable.

Inaccessible patterns can be used to clarify and control definitions that
make use of dependent pattern matching. Consider the following
definition of the function ``Vector.add,`` which adds two vectors of
elements of a type, assuming that type has an associated addition
function:

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

The argument ``{n : Nat}`` appear after the colon, because it cannot
be held fixed throughout the definition.  When implementing this
definition, the equation compiler starts with a case distinction as to
whether the first argument is ``0`` or of the form ``n+1``.  This is
followed by nested case splits on the next two arguments, and in each
case the equation compiler rules out the cases are not compatible with
the first pattern.

But, in fact, a case split is not required on the first argument; the
``casesOn`` eliminator for ``Vector`` automatically abstracts this
argument and replaces it by ``0`` and ``n + 1`` when we do a case
split on the second argument. Using inaccessible patterns, we can prompt
the equation compiler to avoid the case split on ``n``

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

Marking the position as an inaccessible pattern tells the
equation compiler first, that the form of the argument should be
inferred from the constraints posed by the other arguments, and,
second, that the first argument should *not* participate in pattern
matching.

The inaccessible pattern `.(_)` can be written as `_` for convenience.

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

As we mentioned above, the argument ``{n : Nat}`` is part of the
pattern matching, because it cannot be held fixed throughout the
definition. In previous Lean versions, users often found it cumbersome
to have to include these extra discriminants. Thus, Lean 4
implements a new feature, *discriminant refinement*, which includes
these extra discriminants automatically for us.

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

When combined with the *auto bound implicits* feature, you can simplify
the declare further and write:

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

Using these new features, you can write the other vector functions defined
in the previous sections more compactly as follows:

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

Match Expressions
-----------------

Lean also provides a compiler for *match-with* expressions found in
many functional languages.

```lean
def isNotZero (m : Nat) : Bool :=
  match m with
  | 0   => false
  | n+1 => true
```

This does not look very different from an ordinary pattern matching
definition, but the point is that a ``match`` can be used anywhere in
an expression, and with arbitrary arguments.

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

Lean uses the ``match`` construct internally to implement pattern-matching in all parts of the system.
Thus, all four of these definitions have the same net effect.

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

These variations are equally useful for destructing propositions:

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

Local recursive declarations
---------

You can define local recursive declarations using the `let rec` keyword.

```lean
def replicate (n : Nat) (a : α) : List α :=
  let rec loop : Nat → List α → List α
    | 0,   as => as
    | n+1, as => loop n (a::as)
  loop n []

#check @replicate.loop
-- {α : Type} → α → Nat → List α → List α
```

Lean creates an auxiliary declaration for each `let rec`. In the example above,
it created the declaration `replicate.loop` for the `let rec loop` occurring at `replicate`.
Note that, Lean "closes" the declaration by adding any local variable occurring in the
`let rec` declaration as additional parameters. For example, the local variable `a` occurs
at `let rec loop`.

You can also use `let rec` in tactic mode and for creating proofs by induction.

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

You can also introduce auxiliary recursive declarations using `where` clause after your definition.
Lean converts them into a `let rec`.

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

1. Open a namespace ``Hidden`` to avoid naming conflicts, and use the
   equation compiler to define addition, multiplication, and
   exponentiation on the natural numbers. Then use the equation
   compiler to derive some of their basic properties.

2. Similarly, use the equation compiler to define some basic
   operations on lists (like the ``reverse`` function) and prove
   theorems about lists by induction (such as the fact that
   ``reverse (reverse xs) = xs`` for any list ``xs``).

3. Define your own function to carry out course-of-value recursion on
   the natural numbers. Similarly, see if you can figure out how to
   define ``WellFounded.fix`` on your own.

4. Following the examples in [Section Dependent Pattern Matching](#dependent_pattern_matching),
   define a function that will append two vectors.
   This is tricky; you will have to define an auxiliary function.

5. Consider the following type of arithmetic expressions. The idea is
   that ``var n`` is a variable, ``vₙ``, and ``const n`` is the
   constant whose value is ``n``.

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

Here ``sampleExpr`` represents ``(v₀ * 7) + (2 * v₁)``.

Write a function that evaluates such an expression, evaluating each ``var n`` to ``v n``.

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

-- Try it out. You should get 47 here.
-- #eval eval sampleVal sampleExpr
```

Implement "constant fusion," a procedure that simplifies subterms like
``5 + 7`` to ``12``. Using the auxiliary function ``simpConst``,
define a function "fuse": to simplify a plus or a times, first
simplify the arguments recursively, and then apply ``simpConst`` to
try to simplify the result.

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

The last two theorems show that the definitions preserve the value.
