의존 유형론
=====================

의존 유형론은 여러분이 복잡한 수학적 진술을 표현할 수 있게 하고, 복잡한 하드웨어와 소프트웨어 명제를 작성할 수 있게 하며 이 둘에 대해 자연스럽고 일관성있게 추론할 수 있게 하는 강력하고 표현력 있는 언어입니다. 린은  *직관주의 계산법*이라고 하는 가산적인 비축적적 세계(Universe)와 유도형이 있는 의존 유형론 버전을 기반합니다. 2장의 끝에서 여러분은 이것의 의미하는 바의 대부분을 이해하게 될 겁니다.

## 단순 유형론(Simple Type Theory)

'유형론'은 그것의 이름을 모든 표현은 연관된 *유형*을 가지고 있다는 사실로부터 갖게 되었습니다. 예를들어 어떤 맥락에서 ``x + 0``은 자연수를 가리키고  ``f``은 자연수에 대한 함수를 지칭합니다. 엄밀한 정의를 좋아하는 이들에게 린의 자연수는 부호없는 임의 정밀도의 정수입니다.

린에서 여러분이 객체를 어떻게 선언하고 그들의 유형을 확인할 수 있는지 몇 가지 예제가 있습니다.

```lean
/-  몇 가지 상수를 정의합니다. -/

def m : Nat := 1       -- m은 자연수입니다.
def n : Nat := 0
def b1 : Bool := true  -- b1은 불리언입니다.
def b2 : Bool := false

/- 그들의 유형을 확인합니다. -/

#check m            -- output: Nat
#check n
#check n + 0        -- Nat
#check m * (n + 0)  -- Nat
#check b1           -- Bool
#check b1 && b2     -- "&&"은 불리언 and
#check b1 || b2     -- 불리언 or
#check true         -- 불리언 "true"

/- Evaluate -/

#eval 5 * 4         -- 20
#eval m + 2         -- 3
#eval b1 && b2      -- false
```

 ``/-``과 ``-/`` 사이의 모든 글은 린에게 무시하라고 가리키는 주석을 만듭니다. 마찬가지로 두 개의 대시 `--`는 이 줄의 나머지는 주석을 포함함을 나타내고 이 또한 무시됩니다. 주석 블록은 중첩될 수 있으며 대부분의 프로그래밍 언어처럼 코드 조각을 "주석 처리"할 수 있게 합니다.

``def``는 작업 환경에 새로운 상수기호를 선언합니다. 위 예제에서 `def m : Nat := 1`는 `1`을 값으로 갖는 새로운 상수 `m`을 `Nat`유형으로 정의합니다.
``#check`` 명령은 린에게 그것의 유형을 보고하도록 요청합니다. 린에서 시스템에게 정보를 불러오는 보조 명령은 주로 해시(#) 기호로 시작합니다.
`#eval` 명령은 린에게 제시된 표현의 값을 평가하도록 요청합니다.
여러분은 스스로 몇몇 상수를 선언하고 몇 가지 식의 유형을 확인해보길 바랍니다. 이처럼 새로운 대상을 선언하는 것은 시스템을 실험해보는 좋은 방식입니다.

단순 유형론을 강력하게 만드는 것은 기본형 외의 여러분만의 새로운 유형을 만들 수 있다는 점입니다. 예를 들어 ``a``와 ``b``가 유형이라면 ``a -> b``는 ``a`` 에서 ``b``로 가는 함수 유형을 나타냅니다. 그리고 ``a × b`` 는 ``a``의 원소와 ``b``의 원소로 이뤄진 쌍을 원소로 갖는 유형을 나타냅니다. 이것을 *카테시안 곱*이라 합니다. `×`은 유니코드 기호임을 보세요. 분별있는 유니코드의 사용은 가독성을 개선합니다. 그리고 현대의 모든 편집기는 그것의 사용을 지원합니다. 린의 표준 라이브러리에서 여러분은 유형을 나타내는데 그리스 문자를 자주 보게 됩니다. 그리고 유니코드 기호 `→` 은 `->`보다 더 간결한 버전입니다.

```lean
#check Nat → Nat      --화살표를 쓰기 위해서 "\to"나 "\r"를 치세요.
#check Nat -> Nat     -- ASCII 표기의 대체표현입니다.

#check Nat × Nat      -- 곱하기를 쓰기 위해 "\times"를 치세요.
#check Prod Nat Nat   -- 대체 표현입니다.

#check Nat → Nat → Nat
#check Nat → (Nat → Nat)  -- 위와 같은 유형입니다.

#check Nat × Nat → Nat
#check (Nat → Nat) → Nat -- "범함수"

#check Nat.succ     -- Nat → Nat
#check (0, 1)       -- Nat × Nat
#check Nat.add      -- Nat → Nat → Nat

#check Nat.succ 2   -- Nat
#check Nat.add 3    -- Nat → Nat
#check Nat.add 5 2  -- Nat
#check (5, 9).1     -- Nat
#check (5, 9).2     -- Nat

#eval Nat.succ 2   -- 3
#eval Nat.add 5 2  -- 7
#eval (5, 9).1     -- 5
#eval (5, 9).2     -- 9
```

다시 한번 여러분 스스로 몇 가지 예제를 시도해보기 바랍니다.

몇 가지 기본 문법에 대해 살펴봅시다. 여러분은 유니코드 화살표 ``→``를 ``\to``을 치거나 or ``\r``또는 ``\->``으로 입력할 수 있습니다. 여러분은 ASCII 대체 표현으로 ``->``을 사용할 수 있습니다. 그래서 표현식 ``Nat -> Nat``과 ``Nat → Nat``은 같은 식을 의미합니다. 두 표현식 모두 자연수를 입력으로 받아 자연수를 출력으로 반환하는 함수 유형을 가리킵니다. 카테시안 곱을 나타내는 유니코드 기호 ``×``는 ``\times``을 입력하여 씁니다. 여러분은 유형을 포괄하기 위해  ``α``, ``β``, ``γ``같은 그리스 소문자 자주 사용할 것입니다. 여러분은 이들 중 특정한 것은 ``\a``, ``\b``과 ``\g``으로 입력할 수 있습니다.

여기서 몇 개 더 짚고가야 할 것이 있습니다. 우선 함수 ``f``에 값 ``x``의 활용은 ``f x`` 를 지칭합니다. (예를 들어 `Nat.succ 2`)
둘째로 유형 표현식을 쓸 때 화살표는*오른쪽* 먼저 결합합니다. 가령``Nat.add``의 유형은 ``Nat → Nat → Nat``이고 이는 `Nat → (Nat → Nat)`과 동등합니다. 따라서 여러분은 ``Nat.add``은 자연수를 받아 자연수를 받고 자연수를 반환하는 또 다른 함수를 반환하는 함수로 볼 수 있습니다. 유형론에서 보통 ``Nat.add``과 같이 쓰는 것이 자연수 쌍을 입력으로 받고 자연수를 출력으로 하는 함수로 쓰는 것보다 더 편리합니다. 예를 들어 이는 여러분에게 함수 ``Nat.add``의 "부분 적용"을 허용합니다.  위의 예제에서 ``Nat.add 3``는 ``Nat → Nat``유형을 가짐을  보였습니다. 즉 ``Nat.add 3``은 두번째 인자 ``n``을 "기다리는" 함수를 반환하는 것입니다. 이것은 ``Nat.add 3 n``로 쓰는 것과 동등합니다.
<!-- Taking a function ``h`` of type ``Nat
× Nat → Nat`` and "redefining" it to look like ``g`` is a process
known as *currying*. -->

여러분은 ``m : Nat``과  ``n : Nat``이면, ``(m, n)``은 ``Nat × Nat``유형인 ``m``과 ``n``의 순서쌍을 가리킨다는 것을 보았습니다. 이는 여러분에게 자연수의 쌍을 만들 수 있는 방법을 줍니다. 반대로 여러분이 ``p : Nat × Nat``을 갖고 있다면 ``p.1 : Nat``과 ``p.2 : Nat``처럼 쓸 수 있습니다. 이는 여러분에게 순서쌍의 두 성분을 추출하는 방법을 줍니다.

## 대상으로써 유형

린의 종속 유형론이 단순 유형론을 확장시키는 한 방법은 ---``Nat``과 ``Bool``같은 개체는 그들 그 자체로 대상인 일등 시민 ---으로 두는 것입니다. 이렇게 하는 경우에 대해 그들 각각은 유형을 가져야만 합니다.

```lean
#check Nat               -- Type
#check Bool              -- Type
#check Nat → Bool        -- Type
#check Nat × Bool        -- Type
#check Nat → Nat         -- ...
#check Nat × Nat → Nat
#check Nat → Nat → Nat
#check Nat → (Nat → Nat)
#check Nat → Nat → Bool
#check (Nat → Nat) → Nat
```

여러분도 보다시피 위 각각의 표현식은 ``Type`` 유형입니다. 여러분은 유형들에 대해 새 상수를 선언할 수 있습니다.

```lean
def α : Type := Nat
def β : Type := Bool
def F : Type → Type := List
def G : Type → Type → Type := Prod

#check α        -- Type
#check F α      -- Type
#check F Nat    -- Type
#check G α      -- Type → Type
#check G α β    -- Type
#check G α Nat  -- Type
```

위 예에서 제안한 것처럼 여러분은 이미 주로 카테시안 곱 `Prod`에서 ``Type → Type → Type`` 유형의 함수의 예를 보았습니다.

```lean
def α : Type := Nat
def β : Type := Bool

#check Prod α β       -- Type
#check α × β          -- Type

#check Prod Nat Nat   -- Type
#check Nat × Nat      -- Type
```

또 다른 예제가 있습니다. ``α``라 하는 임의의 타입에 대해 ``List α``의 유형은 ``α`` 유형을 원소로 하는 리스트 유형을 가리킵니다.

```lean
def α : Type := Nat

#check List α    -- Type
#check List Nat  -- Type
```

린의 모든 표현식이 유형을 가진다면 ``Type`` 그 자체는 어떤 유형을 가져야 하는지 궁금한게 당연합니다.

```lean
#check Type      -- Type 1
```

여러분은 린의 유형화 시스템의 가장 미묘한 면 중 하나를 마주쳤습니다. 린의 기저에는 무한한 유형의 계층이 있습니다.

```lean
#check Type     -- Type 1
#check Type 1   -- Type 2
#check Type 2   -- Type 3
#check Type 3   -- Type 4
#check Type 4   -- Type 5
```

``Type 0``는 "작은" 또는 "평범한" 유형들의 세계라고 생각해보세요.
``Type 1``는  ``Type 0``를 원소로 갖는 유형들의 더 큰 세계이고 ``Type 2``는 ``Type 1``을 원소로 하는 유형들의 더욱 큰 세계입니다. 모든 자연수 ``n``에 대해 ``Type n``가 있어서 이런 리스트를 무한히 나열할 수 있습니다. ``Type``는 ``Type 0``에 대한 약식 표현입니다.

```lean
#check Type
#check Type 0
```

그러나 몇몇 연산은 유형 세계에 대해 *다형적(polymorphic)*일 필요가 있습니다. 예를 들어 ``α``가 어떤 유형 세계에 있던간에 ``List α``는 임의의 유형 ``α``에 대해 의미가 있어야 합니다. 이는 ``List``함수의 유형 표기를 설명합니다.

```lean
#check List    -- Type u_1 → Type u_1
```

여기서 ``u_1``는 어떤 유형 세계에 대한 변수입니다. ``#check`` 명령의 출력은 ``α``가 ``Type n``유형을 갖는 한 ``List α``도 ``Type n`` 유형을 가짐을 의미합니다. 마찬가지로 ``Prod`` 함수는 다형적입니다.

```lean
#check Prod    -- Type u_1 → Type u_2 → Type (max u_1 u_2)
```

다형적인 상수를 정의하기 위해 린은 여러분이 세계 변수를 `universe` 명령을 명시적으로 사용하여 선언할 수 있게 했습니다.

```lean
universe u

def F (α : Type u) : Type u := Prod α α

#check F    -- Type u → Type u
```

여러분은 F를 정의할 때 universe 매개변수를 제공하는 것으로 universe 명령을 쓰지 않을 수 있습니다.

```lean
def F.{u} (α : Type u) : Type u := Prod α α

#check F    -- Type u → Type u
```

## 함수 추상화와 함수값의 평가

린은 `fun` (또는 `λ`) 키워드를 제공하여 다음과 같은 표현식으로부터 함수를 만들 수 있게 합니다.

```lean
#check fun (x : Nat) => x + 5   -- Nat → Nat
#check λ (x : Nat) => x + 5     --  λ 와 fun 같은 의미를 가집니다.
#check fun x : Nat => x + 5     --  Nat으로 추론됩니다.
#check λ x : Nat => x + 5       --  Nat으로 추론됩니다.
```

여러분은 필요한 매개변수를 람다 함수에 넘겨줌으로써 값을 평가할 수 있습니다.

```lean
#eval (λ x : Nat => x + 5) 10    -- 15
```

다른 표현식으로부터 함수를 만드는 것은 *람다 추상화(lambda abstraction)*과정으로 알려져 있습니다. 여러분이 변수 ``x : α``를 갖고 있고 표현식 ``t : β``을 만들 수 있다 가정합시다. 그러면 표현식``fun (x : α) => t`` 또는 등가적으로 ``λ (x : α) => t``은 ``α → β`` 유형인 대상입니다. 이를  임의의 값 ``x``에서 값 ``t``로 대응시키는 ``α``에서 ``β``까지의 함수로 생각해보세요.

여기 추가 예제가 더 있습니다.

```lean
#check fun x : Nat => fun y : Bool => if not y then x + 1 else x + 2
#check fun (x : Nat) (y : Bool) => if not y then x + 1 else x + 2
#check fun x y => if not y then x + 1 else x + 2   -- Nat → Bool → Nat
```

린은 마지막 세 예제를 같은 표현식으로 해석합니다. 마지막 표현식에서 린은 ``x``와 ``y``의 유형을 표현식 `if not y then x + 1 else x + 2`으로부터 추론합니다.

수학적으로 흔한 함수 연산 예제는 람다 추상화에 대한 것으로 설명될 수 있습니다.

```lean
def f (n : Nat) : String := toString n
def g (s : String) : Bool := s.length > 0

#check fun x : Nat => x        -- Nat → Nat
#check fun x : Nat => true     -- Nat → Bool
#check fun x : Nat => g (f x)  -- Nat → Bool
#check fun x => g (f x)        -- Nat → Bool
```

이 표현식의 의미에 대해 생각해보세요. 표현식 ``fun x : Nat => x``은 ``Nat``에 대한 항등함수를 의미합니다. 표현식 ``fun x : Nat => true``은 항상  ``true``을 반환하는 상수함수를 가리합니다. 그리고 ``fun x : Nat => g (f x)``는 ``f``와 ``g``의 합성함수를 가리킵니다.  일반적으로 여러분도 유형 표기를 빼고 린에게 유형을 추론하게 둘 수 있습니다.  그래서 여러분은 ``fun x : Nat => g (f x)``대신에 ``fun x => g (f x)``와 같이 쓸 수 있습니다.

여러분은 매개변수로 함수의 이름  `f`과 `g` 을 주는 것으로 함수를 전달할 수 있습니다.  그러면 구현에서 이들 함수를 사용할 수 있습니다.

```lean
#check fun (g : String → Bool) (f : Nat → String) (x : Nat) => g (f x)
-- (String → Bool) → (Nat → String) → Nat → Bool
```

여러분은 매개변수로 유형도 전달할 수 있습니다.

```lean
#check fun (α β γ : Type) (g : β → γ) (f : α → β) (x : α) => g (f x)
```
마지막 표현식은 세 유형 ``α``, ``β``, ``γ``과 두 함수 ``g : β → γ``과 ``f : α → β``을 받고 ``g``과 ``f``의 합성을 반환하는 함수를 나타냅니다.
(이 함수의 유형들을 이해하는 것은 아래에서 설명할 의존 곱에 대한 이해가 필요합니다.)

람다 표현식의 일반적인 형태는 ``fun x : α => t``입니다. 여기서 변수 ``x``는 "구속변수"입니다. 이는 그것의 "범위"가 표현식  ``t`` 안으로 제한되는 '자리차지자'일 뿐 입니다.  예를 들어 표현식 ``fun (b : β) (x : α) => b`` 속 변수 ``b``는 앞서 선언된 상수 ``b``와는 아무런 연관이 없습니다.  사실 표현식은  ``fun (u : β) (z : α) => u``처럼 같은 함수를 가리킵니다.

공식적으로 구속 변수의 이름이 바뀌기까지 같은 표현식은 *알파 등가(alpha equivalent)*라 하고 "같은" 것으로 생각합니다. 린도 이를 등가로 인식합니다.

항 ``t : α → β``을 항 ``s : α``에 적용하여 표현식 ``t s : β``을 얻는 것을 보세요. 이전 예제로 돌아가 명확성을 위해 구속변수의 이름을 바꿉시다. 다음 표현식의 유형을 주목하세요.

```lean
#check (fun x : Nat => x) 1     -- Nat
#check (fun x : Nat => true) 1  -- Bool

def f (n : Nat) : String := toString n
def g (s : String) : Bool := s.length > 0

#check
  (fun (α β γ : Type) (u : β → γ) (v : α → β) (x : α) => u (v x)) Nat String Bool g f 0
  -- Bool
```

예상했다시피 표현식``(fun x : Nat => x) 1`` 은 ``Nat`` 유형을 갖습니다.
사실, 더 중요한건 표현식``(fun x : Nat => x)``을 ``1``에 적용하는 것은 값 ``1``을 "반환"하는 겁니다. 그리고 당연히 그럽니다.

```lean
#eval (fun x : Nat => x) 1     -- 1
#eval (fun x : Nat => true) 1  -- true
```

여러분은 나중에 이 항들이 어떻게 평가되는지 볼 겁니다. 현재로써는 이게 의존 유형론의 중요한 특징인 것만 알아 두세요. 모든 항은 전산적 거동을 하고 *정규화(normalization)*의 개념을 지원합니다. 원리적으로 같은 값으로 축약되는 두 항은 *정의상으로 동등(definitionally equal)*하다고 합니다. 이런 것은 린의 유형 검사기가 "같은"것으로 봅니다. 그리고 린은 유형을 인식하고 대조하는데 최선을 다합니다.

린은 완전한 프로그래밍 언어입니다. 이것은 이진 실행 프로그램을 만드는 컴파일러와 상호작용적인 인터프리터를 갖고 있습니다. 여러분은 `#eval` 명령을 사용해 식을 실행할 수 있습니다. 그리고 이것은 당신의 함수를 시험하는 선호되는 방식입니다.

<!--
Note that `#eval` and
`#reduce` are *not* equivalent. The command `#eval` first compiles
Lean expressions into an intermediate representation (IR) and then
uses an interpreter to execute the generated IR. Some builtin types
(e.g., `Nat`, `String`, `Array`) have a more efficient representation
in the IR. The IR has support for using foreign functions that are
opaque to Lean.

In contrast, the ``#reduce`` command relies on a reduction engine
similar to the one used in Lean's trusted kernel, the part of Lean
that is responsible for checking and verifying the correctness of
expressions and proofs. It is less efficient than ``#eval``, and
treats all foreign functions as opaque constants. You will learn later
that there are some other differences between the two commands.
-->

## 정의(Definitions)

``def``가 새 이름을 가진 대상을 선언하는 중요한 방식임을 기억하세요.



```lean
def double (x : Nat) : Nat :=
  x + x
```

다른 프로그래밍언어에서 함수가 어떻게 동작하는지 안다면 이게 여러분에게 더 친숙하게 보일지 모르겠습니다. 이름 `double`은 `Nat` 유형의 입력 매개변수 `x`를 받고  호출의 결과로 `x + x`인 함수로 정의되었습니다. 그래서 `Nat` 유형을 반환합니다. 여러분은 이 함수를 다음과 같이 불러낼 수 있습니다.

```lean
# def double (x : Nat) : Nat :=
#  x + x
#eval double 3    -- 6
```

이 경우 여러분은 `def`를 `lambda`와 같은 종류로 생각할 수 있습니다.
다음은 같은 결과를 만듭니다.

```lean
def double : Nat → Nat :=
  fun x => x + x

#eval double 3    -- 6
```

Lean이 유형을 추론하기에 충분한 정보를 갖고있을 때 여러분은 유형 선언을 생략할 수 있습니다.  유형 추론은 Lean의 중요한 기능입니다.

```lean
def double :=
  fun (x : Nat) => x + x
```

정의의 일반적인 형태는  ``def foo : α := bar``입니다. 여기서  ``α`` 는 식 ``bar``로부터 반환되는 유형입니다.  Lean은 ``α``의 유형을 추론할 수 있습니다. 그러나 이를 명백히 적는 것이 좋습니다.  이것은 당신의 의도를 명확히 만들고 Lean은 정의의 우변에 일치하는 유형이 아닌 경우 에러를 표시할 것입니다.

우변 `bar`는 lambda뿐만 아니라 어떤 식이든 될 수 있습니다.
그래서 `def`는 이 같은 값을 단순히 이름으로 쓸 수 있습니다.

```lean
def pi := 3.141592654
```

`def`는 다수의 입력 매개변수를 받을 수 있습니다.  두 자연수를 더하는 함수를 만들어 봅시다.

```lean
def add (x y : Nat) :=
  x + y

#eval add 3 2               -- 5
```

매개변수 리스트는 이와 같이 나눠 쓸 수 있습니다.

```lean
# def double (x : Nat) : Nat :=
#  x + x
def add (x : Nat) (y : Nat) :=
  x + y

#eval add (double 3) (7 + 9)  -- 22
```

여기서 우리가 `add`의 첫 번째 매개변수를 만들기 위해 `double` 함수를 호출한 것을 보세요.

여러분은 다른 더 흥미로운 식을 `def` 안에 사용할 수 있습니다.

```lean
def greater (x y : Nat) :=
  if x > y then x
  else y
```

여러분은 이 정의가 아마 뭘 할 지 추측할 수 있을 거예요.

여러분은 또 다른 함수를 입력으로 받는 함수를 정의할 수 있습니다.
다음은 주어진 함수를 첫번째 호출의 출력을 두번째에 전달하는 것으로 두 번 호출합니다.

```lean
# def double (x : Nat) : Nat :=
#  x + x
def doTwice (f : Nat → Nat) (x : Nat) : Nat :=
  f (f x)

#eval doTwice double 2   -- 8
```

이제 약간 더 추상적으로 갑시다. 여러분은 유형 매개변수같은 인수를 지정할 수도 있습니다.

```lean
def compose (α β γ : Type) (g : β → γ) (f : α → β) (x : α) : γ :=
  g (f x)
```

이는 `compose`가 하나의 입력만 받는 함수인 경우에만 임의의 두 함수를 입력 인수로 받는 함수임을 의미합니다.
 `β → γ` 와 `α → β`의 유형 대수는 두 번째 함수의 출력 유형이 첫 번째 함수의 입력 유형과 반드시 일치해야 한다는 요구를 같습니다. 이렇지 않다면 두 함수는 합성될 수 없을 것입니다.

`compose`는 이는 두 번째 함수(지역적으로 `f`라 하는)을 호출하는데 사용되기도 하는 유형 `α` 를 세 번째 인수로 받습니다. 그리고 두 번째 합수는 그 함수의 결과(유형 `β`의)를 첫 번째 함수(지역적으로 `g`라 하는)의 입력으로 전달합니다.  첫 번째 함수는 유형 `γ` 를 반환하여 이게 `compose` 함수의 반환형이 되게 합니다.

`compose`는 또 아주 일반적이어서 임의의 유형 `α β γ`에 대해서도 작동합니다.  이는 `compose`가 그들이 입력받는 두 함수 각각이 한 매개변수만 받고 두번째 함수의 출력 유형이 첫번째 함수의 입력 유형과 같은 한 합성할 수 있다는 것을 의미합니다.  예를 들어

```lean
# def compose (α β γ : Type) (g : β → γ) (f : α → β) (x : α) : γ :=
#  g (f x)
# def double (x : Nat) : Nat :=
#  x + x
def square (x : Nat) : Nat :=
  x * x

#eval compose Nat Nat Nat double square 3  -- 18
```

지역 정의(Local Definitions)
-----------------

Lean은 여러분이 ``let`` 키워드를 사용해 "지역" 정의를 가져올 수 있게 허용합니다. 표현식 ``let a := t1; t2`` 는 ``t2``  속 ``a``의 모든 나타남(occurrence)을 ``t1``으로 대체한 결과에 대해 정의상으로 같습니다.

```lean
#check let y := 2 + 2; y * y   -- Nat
#eval  let y := 2 + 2; y * y   -- 16

def twice_double (x : Nat) : Nat :=
  let y := x + x; y * y

#eval twice_double 2   -- 16
```

여기서``twice_double x``도 항  ``(x + x) * (x + x)``과 정의상으로 같습니다.

여러분은 다수의 할당을 ``let`` 구문으로 연결함으로써 결합할 수 있습니다.

```lean
#check let y := 2 + 2; let z := y + y; z * z   -- Nat
#eval  let y := 2 + 2; let z := y + y; z * z   -- 64
```

세미콜론``;``은 줄을 분리할 때 사용되므로 생략될 수 있습니다.
```lean
def t (x : Nat) : Nat :=
  let y := x + x
  y * y
```

표현식 ``let a := t1; t2``의 의미는 ``(fun a => t2) t1``의 의미와 아주 비슷함을 주목하세요. 그러나 이 둘은 같지는 않습니다. 첫 번째 표현식에서, 여러분은 ``t2``속 ``a``의 모든 개체를 ``t1``에 대한 문법적 약어로 생각해야 합니다. 두 번째 표현식에서 ``a``는 변수이고 표현식 ``fun a => t2``는  ``a``의 값과 별개로 의미를 가져야 합니다.
 ``let`` 생성은 약어의 의미로 더 강합니다. 그리고 ``let a := t1; t2`` 형태의 표현식은 ``(fun a => t2) t1``같이 표현될 수 없는 식이 있습니다. 연습으로 아래 유형 확인에서 ``foo``의 정의가 왜 그런지 그러나  ``bar``의 정의는 그렇지 않은지 이해하려고 해 보세요.

```lean
def foo := let a := Nat; fun x : a => x + 2
/-
  def bar := (fun a => fun x : a => x + 2) Nat
-/
```
# 변수와 섹션(Variables and Sections)

다음 세 함수 정의를 생각해보세요.
```lean
def compose (α β γ : Type) (g : β → γ) (f : α → β) (x : α) : γ :=
  g (f x)

def doTwice (α : Type) (h : α → α) (x : α) : α :=
  h (h x)

def doThrice (α : Type) (h : α → α) (x : α) : α :=
  h (h (h x))
```

린은 여러분에게 이런 선언을 더 간결하게 보이게 만들도록 ``variable`` 명령을 제공합니다.

```lean
variable (α β γ : Type)

def compose (g : β → γ) (f : α → β) (x : α) : γ :=
  g (f x)

def doTwice (h : α → α) (x : α) : α :=
  h (h x)

def doThrice (h : α → α) (x : α) : α :=
  h (h (h x))
```
여러분은 ``Type`` 그 자체뿐만 아니라 임의의 유형의 변수를 선언할 수 있습니다.
```lean
variable (α β γ : Type)
variable (g : β → γ) (f : α → β) (h : α → α)
variable (x : α)

def compose := g (f x)
def doTwice := h (h x)
def doThrice := h (h (h x))

#print compose
#print doTwice
#print doThrice
```
이것을 출력하는 것은 세 정의 그룹이 정확히 동일한 효과를 가짐을 보여줍니다.

 ``variable``명령은 Lean에게 선언된 변수를 그들을 이름으로 참조하는 정의의 구속 변수로 삽입하라고 지시합니다. Lean은 정의에서 명시적으로나 암시적으로 사용된 변수를 구분하기에 충분히 똑똑합니다. 그러므로 여러분은 여러분의 정의를 작성할 때  ``α``, ``β``, ``γ``, ``g``, ``f``, ``h``, ``x``가 고정된 대상임에도 사용할 수 있습니다. 그리고 lean이 여러분을 위해 자동으로 정의를 축약할 수 있게 합니다.

이 방식으로 선언되었을 때, 변수는 여러분이 작업하는 파일 끝까지를 범위로 가질 겁니다. 그러나 때때로 변수의 범위를 제한하는 것이 유용합니다. 이를 위해 Lean은  ``section``의 개념을 제공합니다.

```lean
section useful
  variable (α β γ : Type)
  variable (g : β → γ) (f : α → β) (h : α → α)
  variable (x : α)

  def compose := g (f x)
  def doTwice := h (h x)
  def doThrice := h (h (h x))
end useful
```

섹션이 닫히게 될 때, 변수들은 범위를 벗어나게 됩니다. 그리고 구분된 메모리 외에 아무것도 없게 됩니다.

섹션 안에서 줄에 들여쓰기를 하거나  섹션에 이름을 줄 필요도 없습니다. 그말은 즉슨, 여러분은 익명의 ``section`` / ``end`` 쌍을 사용할 수 있다는 것입니다. 그러나 여러분이 섹션에 이름을 붙이고자 한다면 같은 이름을 사용해 이를 닫아야 합니다. section은 중첩될 수도 있습니다. 이는 여러분에게 새로운 변수를 점진적으로 선언할 수 있게 합니다.

# 이름공간(Namespaces)

Lean은 여러분에게 정의를 중첩되고 계층적인 *namespaces*에 묶을 수 있는 능력을 제공합니다.

```lean
namespace Foo
  def a : Nat := 5
  def f (x : Nat) : Nat := x + 7

  def fa : Nat := f a
  def ffa : Nat := f (f a)

  #check a
  #check f
  #check fa
  #check ffa
  #check Foo.fa
end Foo

-- #check a  -- error
-- #check f  -- error
#check Foo.a
#check Foo.f
#check Foo.fa
#check Foo.ffa

open Foo

#check a
#check f
#check fa
#check Foo.fa
```

이름공간 ``Foo``에서 작업한다고 여러분이 선언할 때 여러분이 선언한 모든 식별자들은 "``Foo.``"를 접미사로 갖습니다. 이름공간 안에서 여러분은 식별자들을 그들의 약식 이름으로 부를 수 있습니다. 그러나 한번 이름공간에 끝에 오면 여러분은 더 긴 이름을 사용해야만 합니다.
`section`과는 달리, 이름공간은 이름이 필요합니다. root 계층에서만 익명 이름 공간이 있습니다.

``open`` 명령은 현재 맥락에서 짧은 이름을 가져옵니다.
 짧은 식별자로 접근하기 위해서 종종 여러분이 모듈을 가져오기(import) 할 때, 모듈이 담은 다수의 이름공간을 열기 원할 것입니다. 그러나 때로는 당신이 사용할 다른 이름공간과 식별자가 충돌할 때 여러분이 이 정보가 완전히 자격을 갖춘 이름으로 보호되길 원할 것입니다. 따라서 이름공간은 당신의 작업 환경 속에 이름을 관리하는 방법을 줍니다.

예를 들어 Lean은 이름공간 ``List`` 속에 리스트를 포함한 정의와 정리를 묶습니다.
```lean
#check List.nil
#check List.cons
#check List.map
```
``open List`` 명령은 여러분이 더 짧은 이름을 사용할 수 있게 합니다.
```lean
open List

#check nil
#check cons
#check map
```
section처럼 이름공간도 중첩될 수 있습니다.
```lean
namespace Foo
  def a : Nat := 5
  def f (x : Nat) : Nat := x + 7

  def fa : Nat := f a

  namespace Bar
    def ffa : Nat := f (f a)

    #check fa
    #check ffa
  end Bar

  #check fa
  #check Bar.ffa
end Foo

#check Foo.fa
#check Foo.Bar.ffa

open Foo

#check fa
#check Bar.ffa
```
닫힌 이름공간은 심지어 다른 파일일지라도 나중에 다시 열릴 수 있습니다.

```lean
namespace Foo
  def a : Nat := 5
  def f (x : Nat) : Nat := x + 7

  def fa : Nat := f a
end Foo

#check Foo.a
#check Foo.f

namespace Foo
  def ffa : Nat := f (f a)
end Foo
```

섹션과 마찬가지로 중첩된 이름공간은 그들이 열린 순서대로 닫혀야 합니다. 이름공간과 섹션은 다른 목적을 갖고 일합니다. 이름공간은 데이터를 정리하고 섹션은 정의의 삽입에 대해 변수를 선언합니다. section은 ``set_option``과 ``open``같이 명령의 범위를 제한하는데 유용합니다.

하지만 여러 관점에서 ``namespace ... end``블록은 ``section ... end``블록과 동일하게 동작합니다. 특히, 이름공간 안에서 ``variable`` 명령을 사용한다면 그것의 범위는 이름공간으로 제한될 것입니다. 마찬가지로 여러분이 이름공간 내에서 ``open`` 명령을 사용한다면 그것의 효과는 이름공간이 닫힐 때 사라질 것 입니다.

## 무엇이 의존 유형론을 의존적이게 만드는가?

간단한 설명은 유형이 매개변수에 의존할 수 있다는 겁니다. 여러분은 이것에 대한 멋진 예제를 보았습니다. 유형  ``List α`` 는 인수 ``α``에 의존합니다. 여기서  ``List Nat``과 ``List Bool``을 구분하는 것은 이 의존입니다. 또 다른 예시로 유형 ``Vector α n``을 고려해보세요. 이 벡터의 유형은 길이 ``n``인 ``α``를 원소로 하는 리스트입니다.  이 유형은 *두* 매개변수에 의존합니다. 하나는 벡터의 원소의 유형 (``α : Type``)이고 또 다른 하나는 벡터의 길이``n : Nat``입니다.

여러분이 리스트의 머리에 새 원소를 삽입하는 함수 ``cons``를 만들기 원한다 해봅시다. ``cons``는 어떤 유형을 가져야 할까요? 이러한 함수는 *polymorphic*입니다. 여러분은 ``cons``는  ``Nat``, ``Bool`` 혹은 임의의 유형  ``α``에 대해 동일한 방식으로 동작해야 한다고 기대합니다.
그래서 ``cons``의 첫번째 인수의 유형으로 임의의 유형 ``α``를 받아들이게 하는게 타당합니다. ``cons α``는 ``α``유형을 원소로 하는 리스트에 대한 삽입 함수입니다. 다시 말하면 모든 ``α``에 대해  ``cons α``는 원소 ``a : α``와 리스트 ``as : List α``를 받는 함수입니다.  그리고 새로운 리스트를 반환합니다. 그래서 여러분은  ``cons α a as : List α``를 갖습니다.

``cons α``가  ``α → List α → List α`` 유형을 가져야 함은 분명합니다.
그러나  ``cons``는 어떤 유형을 가져야 할까요?  첫 번째 추측은 ``Type → α → list α → list α``일지 모릅니다. 그러나 생각해보면 이는 말이 되지 않습니다. 이 식에서 ``α``는 어떤 것도 지칭하지 않으므로 ``Type`` 유형을 인수로 지칭해야 합니다.  다시 말하면 함수의 첫 번째 인수로  ``α : Type``으로  *가정*하면 다음 두 원소의 유형은  ``α``와 ``List α``가 됩니다. 이 유형은 첫번째 인수 ``α``에 따라 달라집니다.

```lean
def cons (α : Type) (a : α) (as : List α) : List α :=
  List.cons a as

#check cons Nat        -- Nat → List Nat → List Nat
#check cons Bool       -- Bool → List Bool → List Bool
#check cons            -- (α : Type) → α → List α → List α
```

이것은 *의존적 함수 유형* 또는 *의존적 방향 유형*의 개체입니다. ``α : Type``과``β : α → Type``이라면, ``β``를 ``α``에 대한 유형 족(family)으로 생각할 수 있습니다. 즉, 각각의 ``a : α``에 대해 ``β a``유형입니다. 이 경우 유형 ``(a : α) → β a``는 모든  ``a : α``에 대해,  ``f a``가 ``β a``의 원소라는 성질로 ``f`` 함수의 유형을 지칭합니다. 다시 말하자면 ``f``에 의해 반환되는 값의 유형은 그것의 입력에 의존합니다.

``(a : α) → β``는  모든 식  ``β : Type``에 대해 성립하는 것을 주목하세요. ``β``의 값이 ``a``에 의존할 때(예를 들어 앞 단락에서 식 ``β a``처럼), ``(a : α) → β``는 의존적 함수 유형을 나타냅니다.  ``β``가  ``a``에 의존하지 않을 때, ``(a : α) → β``는 유형 ``α → β``유형과 다르지 않습니다.  물론, 종속 유형론에서(그리고 Lean에서) ``α → β``는 ``β``가 ``a``에 의존하지 않을 때 ``(a : α) → β``에 대한 표기일 뿐입니다.

리스트의 예로 돌아가서 여러분은 다음 `List` 함수의 유형을 검사하기 위해 `#check` 명령을 사용할 수 있습니다.  ``@`` 기호와 소괄호와 중괄호 사이의 차이는 곧 설명할 것입니다.

```lean
#check @List.cons    -- {α : Type u_1} → α → List α → List α
#check @List.nil     -- {α : Type u_1} → List α
#check @List.length  -- {α : Type u_1} → List α → Nat
#check @List.append  -- {α : Type u_1} → List α → List α → List α
```

의존적 함수 유형 ``(a : α) → β a``는 함수의 유형 ``α → β``의 개념을 ``β``가 ``α``에 종속적이라고 함으로써 일반화한 것처럼 의존적 카테시안 곱 유형은 ``(a : α) × β a``는 카테시안 곱 ``α × β``를 같은 방식으로 일반화합니다. 의존적 곱은 *sigma*유형이라고 불립니다. 그리고 여러분은 그것을 `Σ a : α, β a`처럼 쓸 수 있습니다. 여러분은 `⟨a, b⟩` 또는 `Sigma.mk a b`를 종속적 쌍을 만드는데 쓸 수 있습니다.

```lean
universe u v

def f (α : Type u) (β : α → Type v) (a : α) (b : β a) : (a : α) × β a :=
  ⟨a, b⟩

def g (α : Type u) (β : α → Type v) (a : α) (b : β a) : Σ a : α, β a :=
  Sigma.mk a b

def h1 (x : Nat) : Nat :=
  (f Type (fun α => α) Nat x).2

#eval h1 5 -- 5

def h2 (x : Nat) : Nat :=
  (g Type (fun α => α) Nat x).2

#eval h2 5 -- 5
```
위 함수  `f`와 `g`는 같은 함수를 지칭합니다.


암시적 인자(Implicit Arguments)
------------------

우리가 리스트의 구현을 다음과 같이 했다고 가정합시다.

```lean
# universe u
# def Lst (α : Type u) : Type u := List α
# def Lst.cons (α : Type u) (a : α) (as : Lst α) : Lst α := List.cons a as
# def Lst.nil (α : Type u) : Lst α := List.nil
# def Lst.append (α : Type u) (as bs : Lst α) : Lst α := List.append as bs
#check Lst          -- Type u_1 → Type u_1
#check Lst.cons     -- (α : Type u_1) → α → Lst α → Lst α
#check Lst.nil      -- (α : Type u_1) → Lst α
#check Lst.append   -- (α : Type u_1) → Lst α → Lst α → Lst α
```

그럼 여러분은  `Nat`의 리스트를 다음과 같이 생성할 수 있습니다.

```lean
# universe u
# def Lst (α : Type u) : Type u := List α
# def Lst.cons (α : Type u) (a : α) (as : Lst α) : Lst α := List.cons a as
# def Lst.nil (α : Type u) : Lst α := List.nil
# def Lst.append (α : Type u) (as bs : Lst α) : Lst α := List.append as bs
# #check Lst          -- Type u_1 → Type u_1
# #check Lst.cons     -- (α : Type u_1) → α → Lst α → Lst α
# #check Lst.nil      -- (α : Type u_1) → Lst α
# #check Lst.append   -- (α : Type u_1) → Lst α → Lst α → Lst α
#check Lst.cons Nat 0 (Lst.nil Nat)

def as : Lst Nat := Lst.nil Nat
def bs : Lst Nat := Lst.cons Nat 5 (Lst.nil Nat)

#check Lst.append Nat as bs
```

생성자들이 유형에 대해 다형적이기 때문에, 우리는 유형 ``Nat``를 인수로써 반복적으로 삽입해야 합니다. 그러나 이 정보는 중복적입니다. ``Lst.cons Nat 5 (Lst.nil Nat)``에서 두번째 인수 ``5``가 ``Nat`` 유형을 가진다는 사실로부터 인수 ``α``를 추론할 수 있습니다. 어떤 식으로부터도 아니고 ``Lst α``형의 원소를 기대하는 `` Lst.cons`` 함수에 인수로 전달되었다는 사실로부터 누군가는 비슷하게 ``Lst.nil Nat``에서 인수를 추론할 수 있습니다.

이는 의존 유형론의 핵심 특징입니다. 항은 많은 정보를 전달하고 종종 그 정보의 몇은  맥락으로부터 추론될 수 있습니다. Lean에서 누군가는 시스템이 자동적으로 정보를 채워넣도록 명시하기 위해 밑줄문자(``_``)를 사용합니다. 이것은 "암시적 인자"라고 합니다.

```lean
# universe u
# def Lst (α : Type u) : Type u := List α
# def Lst.cons (α : Type u) (a : α) (as : Lst α) : Lst α := List.cons a as
# def Lst.nil (α : Type u) : Lst α := List.nil
# def Lst.append (α : Type u) (as bs : Lst α) : Lst α := List.append as bs
# #check Lst          -- Type u_1 → Type u_1
# #check Lst.cons     -- (α : Type u_1) → α → Lst α → Lst α
# #check Lst.nil      -- (α : Type u_1) → Lst α
# #check Lst.append   -- (α : Type u_1) → Lst α → Lst α → Lst α
#check Lst.cons _ 0 (Lst.nil _)

def as : Lst Nat := Lst.nil _
def bs : Lst Nat := Lst.cons _ 5 (Lst.nil _)

#check Lst.append _ as bs
```

그래도 여전히 이 밑줄문자를 치는 것은 번거롭습니다. 함수가 일반적으로 맥락으로부터 추론할 수 있는 인수를 받을 때, Lean은 여러분이 이런 인수가 암시적이어야 함을 명시하도록 기본적으로 허용합니다. 이것은 다음과 같이 인수를 중괄호 안에 두는 것으로 할 수 있습니다.

```lean
universe u
def Lst (α : Type u) : Type u := List α

def Lst.cons {α : Type u} (a : α) (as : Lst α) : Lst α := List.cons a as
def Lst.nil {α : Type u} : Lst α := List.nil
def Lst.append {α : Type u} (as bs : Lst α) : Lst α := List.append as bs

#check Lst.cons 0 Lst.nil

def as : Lst Nat := Lst.nil
def bs : Lst Nat := Lst.cons 5 Lst.nil

#check Lst.append as bs
```

바뀐 것이라곤 변수 선언에서 ``α : Type u`` 주위의 괄호뿐입니다. 우리는 함수 정의에서도 이 기능을 쓸 수 있습니다.

```lean
universe u
def ident {α : Type u} (x : α) := x

#check ident         -- ?m → ?m
#check ident 1       -- Nat
#check ident "hello" -- String
#check @ident        -- {α : Type u_1} → α → α
```

이 첫 인수는 ``ident``를 암시적으로 만듭니다. 표기상으로 ``ident``가 단순히 임의의 유형의 인수를 받을 수 있는 것처럼 만들어 유형의 명세를 감춥니다. 사실 함수 ``id``는 표준 라이브러리에서도 이와 정확히 동일한 방식으로 정의되어 있습니다. 우리는 여기서 이름의 충돌을 방지하기 위해 비관습적인 이름을 선택할 뿐이었습니다.

``variable`` 명령으로 선언될 때 변수도 암시적으로 구체화될 수 있습니다.

```lean
universe u

section
  variable {α : Type u}
  variable (x : α)
  def ident := x
end

#check ident
#check ident 4
#check ident "hello"
```

``ident``의 이 정의는 여기서 위의 것과 같이 같은 효과를 갖습니다.

Lean은 암시적인 인수를 인스턴스화(instantiating)하는데 아주 복잡한 매커니즘을 가지고 있습니다. 그리고 우리는 함수의 유형과 술어 그리고 심지어 증명을 추론하는데 사용될 수 있음을 볼 것입니다. 이런 "구멍" 또는 "플레이스 홀더"의 인스턴스화 과정은 *협력(elaboration)*으로 불리기도 합니다. 암시적 인수의 존재는 현재로는 식의 정확한 의미를 고치기에 정보가 불충분함을 의미할 수 있습니다. 다른 맥락에서 다른 의미를 가질 수 있기 때문에 ``id`` 나 ``List.nil`` 같은 표현식을 *다형적*이라 합니다.

누군가는 표현식 ``e``의 유형 ``T``를 ``(e : T)``와 같이 씀으로써 항상 명시할 수 있습니다. 이것은 린의 협력기가 암시적 인수를 해결하려고 시도할 때 ``e``의 유형으로 ``T``값을 사용하라고 지시합니다. 아래 예제의 쌍의 두 번째에서, 이 메커니즘은 식 ``id``와 ``List.nil``의 바람직한 유형을 명시하는데 사용됩니다.

```lean
#check List.nil               -- List ?m
#check id                     -- ?m → ?m

#check (List.nil : List Nat)  -- List Nat
#check (id : Nat → Nat)       -- Nat → Nat
```

수치들은 Lean에 매우 많이 있습니다. 그러나 수치 유형이 추론되지 못할 때, 린은 기본적으로 그걸 자연수라고 가정합니다. 그래서 아래 첫 두 ``#check``명령에서 표현식은 같은 방식으로 해석됩니다. 반면 세 번째 ``#check`` 명령은 ``2``를 정수로 해석합니다.

```lean
#check 2            -- Nat
#check (2 : Nat)    -- Nat
#check (2 : Int)    -- Int
```

하지만 때때로 우리는 우리 스스로 함수에 대한 인수가 암시적이도록 선언하는 걸 발견합니다. 그러나 지금 인수를 명시적으로 제공하길 원합니다. 만약 ``foo``가 그런 함수라면 ``@foo`` 표기는 모든 인수가 명시적으로 된 같은 함수를 지칭합니다.

```lean
#check @id        -- {α : Type u_1} → α → α
#check @id Nat    -- Nat → Nat
#check @id Bool   -- Bool → Bool

#check @id Nat 1     -- Nat
#check @id Bool true -- Bool
```

현재 첫 번째 ``#check`` 명령은 식별자 ``id``의 유형을 어떤 플레이스 홀더도 삽입하지 않고 주는 것을 보세요. 게다가 출력은 첫 번째 인수가 암시적임을 가리킵니다.
