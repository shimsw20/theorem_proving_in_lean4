유도형
===============

우리는 린의 형식적인 기초가 기본형 ``Prop, Type 0, Type 1, Type 2, ...``을 포합하고 의존 함수형 ``(x : α) → β``의 형성을 가능하게 함을 보았습니다. 예제에서 우리는 ``Bool``, ``Nat``, and ``Int`` 같은 추가 유형과 유형 생성자 ``List``과 product, ``×``의 사용을 보았습니다. 사실 린의 라이브러리에서 세계보다는 모든 구체적인 유형과 의존 화살표 외에 모든 형 생성자는 *inductive types*으로 알려진 일반적인 유형 생성의 일종의 개체입니다. 유형 세계, 의존 화살표 유형과 유도형과 그들로부터 나라 나온 모든 것 외에는 아무것도 기반으로 하지 않는 수학의 실질적인 구조를 구성하는 것이 가능하다는 것은 주목할 만합니다.

당연히 유도형은 생성자의 명시된 리스트로부터 만들어집니다. 린에서 그런 유형을 나타내는 문법은 다음과 같습니다.

```
    inductive Foo where
      | constructor₁ : ... → Foo
      | constructor₂ : ... → Foo
      ...
      | constructorₙ : ... → Foo
```

직관적인 설명은 아마 이전에 구성된 값으로부터 각 생성자가 ``Foo``의 새로운 대상을 만드는 방식을 지정한다는 것입니다. ``Foo`` 유형은 이 방식으로 생성된 대상 외에 아무것도 갖고있지 않습니다. 유도 선언에서 첫 문자 ``|``은 선택적입니다. 또 우리는 ``|`` 대신 콤마를 사용해 생성자를 나눌 수 있습니다.

우리는 아래에서 생성자의 인자가 ``Foo`` 형의 대상을 특정 ``Foo``의 원소가 상향식으로 만들어졌음을 보장하는 "긍정성" 제약을 조건으로 하여 포함할 수 있음을 볼 것입니다. 대략적으로 말하자면 각 ``...``는 의존 화살표 형의 "대상"으로만 ``Foo``및 이전에 정의된 유형으로 구성된 모든 화살표 유형이 될 수 있습니다.

우리는 다수의 유도형의 예제를 제공합니다. 우리는 유도형과 일명 유도군을 동시에 정의하도록 위의 계획의 약간의 일반화를 고려할 것입니다.

논리 연결사와 마찬가지로 모든 유도형은 유형의 원소를 어떻게 생성하는지 보여주는 도입 규칙과 또다른 생성에서 유형의 원소를 어떻게 "사용"하는지 보여주는 제거 규칙을 동반합니다. 논리 연결사와 유사점은 놀라움으로 오지 말아야 합니다. 우리가 아래에서 보듯이 그들도 유도형 생성의 예제입니다. 여러분은 유도형에 대한 도입규칙을 이미 봤었습니다. 그들은 그저 유형의 정의에서 명시된 생성자들일 뿐입니다. 제거 규칙은 유형의 재귀의 원리를 제공합니다. 이것은 특별한 경우로서 귀납의 원리도 포합합니다.

다음 장에서 우리는 린의 정의 패키지를 설명합니다. 이 패키지는 함수와 유도형과 유도 증명을 수행하는 심지어 더 편리한 방법을 제공합니다. 그러나 유도형의 개념은 너무 근본적이라 우리는 저수준의 실습 이해부터 시작하는 것이 중요하다고 느낍니다. 우리는 유도형의 몇 가지 기본적인 예제로 시작할 것입니다. 그리고 우리의 작업을 더 정교하고 복잡한 예제로 옮겨갈 것입니다.

열거 유형
----------------

가장 간단한 유도형은 원소의 리스트를 유한하게 열거한 유형입니다.

```lean
inductive Weekday where
  | sunday : Weekday
  | monday : Weekday
  | tuesday : Weekday
  | wednesday : Weekday
  | thursday : Weekday
  | friday : Weekday
  | saturday : Weekday
```

``inductive`` 명령은 새로운 유형 ``Weekday``를 만듭니다. 생성자는 모두 ``Weekday`` 이름공간에 살고 있습니다.

```lean
# inductive Weekday where
#  | sunday : Weekday
#  | monday : Weekday
#  | tuesday : Weekday
#  | wednesday : Weekday
#  | thursday : Weekday
#  | friday : Weekday
#  | saturday : Weekday
#check Weekday.sunday
#check Weekday.monday

open Weekday

#check sunday
#check monday
```

여러분은  유도형 `Weekday`를 선언할 때 `: Weekday`을 생략할 수 있습니다.

```lean
inductive Weekday where
  | sunday
  | monday
  | tuesday
  | wednesday
  | thursday
  | friday
  | saturday
```

다른 성질을 구별할 것 없이 ``sunday``, ``monday``, ... , ``saturday``를 ``Weekday``의 구별되는 원소로서 생각해보세요. 제거 규칙  ``Weekday.rec``은 ``Weekday``형과 그것의 생성자를 따라 정의되었습니다. 이는 *recursor*로도 알려져 있고, 이게 유형을 "유도적"으로 만드는 것입니다. 이게 각 생성자에 대응하는 값을 할당함으로 ``Weekday``에 함수를 정의할 수 있게 허용합니다. 직관적인 설명은 유도형은 생성자에 의해 철저히 생성된다는 점입니다. 그래서 이들 없이 생긴 원소는 없습니다.

우리는 ``Weekday``로부터 자연수로의 함수를 정의하는데 `match` 표현식을 사용합니다.

```lean
# inductive Weekday where
#  | sunday : Weekday
#  | monday : Weekday
#  | tuesday : Weekday
#  | wednesday : Weekday
#  | thursday : Weekday
#  | friday : Weekday
#  | saturday : Weekday
open Weekday

def numberOfDay (d : Weekday) : Nat :=
  match d with
  | sunday    => 1
  | monday    => 2
  | tuesday   => 3
  | wednesday => 4
  | thursday  => 5
  | friday    => 6
  | saturday  => 7

#eval numberOfDay Weekday.sunday  -- 1
#eval numberOfDay Weekday.monday  -- 2
#eval numberOfDay Weekday.tuesday -- 3
```

`match` 표현식은 여러분이 유도형을 선언할 때 생성한 *recursor* `Weekday.rec`을 사용하여 컴파일 됩니다.

```lean
# inductive Weekday where
#  | sunday : Weekday
#  | monday : Weekday
#  | tuesday : Weekday
#  | wednesday : Weekday
#  | thursday : Weekday
#  | friday : Weekday
#  | saturday : Weekday
open Weekday

def numberOfDay (d : Weekday) : Nat :=
  match d with
  | sunday    => 1
  | monday    => 2
  | tuesday   => 3
  | wednesday => 4
  | thursday  => 5
  | friday    => 6
  | saturday  => 7

set_option pp.all true
#print numberOfDay
-- ... numberOfDay.match_1
#print numberOfDay.match_1
-- ... Weekday.casesOn ...
#print Weekday.casesOn
-- ... Weekday.rec ...
#check @Weekday.rec
/-
@Weekday.rec.{u}
 : {motive : Weekday → Sort u} →
    motive Weekday.sunday →
    motive Weekday.monday →
    motive Weekday.tuesday →
    motive Weekday.wednesday →
    motive Weekday.thursday →
    motive Weekday.friday →
    motive Weekday.saturday →
    (t : Weekday) → motive t
-/
```

유도 데이터형을 선언할 때, 여러분은 린에게 `Weekday`의 대상을 텍스트로 바꾸는 함수를 생성하라고 지시하도록 `deriving Repr`을 사용할 수 있습니다.
이 함수는 `Weekday`  대상을 표시하도록 `#eval` 명령으로 사용됩니다.

```lean
inductive Weekday where
  | sunday
  | monday
  | tuesday
  | wednesday
  | thursday
  | friday
  | saturday
  deriving Repr

open Weekday

#eval tuesday   -- Weekday.tuesday
```

정의들과 정리들을 같은 이름인 이름공간에 구조체와 연관지어 모으는 것이 종종 유용합니다. 예를 들어, 우리는 ``Weekday`` 이름공간에 ``numberOfDay``함수를 넣을 수 있습니다. 그럼 우리는 우리가 이름공간을 열었을 때 더 짧은 이름을 사용할 수 있게 됩니다.

우리는 ``Weekday``에서 ``Weekday``까지 함수를 정의할 수 있습니다.

```lean
# inductive Weekday where
#  | sunday : Weekday
#  | monday : Weekday
#  | tuesday : Weekday
#  | wednesday : Weekday
#  | thursday : Weekday
#  | friday : Weekday
#  | saturday : Weekday
#  deriving Repr

namespace Weekday
def next (d : Weekday) : Weekday :=
  match d with
  | sunday    => monday
  | monday    => tuesday
  | tuesday   => wednesday
  | wednesday => thursday
  | thursday  => friday
  | friday    => saturday
  | saturday  => sunday

def previous (d : Weekday) : Weekday :=
  match d with
  | sunday    => saturday
  | monday    => sunday
  | tuesday   => monday
  | wednesday => tuesday
  | thursday  => wednesday
  | friday    => thursday
  | saturday  => friday

#eval next (next tuesday)      -- Weekday.thursday
#eval next (previous tuesday)  -- Weekday.tuesday

example : next (previous tuesday) = tuesday :=
  rfl

end Weekday
```

임의의 Weekday ``d``에 대해 ``next (previous d) = d``이라는 일반적인 일반적인 정리를 어떻게 증명할 수 있을까요? 우리는 각 생성자에 대해 주장의 증명을 제공하기 위해 `match`를 사용할 수 있습니다.

```lean
# inductive Weekday where
#  | sunday : Weekday
#  | monday : Weekday
#  | tuesday : Weekday
#  | wednesday : Weekday
#  | thursday : Weekday
#  | friday : Weekday
#  | saturday : Weekday
#  deriving Repr
# namespace Weekday
# def next (d : Weekday) : Weekday :=
#  match d with
#  | sunday    => monday
#  | monday    => tuesday
#  | tuesday   => wednesday
#  | wednesday => thursday
#  | thursday  => friday
#  | friday    => saturday
#  | saturday  => sunday
# def previous (d : Weekday) : Weekday :=
#  match d with
#  | sunday    => saturday
#  | monday    => sunday
#  | tuesday   => monday
#  | wednesday => tuesday
#  | thursday  => wednesday
#  | friday    => thursday
#  | saturday  => friday
def next_previous (d : Weekday) : next (previous d) = d :=
  match d with
  | sunday    => rfl
  | monday    => rfl
  | tuesday   => rfl
  | wednesday => rfl
  | thursday  => rfl
  | friday    => rfl
  | saturday  => rfl
```

심지어 전략 증명을 사용하면 더 간결하게 됩니다.

```lean
# inductive Weekday where
#  | sunday : Weekday
#  | monday : Weekday
#  | tuesday : Weekday
#  | wednesday : Weekday
#  | thursday : Weekday
#  | friday : Weekday
#  | saturday : Weekday
#  deriving Repr
# namespace Weekday
# def next (d : Weekday) : Weekday :=
#  match d with
#  | sunday    => monday
#  | monday    => tuesday
#  | tuesday   => wednesday
#  | wednesday => thursday
#  | thursday  => friday
#  | friday    => saturday
#  | saturday  => sunday
# def previous (d : Weekday) : Weekday :=
#  match d with
#  | sunday    => saturday
#  | monday    => sunday
#  | tuesday   => monday
#  | wednesday => tuesday
#  | thursday  => wednesday
#  | friday    => thursday
#  | saturday  => friday
def next_previous (d : Weekday) : next (previous d) = d := by
  cases d <;> rfl
```

[유도형을 위한 전략](#tactics_for_inductive_types) 아래에서 유도형의 사용을 위해 특별히 고안된 추가 전략들을 도입할 것입니다.

유형으로써 명제 대응 하에서 우리는 합수를 정의하는 것 뿐만 아니라 정리를 증명하는데 ``match``를 사용합니다.  다시 말하자면 유형으로써 명제 대응하에서 경우에 따른 증명은 경우에 따른 정의의 일종이고, 여기서 "정의되는" 것은 데이터의 조각 대신 증명입니다.

린 라이브러리에서 `Bool`형은 열거 유형의 개체입니다.
```lean
# namespace Hidden
inductive Bool where
  | false : Bool
  | true  : Bool
# end Hidden
```

(이 예제를 실행하려면 우리는 ``Hidden``이라는 이름공간에 이들을 두어서 ``Bool``같은 이름이 표준 라이브러리에서의 ``Bool``과 출돌하지 않게 해야 합니다. 이것은 이들 유형이 시스템이 시작할 때 자동적으로 불러와지는 린 "서막"의 일부이기 때문에 필요합니다.

연습으로 여러분은 이 유형들에 대한 도입과 제거 규칙이 하는 것에 대해 생각해봐야 합니다. 추가 연습으로 우리는 ``Bool``형에 불리언연산 ``and``, ``or``, ``not``을 정의하는 것을 제안합니다. 그리고 일반적인 항등식을 확인해보세요. 여러분이  ``and``같은 이항 연산을 `match`를 사용해 정의할 수 있다는 것을 보세요.

```lean
# namespace Hidden
def and (a b : Bool) : Bool :=
  match a with
  | true  => b
  | false => false
# end Hidden
```

마찬가지로 대부분의 항등식들은 적절한 `match`와 그 뒤 ``rfl``를 쓰는 것으로 증명될 수 있습니다.

인수를 가지는 생성자
---------------------------

열거 유형은 유도형의 아주 특별한 경우 입니다. 이들의 생성자는 인수를 전혀 받지 않습니다. 일반적으로 "생성"은 데이터에 의존할 수 있습니다. 그러면 그것은 생성된 인자에서 표현됩니다. 라이브러리에서 곱 유형의 정의와 합 유형의 정의를 고려해보세요.

```lean
# namespace Hidden
inductive Prod (α : Type u) (β : Type v)
  | mk : α → β → Prod α β

inductive Sum (α : Type u) (β : Type v) where
  | inl : α → Sum α β
  | inr : β → Sum α β
# end Hidden
```

우리가 생성자의 대상에 ``α``형과 ``β``형을 포함하지 않은 것을 주목하세요. 한편, 이 예제에서 무슨 일이 일어나는 건지 생각해보세요. 곱 유형은 하나의 생성자 ``Prod.mk``를 갖고 있습니다. 이것은 두 인수를 받습니다.  ``Prod α β``에서 함수를 정의하기 위해서 우리는 입력의 형태가 ``Prod.mk a b``이라 가정할 수 있습니다. 그리고 ``a``와 ``b``에 대해 출력을 명시해야 합니다. 우리는 이것을 ``Prod``에 대한 두 투영(projection)이라고 정의하는데 사용할 수있습니다. 표준 라이브러리는 ``Prod α β``에 대해 ``α × β`` 표기를 정의하고 ``Prod.mk a b``에 대해 ``(a, b)``를 정의합니다.

```lean
# namespace Hidden
# inductive Prod (α : Type u) (β : Type v)
#   | mk : α → β → Prod α β
def fst {α : Type u} {β : Type v} (p : Prod α β) : α :=
  match p with
  | Prod.mk a b => a

def snd {α : Type u} {β : Type v} (p : Prod α β) : β :=
  match p with
  | Prod.mk a b => b
# end Hidden
```

``fst`` 함수는 쌍 ``p``를 받습니다. `match`는 ``p``를 쌍으로서 해석합니다. ``Prod.mk a b`` [종속 유형론](./dependent_type_theory.md)으로부터 이들 정의에 가능한 가장 큰 일반성을 준 것을 기억하세요. 우리는 ``α``형과 ``β``형이 임의의 세계에 속함을 허용합니다.


여기에 `match` 대신 재귀자 `Prod.casesOn`을 사용하는 또다른 예제가 있습니다.

```lean
def prod_example (p : Bool × Nat) : Nat :=
  Prod.casesOn (motive := fun _ => Nat) p (fun b n => cond b (2 * n) (2 * n + 1))

#eval prod_example (true, 3)
#eval prod_example (false, 3)
```

인자 `motive`는 여러분이 생성하기 원하는 대상의 유형을 명시하는데 사용됩니다. 그리고 이것은 쌍에 의존할 수 있기에 함수입니다.
``cond`` 함수는 조건 불리언입니다. ``cond b t1 t2``은 ``b``가 참이면 ``t1``을 그렇지 않으면 ``t2``를 반환합니다.
함수 ``prod_example``은 불리언형 ``b``과 자연수형 ``n``을 받고 ``2 * n``나 ``2 * n + 1`` 둘 중의 하나를 ``b`` 가 참인지 거짓인지에 따라 출력하는 함수입니다.

대조적으로 합 유형은 *두* 생성자 ``inl``과 ``inr``이 있습니다. ("왼쪽 삽입"과 "오른쪽 삽입" 의미) 각각은 *한*개의 (명시적인) 인수를 받습니다. ``Sum α β``에 함수를 정의하기 위해서 우리는 두 경우를 다뤄야 합니다. 입력이 ``inl a``의 꼴인 경우 우리는 출력값을 ``a``에 대해 나타내야 하고 혹은 입력이 ``inr b``꼴인 경우 우리는 출력값을 ``b``에 대해 나타내야 합니다.

```lean
def sum_example (s : Sum Nat Nat) : Nat :=
Sum.casesOn (motive := fun _ => Nat) s
   (fun n => 2 * n)
   (fun n => 2 * n + 1)

#eval sum_example (Sum.inl 3)
#eval sum_example (Sum.inr 3)
```

이 예제는 이전의 것과 닮았다. 하지만 ``sum_example``의 입력이 이제 암시적으로 ``inl n``이나 ``inr n``의 꼴 둘 중의 하나이다.
첫 번째 경우는 함수는 ``2 * n``을 반환하고 두 번째 경우는 ``2 * n + 1``을 반환한다.

곱 유형은 생성자와 ``Prod``의 인수인 매개변수 ``α β : Type``에 의존하였음을 주목하세요. 린은 이 인수가 생성자의 나중 인수나 반환형으로부터 추론될 수 있을 때를 감지하고 그 경우 이들을 암시적이게 만듭니다.

이 섹션 다음에 우리는 유도형의 생성자가 자기 자신의 유도형으로부터 인수를 받을 때 무슨 일이 생기는지 알아볼 것이다. 예제를 특징짓는 것은 이 섹션에서 우리는 이 경우만이 아니라 각 생성자가 이전에 명시된 유형에만 의존한다는 점이다.

다수의 생성자가 있는 유형은 분리적임을 주목하세요. ``Sum α β``의 원소는 ``inl a``의 형태 *또는* ``inl b``의 형태입니다. 다수의 인수들이 있는 생성자는 결합적인 정보를 가져옵니다. ``Prod α β``의 원소  ``Prod.mk a b``으로부터 우리는 ``a``*그리고*``b``를 뽑아낼 수 있다. 임의의 유도형은 다수의 생성자를 갖거나 각각이 다수의 인수를 받게 함으로써 양쪽의 특징을 모두 포함할 수 있다.

함수 정의에서 처럼 린의 유도 정의 문법은 여러분이 이름붙은 인수를 콜론 앞에 생성자에 놓게 할 것이다.

```lean
# namespace Hidden
inductive Prod (α : Type u) (β : Type v) where
  | mk (fst : α) (snd : β) : Prod α β

inductive Sum (α : Type u) (β : Type v) where
  | inl (a : α) : Sum α β
  | inr (b : β) : Sum α β
# end Hidden
```

이 정의의 결과는 본질적으로 이전 섹션에서 제시된 것과 같습니다.

 ``Prod`` 같이 한 생성자만 갖고 있는 유형은 순수하게 결합적입니다. 생성자는 단순히 인수 리스트를 하나의 데이터 조각으로 뭉칩니다. 본질적으로 순차적인 인수들의 유형인 튜플은 초기 인수의 유형에 의존할 수 있습니다. 우리는 그런 유형으로써 "레코드" 혹은 "구조체"를 생각해볼 수도 있습니다. 린에에서 키워드 ``structure``는 그것의 투영 뿐만 아니라 유도형 같은 것을 동시에 정의하는데 사용될 수 있습니다.

```lean
# namespace Hidden
structure Prod (α : Type u) (β : Type v) where
  mk :: (fst : α) (snd : β)
# end Hidden
```

이 예제는 동시에 유도형 ``Prod``과 그것의 생성자 ``mk``, 평범한 제거자 (``rec``과
``recOn``) 뿐만 아니라 위에서 정의한 대로 투영 ``fst``과 ``snd``을 도입합니다.

여러분이 생성자의 이름을 지어주지 않는다면, 린은 ``mk``를 기본 이름으로 사용합니다. 예를 들어 다음은 RGB 3개의 값을 갖는 triple로서 색을 저장하는 레코드를 정의합니다.

```lean
structure Color where
  (red : Nat) (green : Nat) (blue : Nat)
  deriving Repr

def yellow := Color.mk 255 255 0

#eval Color.red yellow
```

The definition of ``yellow`` forms the record with the three values
shown, and the projection ``Color.red`` returns the red component.

You can avoid the parentheses if you add a line break between each field.

```lean
structure Color where
  red : Nat
  green : Nat
  blue : Nat
  deriving Repr
```

The ``structure`` command is especially useful for defining algebraic
structures, and Lean provides substantial infrastructure to support
working with them. Here, for example, is the definition of a
semigroup:

```lean
structure Semigroup where
  carrier : Type u
  mul : carrier → carrier → carrier
  mul_assoc : ∀ a b c, mul (mul a b) c = mul a (mul b c)
```

We will see more examples in [Chapter Structures and Records](./structures_and_records.md).

We have already discussed the dependent product type `Sigma`:

```lean
# namespace Hidden
inductive Sigma {α : Type u} (β : α → Type v) where
  | mk : (a : α) → β a → Sigma β
# end Hidden
```

Two more examples of inductive types in the library are the following:

```lean
# namespace Hidden
inductive Option (α : Type u) where
  | none : Option α
  | some : α → Option α

inductive Inhabited (α : Type u) where
  | mk : α → Inhabited α
# end Hidden
```

In the semantics of dependent type theory, there is no built-in notion
of a partial function. Every element of a function type ``α → β`` or a
dependent function type ``(a : α) → β`` is assumed to have a value
at every input. The ``Option`` type provides a way of representing partial functions. An
element of ``Option β`` is either ``none`` or of the form ``some b``,
for some value ``b : β``. Thus we can think of an element ``f`` of the
type ``α → Option β`` as being a partial function from ``α`` to ``β``:
for every ``a : α``, ``f a`` either returns ``none``, indicating the
``f a`` is "undefined", or ``some b``.

An element of ``Inhabited α`` is simply a witness to the fact that
there is an element of ``α``. Later, we will see that ``Inhabited`` is
an example of a *type class* in Lean: Lean can be instructed that
suitable base types are inhabited, and can automatically infer that
other constructed types are inhabited on that basis.

As exercises, we encourage you to develop a notion of composition for
partial functions from ``α`` to ``β`` and ``β`` to ``γ``, and show
that it behaves as expected. We also encourage you to show that
``Bool`` and ``Nat`` are inhabited, that the product of two inhabited
types is inhabited, and that the type of functions to an inhabited
type is inhabited.

Inductively Defined Propositions
--------------------------------

Inductively defined types can live in any type universe, including the
bottom-most one, ``Prop``. In fact, this is exactly how the logical
connectives are defined.

```lean
# namespace Hidden
inductive False : Prop

inductive True : Prop where
  | intro : True

inductive And (a b : Prop) : Prop where
  | intro : a → b → And a b

inductive Or (a b : Prop) : Prop where
  | inl : a → Or a b
  | inr : b → Or a b
# end Hidden
```

You should think about how these give rise to the introduction and
elimination rules that you have already seen. There are rules that
govern what the eliminator of an inductive type can eliminate *to*,
that is, what kinds of types can be the target of a recursor. Roughly
speaking, what characterizes inductive types in ``Prop`` is that one
can only eliminate to other types in ``Prop``. This is consistent with
the understanding that if ``p : Prop``, an element ``hp : p`` carries
no data. There is a small exception to this rule, however, which we
will discuss below, in the section on inductive families.

Even the existential quantifier is inductively defined:

```lean
# namespace Hidden
inductive Exists {α : Type u} (q : α → Prop) : Prop where
  | intro : ∀ (a : α), q a → Exists q
# end Hidden
```

Keep in mind that the notation ``∃ x : α, p`` is syntactic sugar for ``Exists (fun x : α => p)``.

The definitions of ``False``, ``True``, ``And``, and ``Or`` are
perfectly analogous to the definitions of ``Empty``, ``Unit``,
``Prod``, and ``Sum``. The difference is that the first group yields
elements of ``Prop``, and the second yields elements of ``Type u`` for
some ``u``. In a similar way, ``∃ x : α, p`` is a ``Prop``-valued
variant of ``Σ x : α, p``.

This is a good place to mention another inductive type, denoted
``{x : α // p}``, which is sort of a hybrid between
``∃ x : α, P`` and ``Σ x : α, P``.

```lean
# namespace Hidden
inductive Subtype {α : Type u} (p : α → Prop) where
  | mk : (x : α) → p x → Subtype p
# end Hidden
```

In fact, in Lean, ``Subtype`` is defined using the structure command:

The notation ``{x : α // p x}`` is syntactic sugar for ``Subtype (fun x : α => p x)``.
It is modeled after subset notation in set theory: the idea is that ``{x : α // p x}``
denotes the collection of elements of ``α`` that have property ``p``.

Defining the Natural Numbers
----------------------------

The inductively defined types we have seen so far are "flat":
constructors wrap data and insert it into a type, and the
corresponding recursor unpacks the data and acts on it. Things get
much more interesting when the constructors act on elements of the
very type being defined. A canonical example is the type ``Nat`` of
natural numbers:

```lean
# namespace Hidden
inductive Nat where
  | zero : Nat
  | succ : Nat → Nat
# end Hidden
```

There are two constructors. We start with ``zero : Nat``; it takes
no arguments, so we have it from the start. In contrast, the
constructor ``succ`` can only be applied to a previously constructed
``Nat``. Applying it to ``zero`` yields ``succ zero : Nat``. Applying
it again yields ``succ (succ zero) : Nat``, and so on. Intuitively,
``Nat`` is the "smallest" type with these constructors, meaning that
it is exhaustively (and freely) generated by starting with ``zero``
and applying ``succ`` repeatedly.

As before, the recursor for ``Nat`` is designed to define a dependent
function ``f`` from ``Nat`` to any domain, that is, an element ``f``
of ``(n : nat) → motive n`` for some ``motive : Nat → Sort u``.
It has to handle two cases: the case where the input is ``zero``, and the case where
the input is of the form ``succ n`` for some ``n : Nat``. In the first
case, we simply specify a target value with the appropriate type, as
before. In the second case, however, the recursor can assume that a
value of ``f`` at ``n`` has already been computed. As a result, the
next argument to the recursor specifies a value for ``f (succ n)`` in
terms of ``n`` and ``f n``. If we check the type of the recursor,

```lean
# namespace Hidden
# inductive Nat where
#  | zero : Nat
#  | succ : Nat → Nat
#check @Nat.rec
# end Hidden
```

you find the following:

```
  {motive : Nat → Sort u}
  → motive Nat.zero
  → ((n : Nat) → motive n → motive (Nat.succ n))
  → (t : Nat) → motive t
```

The implicit argument, ``motive``, is the codomain of the function being defined.
In type theory it is common to say ``motive`` is the *motive* for the elimination/recursion,
since it describes the kind of object we wish to construct.
The next two arguments specify how to compute the zero and successor cases, as described above.
They are also known as the ``minor premises``.
Finally, the ``t : Nat``, is the input to the function. It is also known as the ``major premise``.

The `Nat.recOn` is similar to `Nat.rec` but the major premise occurs before the minor premises.

```
@Nat.recOn :
  {motive : Nat → Sort u}
  → (t : Nat)
  → motive Nat.zero
  → ((n : Nat) → motive n → motive (Nat.succ n))
  → motive t
```

Consider, for example, the addition function ``add m n`` on the
natural numbers. Fixing ``m``, we can define addition by recursion on
``n``. In the base case, we set ``add m zero`` to ``m``. In the
successor step, assuming the value ``add m n`` is already determined,
we define ``add m (succ n)`` to be ``succ (add m n)``.

```lean
# namespace Hidden
inductive Nat where
  | zero : Nat
  | succ : Nat → Nat
  deriving Repr

def add (m n : Nat) : Nat :=
  match n with
  | Nat.zero   => m
  | Nat.succ n => Nat.succ (add m n)

open Nat

#eval add (succ (succ zero)) (succ zero)
# end Hidden
```

It is useful to put such definitions into a namespace, ``Nat``. We can
then go on to define familiar notation in that namespace. The two
defining equations for addition now hold definitionally:

```lean
# namespace Hidden
# inductive Nat where
#  | zero : Nat
#  | succ : Nat → Nat
#  deriving Repr
namespace Nat

def add (m n : Nat) : Nat :=
  match n with
  | Nat.zero   => m
  | Nat.succ n => Nat.succ (add m n)

instance : Add Nat where
  add := add

theorem add_zero (m : Nat) : m + zero = m := rfl
theorem add_succ (m n : Nat) : m + succ n = succ (m + n) := rfl

end Nat
# end Hidden
```

We will explain how the ``instance`` command works in
[Chapter Type Classes](./type_classes.md). In the examples below, we will henceforth use
Lean's version of the natural numbers.

Proving a fact like ``zero + m = m``, however, requires a proof by induction.
As observed above, the induction principle is just a special case of the recursion principle,
when the codomain ``motive n`` is an element of ``Prop``. It represents the familiar
pattern of an inductive proof: to prove ``∀ n, motive n``, first prove ``motive 0``,
and then, for arbitrary ``n``, assume ``ih : motive n`` and prove ``motive (succ n)``.

```lean
# namespace Hidden
open Nat

theorem zero_add (n : Nat) : 0 + n = n :=
  Nat.recOn (motive := fun x => 0 + x = x)
   n
   (show 0 + 0 = 0 from rfl)
   (fun (n : Nat) (ih : 0 + n = n) =>
    show 0 + succ n = succ n from
    calc
       0 + succ n = succ (0 + n) := rfl
                _ = succ n       := by rw [ih])
# end Hidden
```

Notice that, once again, when ``Nat.recOn`` is used in the context of
a proof, it is really the induction principle in disguise. The
``rewrite`` and ``simp`` tactics tend to be very effective in proofs
like these. In this case, each can be used to reduce the proof to:

```lean
# namespace Hidden
open Nat

theorem zero_add (n : Nat) : 0 + n = n :=
  Nat.recOn (motive := fun x => 0 + x = x) n
    rfl
    (fun n ih => by simp [add_succ, ih])
# end Hidden
```

For another example, let us prove the associativity of addition,
``∀ m n k, m + n + k = m + (n + k)``.
(The notation ``+``, as we have defined it, associates to the left, so ``m + n + k`` is really ``(m + n) + k``.)
The hardest part is figuring out which variable to do the induction on. Since addition is defined by recursion on the second argument,
``k`` is a good guess, and once we make that choice the proof almost writes itself:

```lean
# namespace Hidden
open Nat
theorem add_assoc (m n k : Nat) : m + n + k = m + (n + k) :=
  Nat.recOn (motive := fun k => m + n + k = m + (n + k)) k
    (show m + n + 0 = m + (n + 0) from rfl)
    (fun k (ih : m + n + k = m + (n + k)) =>
      show m + n + succ k = m + (n + succ k) from
      calc
          m + n + succ k = succ (m + n + k) := rfl
            _ = succ (m + (n + k)) := by rw [ih]
            _ = m + succ (n + k) := rfl
            _ = m + (n + succ k) := rfl)
# end Hidden
```

One again, you can reduce the proof to:

```lean
open Nat
theorem add_assoc (m n k : Nat) : m + n + k = m + (n + k) :=
  Nat.recOn (motive := fun k => m + n + k = m + (n + k)) k
    rfl
    (fun k ih => by simp [Nat.add_succ, ih]; done)
```

Suppose we try to prove the commutativity of addition. Choosing induction on the second argument, we might begin as follows:

```lean
open Nat
theorem add_comm (m n : Nat) : m + n = n + m :=
  Nat.recOn (motive := fun x => m + x = x + m) n
   (show m + 0 = 0 + m by rw [Nat.zero_add, Nat.add_zero])
   (fun (n : Nat) (ih : m + n = n + m) =>
    show m + succ n = succ n + m from
    calc m + succ n = succ (m + n) := rfl
                  _ = succ (n + m) := by rw [ih]
                  _ = succ n +  m  := sorry)
```

At this point, we see that we need another supporting fact, namely, that ``succ (n + m) = succ n + m``.
You can prove this by induction on ``m``:

```lean
open Nat

theorem succ_add (n m : Nat) : succ n + m = succ (n + m) :=
  Nat.recOn (motive := fun x => succ n + x = succ (n + x)) m
    (show succ n + 0 = succ (n + 0) from rfl)
    (fun (m : Nat) (ih : succ n + m = succ (n + m)) =>
     show succ n + succ m = succ (n + succ m) from
     calc succ n + succ m = succ (succ n + m) := rfl
           _  = succ (succ (n + m))           := by rw [ih]
           _  = succ (n + succ m)             := rfl)
```

You can then replace the ``sorry`` in the previous proof with ``succ_add``. Yet again, the proofs can be compressed:

```lean
# namespace Hidden
open Nat
theorem succ_add (n m : Nat) : succ n + m = succ (n + m) :=
  Nat.recOn (motive := fun x => succ n + x = succ (n + x)) m
    rfl
    (fun m ih => by simp only [add_succ, ih])

theorem add_comm (m n : Nat) : m + n = n + m :=
  Nat.recOn (motive := fun x => m + x = x + m) n
    (by simp)
    (fun m ih => by simp only [add_succ, succ_add, ih])
# end Hidden
```

Other Recursive Data Types
--------------------------

Let us consider some more examples of inductively defined types. For
any type, ``α``, the type ``List α`` of lists of elements of ``α`` is
defined in the library.

```lean
# namespace Hidden
inductive List (α : Type u) where
| nil  : List α
| cons : α → List α → List α

namespace List

def append (as bs : List α) : List α :=
  match as with
  | nil       => bs
  | cons a as => cons a (append as bs)

theorem nil_append (as : List α) : append nil as = as :=
  rfl

theorem cons_append (a : α) (as bs : List α)
                    : append (cons a as) bs = cons a (append as bs) :=
  rfl

end List
# end Hidden
```

A list of elements of type ``α`` is either the empty list, ``nil``, or
an element ``h : α`` followed by a list ``t : List α``.
The first element, ``h``, is commonly known as the "head" of the list,
and the remainder, ``t``, is known as the "tail."

As an exercise, prove the following:

```lean
# namespace Hidden
# inductive List (α : Type u) where
# | nil  : List α
# | cons : α → List α → List α
# namespace List
# def append (as bs : List α) : List α :=
#  match as with
#  | nil       => bs
#  | cons a as => cons a (append as bs)
# theorem nil_append (as : List α) : append nil as = as :=
#  rfl
# theorem cons_append (a : α) (as bs : List α)
#                     : append (cons a as) bs = cons a (append as bs) :=
#  rfl
theorem append_nil (as : List α) : append as nil = as :=
  sorry

theorem append_assoc (as bs cs : List α)
        : append (append as bs) cs = append as (append bs cs) :=
  sorry
# end List
# end Hidden
```

Try also defining the function ``length : {α : Type u} → List α → Nat`` that returns the length of a list,
and prove that it behaves as expected (for example, ``length (append as bs) = length as + length bs``).

For another example, we can define the type of binary trees:

```lean
inductive BinaryTree where
  | leaf : BinaryTree
  | node : BinaryTree → BinaryTree → BinaryTree
```

In fact, we can even define the type of countably branching trees:

```lean
inductive CBTree where
  | leaf : CBTree
  | sup : (Nat → CBTree) → CBTree

namespace CBTree

def succ (t : CBTree) : CBTree :=
  sup (fun _ => t)

def toCBTree : Nat → CBTree
  | 0 => leaf
  | n+1 => succ (toCBTree n)

def omega : CBTree :=
  sup toCBTree

end CBTree
```

Tactics for Inductive Types
---------------------------

Given the fundamental importance of inductive types in Lean, it should
not be surprising that there are a number of tactics designed to work
with them effectively. We describe some of them here.

The ``cases`` tactic works on elements of an inductively defined type,
and does what the name suggests: it decomposes the element according
to each of the possible constructors. In its most basic form, it is
applied to an element ``x`` in the local context. It then reduces the
goal to cases in which ``x`` is replaced by each of the constructions.

```lean
example (p : Nat → Prop) (hz : p 0) (hs : ∀ n, p (Nat.succ n)) : ∀ n, p n := by
  intro n
  cases n
  . exact hz  -- goal is p 0
  . apply hs  -- goal is a : ℕ ⊢ p (succ a)
```

There are extra bells and whistles. For one thing, ``cases`` allows
you to choose the names for each alternative using a
``with`` clause. In the next example, for example, we choose the name
``m`` for the argument to ``succ``, so that the second case refers to
``succ m``. More importantly, the cases tactic will detect any items
in the local context that depend on the target variable. It reverts
these elements, does the split, and reintroduces them. In the example
below, notice that the hypothesis ``h : n ≠ 0`` becomes ``h : 0 ≠ 0``
in the first branch, and ``h : succ m ≠ 0`` in the second.

```lean
open Nat

example (n : Nat) (h : n ≠ 0) : succ (pred n) = n := by
  cases n with
  | zero =>
    -- goal: h : 0 ≠ 0 ⊢ succ (pred 0) = 0
    apply absurd rfl h
  | succ m =>
    -- second goal: h : succ m ≠ 0 ⊢ succ (pred (succ m)) = succ m
    rfl
```

Notice that ``cases`` can be used to produce data as well as prove propositions.

```lean
def f (n : Nat) : Nat := by
  cases n; exact 3; exact 7

example : f 0 = 3 := rfl
example : f 5 = 7 := rfl
```

Once again, cases will revert, split, and then reintroduce depedencies in the context.

```lean
def Tuple (α : Type) (n : Nat) :=
  { as : List α // as.length = n }

def f {n : Nat} (t : Tuple α n) : Nat := by
  cases n; exact 3; exact 7

def myTuple : Tuple Nat 3 :=
  ⟨[0, 1, 2], rfl⟩

example : f myTuple = 7 :=
  rfl
```

Here is an example with multiple constructors with arguments.

```lean
inductive Foo where
  | bar1 : Nat → Nat → Foo
  | bar2 : Nat → Nat → Nat → Foo

def silly (x : Foo) : Nat := by
  cases x with
  | bar1 a b => exact b
  | bar2 c d e => exact e
```

The alternatives for each constructor don't need to be solved
in the order the constructors were declared.

```lean
inductive Foo where
  | bar1 : Nat → Nat → Foo
  | bar2 : Nat → Nat → Nat → Foo

def silly (x : Foo) : Nat := by
  cases x with
  | bar2 c d e => exact e
  | bar1 a b => exact b
```

The syntax of the ``with`` is convenient for writing structured proofs.
Lean also provides a complementary ``case`` tactic, which allows you to focus on goal
assign variable names.

```lean
inductive Foo where
  | bar1 : Nat → Nat → Foo
  | bar2 : Nat → Nat → Nat → Foo

def silly (x : Foo) : Nat := by
  cases x
  case bar2 c d e => exact e
  case bar1 a b => exact b
```

The ``case`` tactic is clever, in that it will match the constructor to the appropriate goal. For example, we can fill the goals above in the opposite order:

```lean
inductive Foo where
  | bar1 : Nat → Nat → Foo
  | bar2 : Nat → Nat → Nat → Foo

def silly (x : Foo) : Nat := by
  cases x
  case bar1 a b => exact b
  case bar2 c d e => exact e
```

You can also use ``cases`` with an arbitrary expression. Assuming that
expression occurs in the goal, the cases tactic will generalize over
the expression, introduce the resulting universally quantified
variable, and case on that.

```lean
open Nat

example (p : Nat → Prop) (hz : p 0) (hs : ∀ n, p (succ n)) (m k : Nat)
        : p (m + 3 * k) := by
  cases m + 3 * k
  exact hz   -- goal is p 0
  apply hs   -- goal is a : ℕ ⊢ p (succ a)
```

Think of this as saying "split on cases as to whether ``m + 3 * k`` is
zero or the successor of some number." The result is functionally
equivalent to the following:

```lean
open Nat

example (p : Nat → Prop) (hz : p 0) (hs : ∀ n, p (succ n)) (m k : Nat)
        : p (m + 3 * k) := by
  generalize m + 3 * k = n
  cases n
  exact hz   -- goal is p 0
  apply hs   -- goal is a : ℕ ⊢ p (succ a)
```

Notice that the expression ``m + 3 * k`` is erased by ``generalize``; all
that matters is whether it is of the form ``0`` or ``succ a``. This
form of ``cases`` will *not* revert any hypotheses that also mention
the expression in the equation (in this case, ``m + 3 * k``). If such a
term appears in a hypothesis and you want to generalize over that as
well, you need to ``revert`` it explicitly.

If the expression you case on does not appear in the goal, the
``cases`` tactic uses ``have`` to put the type of the expression into
the context. 여기 예제가 있습니다.

```lean
example (p : Prop) (m n : Nat)
        (h₁ : m < n → p) (h₂ : m ≥ n → p) : p := by
  cases Nat.lt_or_ge m n
  case inl hlt => exact h₁ hlt
  case inr hge => exact h₂ hge
```

The theorem ``Nat.lt_or_ge m n`` says ``m < n ∨ m ≥ n``, and it is
natural to think of the proof above as splitting on these two
cases. In the first branch, we have the hypothesis ``h₁ : m < n``, and
in the second we have the hypothesis ``h₂ : m ≥ n``. The proof above
is functionally equivalent to the following:

```lean
example (p : Prop) (m n : Nat)
        (h₁ : m < n → p) (h₂ : m ≥ n → p) : p := by
  have h : m < n ∨ m ≥ n := Nat.lt_or_ge m n
  cases h
  case inl hlt => exact h₁ hlt
  case inr hge => exact h₂ hge
```

After the first two lines, we have ``h : m < n ∨ m ≥ n`` as a
hypothesis, and we simply do cases on that.

Here is another example, where we use the decidability of equality on
the natural numbers to split on the cases ``m = n`` and ``m ≠ n``.

```lean
#check Nat.sub_self

example (m n : Nat) : m - n = 0 ∨ m ≠ n := by
  cases Decidable.em (m = n) with
  | inl heq => rw [heq]; apply Or.inl; exact Nat.sub_self n
  | inr hne => apply Or.inr; exact hne
```

Remember that if you ``open Classical``, you can use the law of the
excluded middle for any proposition at all. But using type class
inference (see [Chapter Type Classes](./type_classes.md)), Lean can actually
find the relevant decision procedure, which means that you can use the
case split in a computable function.

Just as the ``cases`` tactic can be used to carry out proof by cases,
the ``induction`` tactic can be used to carry out proofs by
induction. The syntax is similar to that of ``cases``, except that the
argument can only be a term in the local context. 여기 예제가 있습니다.

```lean
# namespace Hidden
theorem zero_add (n : Nat) : 0 + n = n := by
  induction n with
  | zero => rfl
  | succ n ih => rw [Nat.add_succ, ih]
# end Hidden
```

As with ``cases``, we can use the ``case`` tactic instead of `with`.

```lean
# namespace Hidden
theorem zero_add (n : Nat) : 0 + n = n := by
  induction n
  case zero => rfl
  case succ n ih => rw [Nat.add_succ, ih]
# end Hidden
```

Here are some additional examples:

```lean
# namespace Hidden
open Nat

theorem zero_add (n : Nat) : 0 + n = n := by
  induction n <;> simp [*, add_zero, add_succ]

theorem succ_add (m n : Nat) : succ m + n = succ (m + n) := by
  induction n <;> simp [*, add_zero, add_succ]

theorem add_comm (m n : Nat) : m + n = n + m := by
  induction n <;> simp [*, add_zero, add_succ, succ_add, zero_add]

theorem add_assoc (m n k : Nat) : m + n + k = m + (n + k) := by
  induction k <;> simp [*, add_zero, add_succ]
# end Hidden
```

The `induction` tactic also supports user-defined induction principles with
multiple targets (aka major premises).


```lean
/-
theorem Nat.mod.inductionOn
      {motive : Nat → Nat → Sort u}
      (x y  : Nat)
      (ind  : ∀ x y, 0 < y ∧ y ≤ x → motive (x - y) y → motive x y)
      (base : ∀ x y, ¬(0 < y ∧ y ≤ x) → motive x y)
      : motive x y :=
-/

example (x : Nat) {y : Nat} (h : y > 0) : x % y < y := by
  induction x, y using Nat.mod.inductionOn with
  | ind x y h₁ ih =>
    rw [Nat.mod_eq_sub_mod h₁.2]
    exact ih h
  | base x y h₁ =>
     have : ¬ 0 < y ∨ ¬ y ≤ x := Iff.mp (Decidable.not_and_iff_or_not ..) h₁
     match this with
     | Or.inl h₁ => exact absurd h h₁
     | Or.inr h₁ =>
       have hgt : y > x := Nat.gt_of_not_le h₁
       rw [← Nat.mod_eq_of_lt hgt] at hgt
       assumption
```

You can use the `match` notation in tactics too:

```lean
example : p ∨ q → q ∨ p := by
  intro h
  match h with
  | Or.inl _  => apply Or.inr; assumption
  | Or.inr h2 => apply Or.inl; exact h2
```

As a convenience, pattern-matching has been integrated into tactics such as `intro` and `funext`.

```lean
example : s ∧ q ∧ r → p ∧ r → q ∧ p := by
  intro ⟨_, ⟨hq, _⟩⟩ ⟨hp, _⟩
  exact ⟨hq, hp⟩

example :
    (fun (x : Nat × Nat) (y : Nat × Nat) => x.1 + y.2)
    =
    (fun (x : Nat × Nat) (z : Nat × Nat) => z.2 + x.1) := by
  funext (a, b) (c, d)
  show a + d = d + a
  rw [Nat.add_comm]
```

We close this section with one last tactic that is designed to
facilitate working with inductive types, namely, the ``injection``
tactic. By design, the elements of an inductive type are freely
generated, which is to say, the constructors are injective and have
disjoint ranges. The ``injection`` tactic is designed to make use of
this fact:

```lean
open Nat

example (m n k : Nat) (h : succ (succ m) = succ (succ n))
        : n + k = m + k := by
  injection h with h'
  injection h' with h''
  rw [h'']
```

The first instance of the tactic adds ``h' : succ m = succ n`` to the
context, and the second adds ``h'' : m = n``.

The ``injection`` tactic also detects contradictions that arise when different constructors
are set equal to one another, and uses them to close the goal.

```lean
open Nat


example (m n : Nat) (h : succ m = 0) : n = n + 7 := by
  injection h

example (m n : Nat) (h : succ m = 0) : n = n + 7 := by
  contradiction

example (h : 7 = 4) : False := by
  contradiction
```

As the second example shows, the ``contradiction`` tactic also detects contradictions of this form.

Inductive Families
------------------

We are almost done describing the full range of inductive definitions
accepted by Lean. So far, you have seen that Lean allows you to
introduce inductive types with any number of recursive
constructors. In fact, a single inductive definition can introduce an
indexed *family* of inductive types, in a manner we now describe.

An inductive family is an indexed family of types defined by a
simultaneous induction of the following form:

```
inductive foo : ... → Sort u where
  | constructor₁ : ... → foo ...
  | constructor₂ : ... → foo ...
  ...
  | constructorₙ : ... → foo ...
```

In contrast to ordinary inductive definition, which constructs an
element of some ``Sort u``, the more general version constructs a
function ``... → Sort u``, where "``...``" denotes a sequence of
argument types, also known as *indices*. Each constructor then
constructs an element of some member of the family. One example is the
definition of ``Vector α n``, the type of vectors of elements of ``α``
of length ``n``:

```lean
# namespace Hidden
inductive Vector (α : Type u) : Nat → Type u where
  | nil  : Vector α 0
  | cons : α → {n : Nat} → Vector α n → Vector α (n+1)
# end Hidden
```

Notice that the ``cons`` constructor takes an element of
``Vector α n`` and returns an element of ``Vector α (n+1)``, thereby using an
element of one member of the family to build an element of another.

A more exotic example is given by the definition of the equality type in Lean:

```lean
# namespace Hidden
inductive Eq {α : Sort u} (a : α) : α → Prop where
  | refl {} : Eq a a
# end Hidden
```

For each fixed ``α : Sort u`` and ``a : α``, this definition
constructs a family of types ``Eq a x``, indexed by ``x : α``.
Notably, however, there is only one constructor, ``refl``, which
is an element of ``Eq a a``, and the curly braces after the
constructor tell Lean to make the argument to ``refl``
explicit. Intuitively, the only way to construct a proof of ``Eq a x``
is to use reflexivity, in the case where ``x`` is ``a``.
Note that ``Eq a a`` is the only inhabited type in the family of types
``Eq a x``. The elimination principle generated by Lean is as follows:

```lean
universe u v

#check (@Eq.rec : {α : Sort u} → {a : α} → {motive : (x : α) → a = x → Sort v}
                  → motive a rfl → {b : α} → (h : a = b) → motive b h)
```

It is a remarkable fact that all the basic axioms for equality follow
from the constructor, ``refl``, and the eliminator, ``Eq.rec``. The
definition of equality is atypical, however; see the discussion in the
next section.

The recursor ``Eq.rec`` is also used to define substitution:

```lean
# namespace Hidden
theorem subst {α : Type u} {a b : α} {p : α → Prop} (h₁ : Eq a b) (h₂ : p a) : p b :=
  Eq.rec (motive := fun x _ => p x) h₂ h₁
# end Hidden
```

You can also define `subst` using `match`.

```lean
# namespace Hidden
theorem subst {α : Type u} {a b : α} {p : α → Prop} (h₁ : Eq a b) (h₂ : p a) : p b :=
  match h₁ with
  | rfl => h₂
# end Hidden
```

Actually, Lean compiles the `match` expressions using a definition based on
`Eq.rec`.

```lean
# namespace Hidden
theorem subst {α : Type u} {a b : α} {p : α → Prop} (h₁ : Eq a b) (h₂ : p a) : p b :=
  match h₁ with
  | rfl => h₂

set_option pp.all true
#print subst
  -- ... subst.match_1 ...
#print subst.match_1
  -- ... Eq.casesOn ...
#print Eq.casesOn
  -- ... Eq.rec ...
# end Hidden
```

Using the recursor or `match` with ``h₁ : a = b``, we may assume ``a`` and ``b`` are the same,
in which case, ``p b`` and ``p a`` are the same.

It is not hard to prove that ``Eq`` is symmetric and transitive.
In the following example, we prove ``symm`` and leave as exercise the theorems ``trans`` and ``congr`` (congruence).

```lean
# namespace Hidden
theorem symm {α : Type u} {a b : α} (h : Eq a b) : Eq b a :=
  match h with
  | rfl => rfl

theorem trans {α : Type u} {a b c : α} (h₁ : Eq a b) (h₂ : Eq b c) : Eq a c :=
  sorry

theorem congr {α β : Type u} {a b : α} (f : α → β) (h : Eq a b) : Eq (f a) (f b) :=
  sorry
# end Hidden
```

In the type theory literature, there are further generalizations of
inductive definitions, for example, the principles of
*induction-recursion* and *induction-induction*. These are not
supported by Lean.

Axiomatic Details
-----------------

We have described inductive types and their syntax through
examples. This section provides additional information for those
interested in the axiomatic foundations.

We have seen that the constructor to an inductive type takes
*parameters* --- intuitively, the arguments that remain fixed
throughout the inductive construction --- and *indices*, the arguments
parameterizing the family of types that is simultaneously under
construction. Each constructor should have a type, where the
argument types are built up from previously defined types, the
parameter and index types, and the inductive family currently being
defined. The requirement is that if the latter is present at all, it
occurs only *strictly positively*. This means simply that any argument
to the constructor in which it occurs is a dependent arrow type in which the
inductive type under definition occurs only as the resulting type,
where the indices are given in terms of constants and previous
arguments.

Since an inductive type lives in ``Sort u`` for some ``u``, it is
reasonable to ask *which* universe levels ``u`` can be instantiated
to. Each constructor ``c`` in the definition of a family ``C`` of
inductive types is of the form

```
  c : (a : α) → (b : β[a]) → C a p[a,b]
```

where ``a`` is a sequence of data type parameters, ``b`` is the
sequence of arguments to the constructors, and ``p[a, b]`` are the
indices, which determine which element of the inductive family the
construction inhabits. (Note that this description is somewhat
misleading, in that the arguments to the constructor can appear in any
order as long as the dependencies make sense.) The constraints on the
universe level of ``C`` fall into two cases, depending on whether or
not the inductive type is specified to land in ``Prop`` (that is,
``Sort 0``).

Let us first consider the case where the inductive type is *not*
specified to land in ``Prop``. Then the universe level ``u`` is
constrained to satisfy the following:

> For each constructor ``c`` as above, and each ``βk[a]`` in the sequence ``β[a]``, if ``βk[a] : Sort v``, we have ``u`` ≥ ``v``.

In other words, the universe level ``u`` is required to be at least as
large as the universe level of each type that represents an argument
to a constructor.

When the inductive type is specified to land in ``Prop``, there are no
constraints on the universe levels of the constructor arguments. But
these universe levels do have a bearing on the elimination
rule. Generally speaking, for an inductive type in ``Prop``, the
motive of the elimination rule is required to be in ``Prop``.

There is an exception to this last rule: we are allowed to eliminate
from an inductively defined ``Prop`` to an arbitrary ``Sort`` when
there is only one constructor and each constructor argument is either
in ``Prop`` or an index. The intuition is that in this case the
elimination does not make use of any information that is not already
given by the mere fact that the type of argument is inhabited. This
special case is known as *singleton elimination*.

We have already seen singleton elimination at play in applications of
``Eq.rec``, the eliminator for the inductively defined equality
type. We can use an element ``h : Eq a b`` to cast an element
``t' : p a`` to ``p b`` even when ``p a`` and ``p b`` are arbitrary types,
because the cast does not produce new data; it only reinterprets the
data we already have. Singleton elimination is also used with
heterogeneous equality and well-founded recursion, which will be
discussed in a later chapter.


Mutual and Nested Inductive Types
---------------------------------

We now consider two generalizations of inductive types that are often
useful, which Lean supports by "compiling" them down to the more
primitive kinds of inductive types described above. In other words,
Lean parses the more general definitions, defines auxiliary inductive
types based on them, and then uses the auxiliary types to define the
ones we really want. Lean's equation compiler, described in the next
chapter, is needed to make use of these types
effectively. Nonetheless, it makes sense to describe the declarations
here, because they are straightforward variations on ordinary
inductive definitions.

First, Lean supports *mutually defined* inductive types. The idea is
that we can define two (or more) inductive types at the same time,
where each one refers to the other(s).

```lean
mutual
  inductive Even : Nat → Prop where
    | even_zero : Even 0
    | even_succ : (n : Nat) → Odd n → Even (n + 1)

  inductive Odd : Nat → Prop where
    | odd_succ : (n : Nat) → Even n → Odd (n + 1)
end
```

In this example, two types are defined simultaneously: a natural
number ``n`` is ``Even`` if it is ``0`` or one more than an ``Odd``
number, and ``Odd`` if it is one more than an ``Even`` number.
In the exercises below, you are asked to spell out the details.

A mutual inductive definition can also be used to define the notation
of a finite tree with nodes labelled by elements of ``α``:

```lean
mutual
    inductive Tree (α : Type u) where
      | node : α → TreeList α → Tree α

    inductive TreeList (α : Type u) where
      | nil  : TreeList α
      | cons : Tree α → TreeList α → TreeList α
end
```

With this definition, one can construct an element of ``Tree α`` by
giving an element of ``α`` together with a list of subtrees, possibly
empty. The list of subtrees is represented by the type ``TreeList α``,
which is defined to be either the empty list, ``nil``, or the
``cons`` of a tree and an element of ``TreeList α``.

This definition is inconvenient to work with, however. It would be
much nicer if the list of subtrees were given by the type
``List (Tree α)``, especially since Lean's library contains a number of functions
and theorems for working with lists. One can show that the type
``TreeList α`` is *isomorphic* to ``List (Tree α)``, but translating
results back and forth along this isomorphism is tedious.

In fact, Lean allows us to define the inductive type we really want:

```lean
inductive Tree (α : Type u) where
  | mk : α → List (Tree α) → Tree α
```

This is known as a *nested* inductive type. It falls outside the
strict specification of an inductive type given in the last section
because ``Tree`` does not occur strictly positively among the
arguments to ``mk``, but, rather, nested inside the ``List`` type
constructor. Lean then automatically builds the
isomorphism between ``TreeList α`` and ``List (Tree α)`` in its kernel,
and defines the constructors for ``Tree`` in terms of the isomorphism.

연습문제
---------

1. Try defining other operations on the natural numbers, such as
   multiplication, the predecessor function (with ``pred 0 = 0``),
   truncated subtraction (with ``n - m = 0`` when ``m`` is greater
   than or equal to ``n``), and exponentiation. Then try proving some
   of their basic properties, building on the theorems we have already
   proved.

   Since many of these are already defined in Lean's core library, you
   should work within a namespace named ``Hidden``, or something like
   that, in order to avoid name clashes.

2. Define some operations on lists, like a ``length`` function or the
   ``reverse`` function. Prove some properties, such as the following:

   a. ``length (s ++ t) = length s + length t``

   b. ``length (reverse t) = length t``

   c. ``reverse (reverse t) = t``

3. Define an inductive data type consisting of terms built up from the following constructors:

   - ``const n``, a constant denoting the natural number ``n``
   - ``var n``, a variable, numbered ``n``
   - ``plus s t``, denoting the sum of ``s`` and ``t``
   - ``times s t``, denoting the product of ``s`` and ``t``

   Recursively define a function that evaluates any such term with respect to an assignment of values to the variables.

4. Similarly, define the type of propositional formulas, as well as
   functions on the type of such formulas: an evaluation function,
   functions that measure the complexity of a formula, and a function
   that substitutes another formula for a given variable.
