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

이 예제는 이전의 것과 닮았습니다. 하지만 ``sum_example``의 입력이 이제 암시적으로 ``inl n``이나 ``inr n``의 꼴 둘 중의 하나입니다.
첫 번째 경우는 함수는 ``2 * n``을 반환하고 두 번째 경우는 ``2 * n + 1``을 반환합니다.

곱 유형은 생성자와 ``Prod``의 인수인 매개변수 ``α β : Type``에 의존하였음을 주목하세요. 린은 이 인수가 생성자의 나중 인수나 반환형으로부터 추론될 수 있을 때를 감지하고 그 경우 이들을 암시적이게 만듭니다.

이 섹션 다음에 우리는 유도형의 생성자가 자기 자신의 유도형으로부터 인수를 받을 때 무슨 일이 생기는지 알아볼 것입니다. 예제를 특징짓는 것은 이 섹션에서 우리는 이 경우만이 아니라 각 생성자가 이전에 명시된 유형에만 의존한다는 점입니다.

다수의 생성자가 있는 유형은 분리적임을 주목하세요. ``Sum α β``의 원소는 ``inl a``의 형태 *또는* ``inl b``의 형태입니다. 다수의 인수들이 있는 생성자는 결합적인 정보를 가져옵니다. ``Prod α β``의 원소  ``Prod.mk a b``으로부터 우리는 ``a``*그리고*``b``를 뽑아낼 수 있습니다. 임의의 유도형은 다수의 생성자를 갖거나 각각이 다수의 인수를 받게 함으로써 양쪽의 특징을 모두 포함할 수 있습니다.

함수 정의에서 처럼 린의 유도 정의 문법은 여러분이 이름붙은 인수를 콜론 앞에 생성자에 놓게 할 겁니다.

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

``yellow``의 정의는 제시한 세 값의 레코드를 형성합니다. 그리고 투영 ``Color.red``은 빨간색 성분을 반환합니다.

여러분은 각 필드 사이에 줄바꿈 문자를 추가하면 괄호를 생략할 수 있습니다.

```lean
structure Color where
  red : Nat
  green : Nat
  blue : Nat
  deriving Repr
```

``structure`` 명령은 대수적 구조를 정의하는데 특히 유용합니다. 그리고 린은 이들과 작업을 지원하는 중요한 기반구조를 제공합니다. 예를 들어 여기 반군(半群, semigroup)의 정의가 있습니다.

```lean
structure Semigroup where
  carrier : Type u
  mul : carrier → carrier → carrier
  mul_assoc : ∀ a b c, mul (mul a b) c = mul a (mul b c)
```

우리는 [구조체와 레코드 장](./structures_and_records.md)에서 더 많은 예제를 볼 것입니다.

우리는 이미 의존 곱 유형 `Sigma`에 대해 얘기했습니다.

```lean
# namespace Hidden
inductive Sigma {α : Type u} (β : α → Type v) where
  | mk : (a : α) → β a → Sigma β
# end Hidden
```

라이브러리에서 유도형의 둘 이상의 예제가 다음에 있습니다.

```lean
# namespace Hidden
inductive Option (α : Type u) where
  | none : Option α
  | some : α → Option α

inductive Inhabited (α : Type u) where
  | mk : α → Inhabited α
# end Hidden
```

의존 유형론의 의미론에서 부분 함수의 내장 개념은 없습니다. ``α → β``형 함수나 ``(a : α) → β``형 의존 함수의 모든 원소는 매 입력에 대한 함숫값을 갖는다고 가정됩니다. ``Option`` 형은 부분 함수를 표현하는 한 방법을 제공합니다. ``Option β``의 원소는 ``none``이거나 어떤 값 ``b : β``에 대한 ``some b``꼴 입니다. 따라서 우리는 ``α → Option β``형의 원소 ``f``를 모든 ``a : α``에 대한 ``α``에서 ``β``까지의 부분함수인 것으로 생각할 수 있습니다. ``f a`` ``f a``가 "정의되지 않음"을 가리키는 ``none``을 반환하거나 ``some b``을 반환합니다.

``Inhabited α``의 원소는 단지 ``α``의 원소가 있다는 사실에 대한 증인입니다. 나중에 우리는 ``Inhabited``가 린에서 *type class*의 예임을 보게 될 것입니다. 린은 적절한 기반형이 내장됨을 알게 되면 자동적으로 다른 생성된 유형도 그 기저에 내장되었음을 추론할 수 있습니다.

연습으로 우리는 여러분이 ``α``에서``β``까지 그리고 ``β`` to ``γ``까지 부분 함수에 대한 합성의 개념을 만들도록 권장합니다. 그리고 그것이 기대한 바처럼 행동하는 것을 보여주세요. 또 우리는 여러분이 ``Bool``과 ``Nat``이 내장되었음을 보이길 권장합니다. 즉, 두 내장된 유형의 곱과 내장된 유형으로의 함수의 유형이 내장되었음을 보이길 원합니다.

귀납적으로 정의된 명제
--------------------------------

귀납적으로 정의된 유형은 가장 바닥의 것인 ``Prop``을 포함하는 임의의 유형 세계에 살 수 있습니다. 사실 이것은 논리 결합자가 어떻게 정의되는가에 대한 것 입니다.

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

여러분은 이것이 어떻게 여러분이 이미 봐온 도입과 제거 규칙을 제공하는지에 대해 생각해봐야 합니다. 유도형의 제거자가 제거할 수 있는 것, 즉 유형의 어느 종류가 재귀자의 대상이 될 수 있는가를 다루는 규칙이 있습니다. 대략적으로 말하면, ``Prop``에서 유도형을 특징짓는 것은 ``Prop``의 다른 유형으로만 제거할 수 있습니다. 이것은 ``p : Prop``이면 원소 ``hp : p``는 아무 데이터도 나르지 않는다는 것의 이해와 일관됩니다. 그러나 이 규칙에 우리가 아래에서 논의할 작은 예외가 유도군의 섹션에 있습니다.

심지어 존재 한정기호도 유도적으로 정의됩니다.

```lean
# namespace Hidden
inductive Exists {α : Type u} (q : α → Prop) : Prop where
  | intro : ∀ (a : α), q a → Exists q
# end Hidden
```

``∃ x : α, p`` 기호는 ``Exists (fun x : α => p)``에 대한 문법적 설탕임을 기억하세요.

 ``False``, ``True``, ``And``그리고 ``Or``의 정의는 완전히 ``Empty``, ``Unit``,
``Prod``과 ``Sum``의 정의와 유사합니다. 차이점은 첫 번째 그룹은 ``Prop``의 원소를 얻고 두 번째 그룹은 어떤 ``u``에 대한 ``Type u`` 의 원소를 얻는다는 점입니다. 마찬가지로 ``∃ x : α, p``은 ``Σ x : α, p``의 ``Prop`` 값이 매겨진 변형입니다.

여기서 또 다른 유도형 ``∃ x : α, P``과 ``Σ x : α, P``이 섞인 ``{x : α // p}``으로 나타낸 유도형을 얘기하기 좋은 곳 같습니다.

```lean
# namespace Hidden
inductive Subtype {α : Type u} (p : α → Prop) where
  | mk : (x : α) → p x → Subtype p
# end Hidden
```

사실 린에서 ``Subtype``은 구조체 명령을 사용해 정의됩니다.

기호 ``{x : α // p x}``은 ``Subtype (fun x : α => p x)``에 대한 문법적 설탕입니다.
집합론에서 부분집합 표기 이후에 모델되었습니다.

자연수를 정의하기
----------------------------

우리가 지금까지 본 재귀적으로 정의된 유형은 "평평"합니다. 생성자는 데이터를 변형해서 유형에 그것을 삽입하고, 그에 대응하는 재귀자는 데이터를 풀고 그것에 작용합니다. 생성자가 정의될 바로 그 유형의 원소들에 작용할 때 훨씬 더 흥미롭게 될 것입니다. 표준 예제는 자연수의 ``Nat``유형입니다.

```lean
# namespace Hidden
inductive Nat where
  | zero : Nat
  | succ : Nat → Nat
# end Hidden
```

두 생성자가 있습니다. ``zero : Nat``으로 시작합니다. 이것은 아무 인수를 받지 않습니다. 그래서 우리는 시작부터 이것을 갖습니다. 반대로 생성자 ``succ``은 이전에 생성된 ``Nat``에만 적용될 수 있습니다. 이를 ``zero``에 적용하여``succ zero : Nat``을 얻습니다. 이를 다시 적용하여 ``succ (succ zero) : Nat``을 얻습니다. 그리고 계속됩니다. 직관적으로 ``Nat``은 이 생성자에서 "가장 작은" 유형입니다. ``zero``으로 시작하여 ``succ``를 반복적으로 적용함으로 남김없이 (그리고 자유롭게) 생성됨을 의미합니다.

전처럼 ``Nat``에 대한 재귀자는 의존함수 ``f``를 ``Nat``에서 임의의 영역으로 정의하도록 설계되었습니다. 즉,  어떤 ``motive : Nat → Sort u``에 대해 ``(n : nat) → motive n``의 원소가 ``f``입니다.
이것은 입력이 ``zero``인 경우와  입력이 어떤 ``n : Nat``에 대해 ``succ n`` 꼴인 입력에 대한 경우 두가지를 다뤄야 합니다. 첫 번째 경우에서 우리는 단순히 이전처럼 적절한 유형으로 대상 값을 명시할 수 있습니다. 그러나 두 번째 경우에서 재귀자는 ``n``에서 ``f``의 값이 이미 계산되었음을 가정합니다. 그 결과 재귀자에 대한 다음 인수는 ``n``과 ``f n``에 대해서 ``f (succ n)``에 대한 값을 명시합니다. 우리가 재귀자의 유형을 확인해보면

```lean
# namespace Hidden
# inductive Nat where
#  | zero : Nat
#  | succ : Nat → Nat
#check @Nat.rec
# end Hidden
```

여러분은 다음을 발견합니다.

```
  {motive : Nat → Sort u}
  → motive Nat.zero
  → ((n : Nat) → motive n → motive (Nat.succ n))
  → (t : Nat) → motive t
```

암시적 인수 ``motive``는 정의될 함수와 공동 영역입니다.
유형론에서 ``motive``가 제거/재귀에 대한 *motive*다 라고 흔히 말합니다. 왜냐하면 이는 우리가 생성하고자 하는 대산의 종류를 설명하기 때문입니다.
다음 두 인수는 위에서 설명한 0과 계승자에 대한 경우를 어떻게 계산하는지를 보여줍니다.
이들은 ``사소한 전제``라고도 알려져 있습니다.
마침내 ``t : Nat``가 함수에 대한 입력입니다. 이것은 ``주요 전제``로 알려져 있습니다.

`Nat.recOn`은 `Nat.rec`과 비슷하지만 주요 전제는 사소한 전제보다 먼저 일어납니다.

```
@Nat.recOn :
  {motive : Nat → Sort u}
  → (t : Nat)
  → motive Nat.zero
  → ((n : Nat) → motive n → motive (Nat.succ n))
  → motive t
```

예를 들어 자연수에 대한 추가 함수 ``add m n``을 고려해보세요. ``m``을 고치면 우리는 ``n``에 대한 재귀로부터 덧셈을 정의할 수 있습니다. 기저의 경우에서 우리는 ``add m zero``를 ``m``으로 설정합니다. 계승자 단계에서 우리는 ``add m (succ n)``이 ``add m (succ n)``이 되도록 정의하여 값 ``add m n``의 추정은 이미 결정되었습니다.

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

``Nat`` 이름공간에 그런 정의를 넣는 것은 유용합니다. 그럼 그 이름공간에 친숙한 기호를 정의해 나갈 수 있습니다. 덧셈에 대해 정의한 두 방정식은 이제 정의상으로 성립합니다.

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

[유형 클래스 장](./type_classes.md)에서 ``instance`` 명령이 어떻게 동작하는지 설명할 것입니다. 아래 예제에서 우리는 이후부터 자연수의 린 버전을 사용할 것입니다.

하지만 ``zero + m = m``같은 사실을 증명하는 것은 귀납에 의한 증명이 요구됩니다.
위에서 봤듯이 공동역역 ``motive n``이 ``Prop``의 원소일 때 귀납 원리는 재귀 원리의 특별한 경우일 뿐입니다. 이는 귀납적 적의의 유사한 패턴을 보여줍니다. ``∀ n, motive n``을 증명하기 위해 우선 ``motive 0``을 증명하고 그 뒤 임의의 ``n``에 대해 ``ih : motive n``을 가정하고 ``motive (succ n)``를 증명합니다.

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

다시 한 번 ``Nat.recOn``은 증명의 맥락에서 사용됨을 주목하세요. 이는 정말로 귀납 원리가 위장한 것입니다. ``rewrite``와 ``simp`` 전략은 이 같은 증명에서 아주 효과적인 경향이 있습니다. 여기서 각각은 증명을 다음과 같이 간단히 하는데 사용됩니다.

```lean
# namespace Hidden
open Nat

theorem zero_add (n : Nat) : 0 + n = n :=
  Nat.recOn (motive := fun x => 0 + x = x) n
    rfl
    (fun n ih => by simp [add_succ, ih])
# end Hidden
```

다른 예제에서 덧셈의 결합성 ``∀ m n k, m + n + k = m + (n + k)``을 증명해 봅시다.
(``+`` 기호는 우리가 정의했다시피 왼쪽으로 결합됩니다. 그래서 ``m + n + k``은 사실 ``(m + n) + k``입니다.) 가장 어려운 부분은 어떤 변수에 귀납을 적용할 것인지 알아내는 것 입니다. 덧셈은 두 번째 인수에 대해 재귀적으로 정의되어 있기 때문에 ``k``는 좋은 추측입니다. 그리고 한번 우리가 그 선택을 하면 증명은 거의 술술 써집니다.

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

다시한번 여러분은 증명을 다음과 같이 줄일 수 있습니다.

```lean
open Nat
theorem add_assoc (m n k : Nat) : m + n + k = m + (n + k) :=
  Nat.recOn (motive := fun k => m + n + k = m + (n + k)) k
    rfl
    (fun k ih => by simp [Nat.add_succ, ih]; done)
```

우리가 덧셈에 교환성을 증명하려고 한다 가정합시다. 두 번째 인수에 귀납을 선택하는 것으로 우리는 다음과 같이 시작할 수 있습니다.

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

이 시점에서 우리는 또다른 지지하는 사실 ``succ (n + m) = succ n + m``이 필요함을 알게 됩니다.
여러분은 이것을 ``m``에 대한 귀납으로 증명할 수 있습니다.

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

그럼 여러분은 이전 증명에서 ``sorry``를 ``succ_add``으로 대체할 수 있습니다. 그러나 다시 이 증명은 간단히 될 수 있습니다.

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

다른 재귀적인 데이터 유형
--------------------------

재귀적으로 정의된 유형에 대해 몇 가지 예제를 더 고려해봅시다. 임의의 유형 ``α``에 대한 ``α`` 원소의 리스트 ``List α``형은 라이브러리에 정의됩니다.

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

``α``형 원소의 리스트는 빈 리스트 ``nil``이거나 리스트 ``t : List α``의 다음의 원소 ``h : α``입니다.
첫 원소 ``h``는 흔히 리스트의 "헤드"로 알려져 있고 나머지 ``t``는 "테일"이라고 알려져 있습니다.

연습으로 다음을 증명하세요.

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

리스트의 길이를 반환하는  함수 ``length : {α : Type u} → List α → Nat``도 정의해 보세요. 그리고 이것 예상대로 동작하는지 증명하세요. (예를 들어 ``length (append as bs) = length as + length bs``)

또 다른 예제로 우리는 이진 트리의 유형을 정의할 수 있습니다.

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

귀납형에 대한 전략
---------------------------

린의 귀납형의 근본적인 중요성이 제시되었을 때 이들과 효과적으로 동작하도록 설계된 다수의 전략이 있는 것은 놀라운 일이 아닙니다. 여기서 우리는 이들 중 몇 가지를 설명합니다.

``cases`` 전략은 재귀적으로 정의된 유형의 원소와 이름이 제안하는 것에 작용합니다. 이것은 가능한 생성자들의 각각에 따라 원소를 분리한다. 그것의 가장 기본 형태에서 이것은 지역 맥락에서 원소 ``x``에 적용됩니다. 그 뒤 이것은 목표를 ``x``는 생성자의 각각으로 대체되는 경우로 바꿉니다.

```lean
example (p : Nat → Prop) (hz : p 0) (hs : ∀ n, p (Nat.succ n)) : ∀ n, p n := by
  intro n
  cases n
  . exact hz  -- goal is p 0
  . apply hs  -- goal is a : ℕ ⊢ p (succ a)
```

여기 여분의 종과 호루라기가 있습니다. 한 가지에 대해, ``cases``는 여러분이 ``with`` 절을 사용하여 각 대안에 대한 이름을 선택할 수 있도록 허용합니다.  다음 예제에서 예를들어 우리는 이름``m``을 ``succ``에 대한 인수로 선택하여 두 번쨰 경우가 ``succ m``을 참조하도록 합니다. 더 중요하게 cases 전략은 대상 변수에 의존하는 지역 상황 속 임의의 항목을 감지할 수 있습니다. 이것은 이 원소를 되돌리고, 나누기를 하고, 그들을 다시 도입합니다. 아래 예제에서 가정 ``h : n ≠ 0``이  첫 분기에서 ``h : 0 ≠ 0``이 되고 두 번째 분기에서 ``h : succ m ≠ 0``이 됨을 주목하세요.

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

``cases``는 데이터를 만드는 것만 아니라 명제를 증명하는 데에도 사용될 수 있음을 주목하세요.

```lean
def f (n : Nat) : Nat := by
  cases n; exact 3; exact 7

example : f 0 = 3 := rfl
example : f 5 = 7 := rfl
```

다시 한번, cases는 맥락의 종속물들을 되돌리고, 나누고, 재도입합니다.

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

인자를 갖는 다수의 생성자 있는 예제가 있습니다.

```lean
inductive Foo where
  | bar1 : Nat → Nat → Foo
  | bar2 : Nat → Nat → Nat → Foo

def silly (x : Foo) : Nat := by
  cases x with
  | bar1 a b => exact b
  | bar2 c d e => exact e
```

각 생성자에 대한 대안은 성성자가 선언된 순서대로 풀려야 할 필요는 없습니다.

```lean
inductive Foo where
  | bar1 : Nat → Nat → Foo
  | bar2 : Nat → Nat → Nat → Foo

def silly (x : Foo) : Nat := by
  cases x with
  | bar2 c d e => exact e
  | bar1 a b => exact b
```

``with``의 문법은 구조화된 증명을 작성하는데 편리합니다.
린은 여러분이 목표에 변수 이름을 할당할 수 있게 하는 보완적인 ``case`` 전략도 제공합니다.

```lean
inductive Foo where
  | bar1 : Nat → Nat → Foo
  | bar2 : Nat → Nat → Nat → Foo

def silly (x : Foo) : Nat := by
  cases x
  case bar2 c d e => exact e
  case bar1 a b => exact b
```

 ``case`` 전략은 적절한 목표에 대한 생성자를 짝지어준다는 점에서 영리합니다. 예를 들어 우리는 위의 목표를 반대 순서로 채울 수 있습니다.

```lean
inductive Foo where
  | bar1 : Nat → Nat → Foo
  | bar2 : Nat → Nat → Nat → Foo

def silly (x : Foo) : Nat := by
  cases x
  case bar1 a b => exact b
  case bar2 c d e => exact e
```

여러분은 임의의 표현식에 ``cases``를 사용할 수도 있습니다. 표현식이 목표에서 나타남을 가정하면, cases 전략은 표현식을 일반화하고 결과적으로 보편적으로 정량화된 변수를 도입하고 이에 대한 경우를 나눕니다.

```lean
open Nat

example (p : Nat → Prop) (hz : p 0) (hs : ∀ n, p (succ n)) (m k : Nat)
        : p (m + 3 * k) := by
  cases m + 3 * k
  exact hz   -- goal is p 0
  apply hs   -- goal is a : ℕ ⊢ p (succ a)
```

이것을 "``m + 3 * k``이 0이거나 어떤 수의 계승자인지로 경우가 나뉜다"고 생각합시다. 이 결과는 다음과 기능적으로 동등합니다.

```lean
open Nat

example (p : Nat → Prop) (hz : p 0) (hs : ∀ n, p (succ n)) (m k : Nat)
        : p (m + 3 * k) := by
  generalize m + 3 * k = n
  cases n
  exact hz   -- goal is p 0
  apply hs   -- goal is a : ℕ ⊢ p (succ a)
```

표현식 ``m + 3 * k``은 ``generalize``에 의해 지워짐을 보세요. 중요한 것은 ``0`` 혹은 ``succ a``의 형태인지 아닌지 입니다. 이 ``cases``의 형태는 방정식(이 경우 ``m + 3 * k``)에서 표현식을 언급한 적 있는 어떤 가정도 되돌리지 *않을* 것입니다. 만약 그런 항이 가정에 나타나고 여러분이 그것에 대해서도 일반화하기 원한다다면 여러분은 그것을 명시적으로 ``revert`` 할 필요가 있습니다.

여러분이 경우를 나누려는 표현식이 목표에 나타나지 않는다면 ``cases`` 전략은 맥락에 표현식의 유형을 넣도록``have`` 를 사용합니다. 여기 예제가 있습니다.

```lean
example (p : Prop) (m n : Nat)
        (h₁ : m < n → p) (h₂ : m ≥ n → p) : p := by
  cases Nat.lt_or_ge m n
  case inl hlt => exact h₁ hlt
  case inr hge => exact h₂ hge
```

정리 ``Nat.lt_or_ge m n``은 ``m < n ∨ m ≥ n``을 말합니다. 그리고 이것은 이들 두 경우를 나눔으로써 위의 증명이 당연하다고 생각합니다. 첫 분기에서 우리는 가정 ``h₁ : m < n``을 갖고 두 번째에서 우리는 가정 ``h₂ : m ≥ n``을 갖습니다. 위의 증명은 다음과 기능적으로 동등합니다.

```lean
example (p : Prop) (m n : Nat)
        (h₁ : m < n → p) (h₂ : m ≥ n → p) : p := by
  have h : m < n ∨ m ≥ n := Nat.lt_or_ge m n
  cases h
  case inl hlt => exact h₁ hlt
  case inr hge => exact h₂ hge
```

첫 두 줄 이후에 우리는 ``h : m < n ∨ m ≥ n``을 가정으로 갖습니다. 그리고 우리는 단순히 이에 대해 경우를 나눕니다.

여기 또 다른 예제가 있습니다. 우리는 ``m = n``과 ``m ≠ n``으로 나누도록  자연수에 대한 동등성의 결정가능성을 사용합니다.

```lean
#check Nat.sub_self

example (m n : Nat) : m - n = 0 ∨ m ≠ n := by
  cases Decidable.em (m = n) with
  | inl heq => rw [heq]; apply Or.inl; exact Nat.sub_self n
  | inr hne => apply Or.inr; exact hne
```

여러분이 ``open Classical``을 하면 여러분은 임의의 명제에 대해서 배중률을 사용할 수 있음을 기억하세요. 그러나 유형 클래스 추론을 사용하여 ([유형 클래스 장](./type_classes.md) 참조), 린이 실제로 연관된 결정 절차를 찾을 수 있다. 이 말은 여러분이 셀 수 있는 함수에 대해 경우를 나누는 것이 가능하다는 의미이다.

``cases`` 전략은 경우에 따른 증명을 수행하는데 사용될 수 있다. ``induction`` 전략은 귀납으로 증명을 수행하는데 사용될 수 있다. 인수가 지역 상황에 대한 것이라는 점을 제외하고 문법은 ``cases``의 것과 비슷합니다. 여기 예제가 있습니다.

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

여기 추가 예제가 있습니다.

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

`induction` 전략은 (주요 전제라고도 하는) 다수의 타겟을 갖는 사용자 정의 귀납 원리도 지원합니다.


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

여러분은 전략에서 `match` 기호도 사용할 수 있습니다.

```lean
example : p ∨ q → q ∨ p := by
  intro h
  match h with
  | Or.inl _  => apply Or.inr; assumption
  | Or.inr h2 => apply Or.inl; exact h2
```

편리하기에 패턴 매칭은 `intro`와 `funext` 같은 전략에 합쳐졌습니다.

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

 귀납형과 동작하는 걸 가능하도록 설계된 즉, ``injection`` 전략으로 우리는 이 장을 이 마지막을 마칩니다. 설계하면서 유도형의 원소는 자유롭게 생성됩니다. 그말은 생성자는 주입적이고 분리된 범위를 갖습니다. ``injection`` 전략은 이 사실을 사용하도록 설계되었습니다.

```lean
open Nat

example (m n k : Nat) (h : succ (succ m) = succ (succ n))
        : n + k = m + k := by
  injection h with h'
  injection h' with h''
  rw [h'']
```

전략의 첫번째 개체는 ``h' : succ m = succ n``을 맥락에 추가합니다. 그리고 두번째 개체 ``h'' : m = n``을 추가합니다.

``injection`` 전략은 서로 다른 생성자들이 서로 같도록 설정되었을 때 일어나는 모순을 감지하고 이들로 목표를 종료하는데 사용합니다.

```lean
open Nat


example (m n : Nat) (h : succ m = 0) : n = n + 7 := by
  injection h

example (m n : Nat) (h : succ m = 0) : n = n + 7 := by
  contradiction

example (h : 7 = 4) : False := by
  contradiction
```

두 번째 예제가 보여주다시피 ``contradiction`` 전략도 이 형태의 모순을 감지합니다.

유도군
------------------

우리는 거의 린이 허용하는 귀납 정의의 대부분을 설명했습니다. 지금까지 여러분은 린이 여러분에게 재귀적인 생성자에 대한 임의의 수로 유도형을 도입하게 해줌을 보았습니다. 사실 단일 재귀적 정의는 이제 우리가 설명할 방식으로 유도형의 색인된 *family*를 도입할 수 있습니다.

유도군은 다음 형태를 따르는 동시 재귀로 정의되는 유형의 색인된 군입니다.

```
inductive foo : ... → Sort u where
  | constructor₁ : ... → foo ...
  | constructor₂ : ... → foo ...
  ...
  | constructorₙ : ... → foo ...
```

어떤 ``Sort u``의 원소를 생성하는 평범한 재귀적 정의와는 반대로 더 일반적인 형태는 함수 ``... → Sort u``을 생성합니다. 한편, "``...``"은 *indices*로도 알려진 인수 유형의 나열을 의미합니다. 그럼 각 생성자는 군의 일부 구성원의 원소를 생성합니다. 한 예제는 길이 ``n``의  ``α``를 원소로 하는 벡터 유형 ``Vector α n``의 정의입니다.

```lean
# namespace Hidden
inductive Vector (α : Type u) : Nat → Type u where
  | nil  : Vector α 0
  | cons : α → {n : Nat} → Vector α n → Vector α (n+1)
# end Hidden
```

``cons`` 생성자는 ``Vector α n``의 원소를 받고 ``Vector α (n+1)``의 원소를 반환합니다. 그러므로 군의 한 구성원의 원소를 다른 원소를 만드는데 사용합니다.

더 특이한 예제는 린의 동등성 유형의 정의에 의해 제시됩니다.

```lean
# namespace Hidden
inductive Eq {α : Sort u} (a : α) : α → Prop where
  | refl {} : Eq a a
# end Hidden
```

각 고정된  ``α : Sort u``와 ``a : α``에 대해 이 정의는 ``x : α``으로 색인된 ``Eq a x``형의 군을 생성합니다.
하지만 주목할 점은 오직 ``Eq a a``의 원소인 한 생성자 ``refl``있습니다. 그리고 생성자 뒤의 중괄호는 린에게 ``refl``을 명시적인 인수로 만들게 합니다. 직관적으로 ``Eq a x``의 증명을 생성하는 유일한 방법은 ``x``가 ``a``인 경우 반사성을 사용하는 것입니다.
``Eq a a``는 ``Eq a x``형의 군에서 유일한 내장 유형임을 주목하세요. 린에 의해 생성된 제거 원리는 다음과 같습니다.

```lean
universe u v

#check (@Eq.rec : {α : Sort u} → {a : α} → {motive : (x : α) → a = x → Sort v}
                  → motive a rfl → {b : α} → (h : a = b) → motive b h)
```

동등성에 대한 모든 기본 공리는 생성자 ``refl``과 제거자 ``Eq.rec``로부터 따라 나온다는 사실은 주목할만 합니다. 하지만 동등성의 정의는 전형적이지 않습니다. 다음 섹션의 논의를 보세요.

재귀자 ``Eq.rec``도 대입을 정의하는데 사용됩니다.

```lean
# namespace Hidden
theorem subst {α : Type u} {a b : α} {p : α → Prop} (h₁ : Eq a b) (h₂ : p a) : p b :=
  Eq.rec (motive := fun x _ => p x) h₂ h₁
# end Hidden
```

여러분도 `match`을 사용해 `subst`을 정의할 수 있습니다.

```lean
# namespace Hidden
theorem subst {α : Type u} {a b : α} {p : α → Prop} (h₁ : Eq a b) (h₂ : p a) : p b :=
  match h₁ with
  | rfl => h₂
# end Hidden
```

실제로, 린은 `match` 표현식을 `Eq.rec`에 기반한 정의를 사용해 컴파일합니다.

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

재귀자나 `match`를 ``h₁ : a = b``과 사용하면, 우리는 ``a``와 ``b``가 같다고 가정할 수 있습니다. 그 경우 ``p b``와 ``p a``는 동일합니다.

``Eq``가 대칭적이고 추이적임을 증명하는 것은 어렵지 않습니다.
다음 예제에서 우리는``symm``을 증명합니다. 그리고 정리 ``trans``과 ``congr`` (적합, congruence)을 연습으로 남겨놓겠습니다.

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

유형론 교재에서는 재귀적 정의의 더 일반화 예를 들어 *induction-recursion*과 *induction-induction*의 원리가 있습니다. 이것들은 린에서 지원되지 않습니다.

공리적 세부사항
-----------------

우리는 유도형과 그들의 문법을 예제를 통해 설명했습니다. 이 섹션은 공리적 기초에 대해 흥미로워하는 이들을 위한 추가 정보를 제공합니다.

우리는 유도형에서 생성자는 *매개변수(parameters)*-- 직관적으로 재귀 생성 동안 고정된 상태로 남는 인수 --와 동시에 생성중인 유형의 군을 매개변수화하는 인수 *indices*를 받는 것을 보았습니다.   각 생성자는 이전에 정의된 유형, 매개변수와 색인 유형, 현재 정의 중인 유도군으로 만들어져서 유형을 가져야만 합니다. 요구사항은 만약 후자가 전부 나타났다면 이것은 *엄격하게 긍정적으로*만 일어납니다. 이 의미는 단순히 그것이 발생하는 생성자에서 임의의 인자가 유도형이 정의 하에서 결과적인 유형으로써만 일어나는 의존 화살표 유형임을 의미합니다. 여기서 색인은 상수와 이전의 인수에 대해서 제시됩니다.

유도형이 어떤 ``u``에 대해 ``Sort u``에 속해 있기 때문에, *어느*세계의 수준에 ``u``가 개체화 될 수 있는지 묻는 것은 합리적입니다. 유도형의 ``C`` 군의 정의에서 각 생성자 ``c``는 다음 형태와 같습니다.

```
  c : (a : α) → (b : β[a]) → C a p[a,b]
```

여기서 ``a``는 데이터 유형 매개변수의 나열이고 ``b``는 생성자에 대한 인수의 나열이고 ``p[a, b]`` 는 유도군의 어떤 원소가 생성자를 어디에 머무르게 할지 결정하는  색인입니다. (그들의 의존성이 성립되는 한 인자가 생성자에 임의의 순서로 나타날 수 있다는 점에서 이 설명은 약간 오해로 이끌 수 있습니다.) ``C``의 세계 수준에서 유도형이 ``Prop`` (즉, ``Sort 0``)에 머무른다고 나타나져 있는지 아닌지에 따라 제약은 두 경우로 나누어 떨어집니다.

우선 유도형이 ``Prop``에 머무른다고 명시되지*않은*경우를 생각해봅시다. 그러면 세계 수준 ``u``는 다음을 만족하도록 제한됩니다.

> 위처럼 각 생성자 ``c``와 ``β[a]``열에서 각 ``βk[a]``에 대해 만약 ``βk[a] : Sort v``이면 ``u`` ≥ ``v``이다.

다시 말하면,  세계 수준 ``u``는 적어도 생성자에 대한 인자로 나타난 각 유형의 세계 수준 만큼이나 클 필요가 있음을 요구합니다.

유도형이 ``Prop``에서 머무른다고 명시되어 있을 때, 생성자 인수의 세계 수준에 대한 제한이 없습니다. 그러나 이 세계 수준은 제거 규칙으로부터 영향을 받습니다. 쉽게 말하자면 ``Prop``에 대한 유도형에 대해 제거 규칙의 동기는 ``Prop``에 있어야 함을 요구합니다.

이 마지막 규칙에 예외가 있습니다. 우리는 재귀적으로 정의된 ``Prop``에서 임의의 ``Sort``이르기까지 오직 한 생성자와 각 생성자 인수가 ``Prop``에 있거나 한 색인으로 있을 때 제거할 수 있습니다. 이 경우에 대한 직관적인 설명은 제거가 단순히 인수 유형이 존재한다는 사실에 의해 이미 제공되는 정보를 쓰지 않는다는 것입니다. 이 특별한 경우는 *한번에 한 제거(singleton elimination)*로도 알려져 있습니다.

우리는 재귀적으로 정의된 동등 유형에 대한 제거자인``Eq.rec``의 활용에서 한번에 하나씩 제거되는 것을 보았습니다. 우리는 원소 ``h : Eq a b``를 심지어 ``p a``과 ``p b``가 임의의 유형일 때에도 원소 ``t' : p a``에서 ``p b``로 변환하는데 사용할 수 있습니다. 왜냐하면 변환은 새로운 데이터를 만들지 않고 이미 가진 데이터를 재해석하기만 하기 때문입니다. 한 번에 하나씩 제거는 동일하지 않은 동등석과 잘 세워진 제귀에도 사용됩니다. 이것은 이후에 논의할 예정입니다.


상호적이고 중첩된 유도형
---------------------------------

이제 우리는 유도형의 종종 유용한 두 가지 일반화를 고려했습니다. 린은 이들을 위에서 설명한 유도형의 더 기초적인 종류로 "컴파일"해나감으로써 지원합니다. 다시 말하면, 린은 더 일반적인 정의를 구문분석해 이들이 기반하는 부가적인 유도형을 정의하고, 그 뒤 부가적인 유형을 우리가 원하는 것을 정의하는데 사용합니다. 다음 장에서 설명할 린의 방정식 컴파일러는 이 유형의 사용을 효과적으로 만들기 위해 필요합니다. 그래도 여전히 여기에 선언을 설명하는 것이 이치에 맞는 것 같습니다.왜냐하면 그들은 평범한 재귀적 정의에 직관적인 변형이기 때문입니다.

우선 린은 유도형의 *상호적으로 정의됨(mutually defined)*을 지원합니다. 아이디어는 각각이 서로 다른 이들을 참조하면서 우리가 둘(혹은 그 이상의) 유도형을 동시에 정의할 수 있다는 것입니다.

```lean
mutual
  inductive Even : Nat → Prop where
    | even_zero : Even 0
    | even_succ : (n : Nat) → Odd n → Even (n + 1)

  inductive Odd : Nat → Prop where
    | odd_succ : (n : Nat) → Even n → Odd (n + 1)
end
```

이 예제에서 두 유형은 동시에 정의되었습니다.. 자연수 ``n``은 만약 이것이 ``0`` 혹은 ``홀수(Odd)``보다 하나 크면``짝수(Even)``입니다. 그리고 ``홀수(Odd)``는 ``짝수(Even)``보다 하나 큰 것입니다.
아래 연습에서 여러분은 세부 사항을 말하도록 요청받습니다.

상호적 재귀 정의는 노드가 ``α``의 원소로 색인된 유한 트리의 기호를 정의하는데도 사용될 수 있습니다.

```lean
mutual
    inductive Tree (α : Type u) where
      | node : α → TreeList α → Tree α

    inductive TreeList (α : Type u) where
      | nil  : TreeList α
      | cons : Tree α → TreeList α → TreeList α
end
```

이 정의를 갖고 대게는 빈 하위 트리의 리스트와 ``α``의 원소를 줌으로써 ``Tree α``의 원소를 생성할 수 있습니다. 하위 트리의 리스트는 ``TreeList α``형으로 표현됩니다. 이것은 빈 리스트 ``nil``이거나 트리의 ``cons``과 ``TreeList α``의 원소로 정의될 수 있습니다.

이그러나  정의는 작업하기에 불편합니다. 만약 하위트리의 리스트가 ``List (Tree α)``형으로 제시된다면 훨씬 더 좋을 것입니다. 왜냐하면 특이 린의 라이브러리가 리스트와 작업할 수 있는 다수의 함수와 정리를 담고 있기 때문입니다. 어떤 이는 ``TreeList α``형이 ``List (Tree α)``과 *i동형(somorphic)*임을 보일 수 있습니다. 그러나 이 동형을 따라 결과를 앞뒤로 번역하는 것은 번거롭습니다.

사실 린은 우리가 원하는 유도형을 정의하도록 해줍니다.

```lean
inductive Tree (α : Type u) where
  | mk : α → List (Tree α) → Tree α
```

이것은 *중첩된(nested)* 유도형으로 알려져 있습니다. 이것은 마지막 섹션에서 제시된 유도형의 엄격한 명세를 바깥으로 빠져나옵니다. 왜냐하면 ``Tree``는 ``mk``에 대한 인수 사이에서 엄격하게 긍정적으로 일어나지 않고 대신  ``List``형 생성자의 중첩된 안쪽에서 일어나기 때문입니다. 그 후 린은 자동적으로 그것의 커널에서 ``TreeList α``과``List (Tree α)`` 사이의 동형을 만듭니다. 그리고 동형에 대해서 ``Tree``에 대한 생성자를 정의합니다.

연습문제
---------

1. 자연수에 대해 곱셈, 선행자 함수 (``pred 0 = 0``으로), 절단된 뺄셈( ``m`` 이  ``n``)보다 크거나 같을 때 ``n - m = 0``으로)와 거듭제곱 같은 다른 연산을 정의해보세요. 그 뒤 그들의 기본 성질 몇 가지를 증명해보세요. 우리가 이미 증명한 정리를 세워보세요.

   이미 이들 중 다수가 이미 린의 중앙 라이브러리에 정의되어 있기에 여러분은 ``Hidden`` 혹은 이름 충돌을 피할 수 있는 것으로 이름지은 이름공간에서 작업해야만 합니다.

2. 리스트에 대한 ``length``함수나 ``reverse`` 함수같은 몇 가지 연산을 정의하세요. 다음과 같은 몇 가지 성질을 증명하세요.

   a. ``length (s ++ t) = length s + length t``

   b. ``length (reverse t) = length t``

   c. ``reverse (reverse t) = t``

3. 다음 생성자로부터 세워진 항으로 구성된 유도 데이터 형을 정의하세요.

   - ``const n``, a constant denoting the natural number ``n``
   - ``var n``, a variable, numbered ``n``
   - ``plus s t``, denoting the sum of ``s`` and ``t``
   - ``times s t``, denoting the product of ``s`` and ``t``

   변수에 값을 할당한 것에 대한 항으로 계산하는 재귀적으로 함수를 정의하세요.

4. 비슷하게 계산 함수와 공식의 복잡도를 측정하는 함수 및 제시한 변수로 다른 식에 대입하는 함수와 마찬가지인 명제 논리식의 유형을 정의하세요.
