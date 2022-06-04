한정기호와 동등성
========================

지난 장에서 여러분에게 명제적 연결사를 포함한 문장의 증명을 구성하는 방법을 소개했습니다. 이번 장에서는 우리는 전칭과 존재 한정기호와 동등 관계를 포함한 논리 구축 레퍼토리를 확장합니다.

전칭 한정기호
------------------------

``α`` 가 임의의 유형인지를 보세요, 우리는 ``α``에 대해 단항 술어 p를  ``α → Prop``형의 대상으로 나타낼 수 있습니다. 이 경우 ``x : α``가 주어진다면, ``p x``는  ``p``가  ``x``가 성립한다는 주장을 지칭합니다. 마찬가지로 대상 ``r : α → α → Prop``은 ``α``에 대한 이항 관계 즉, ``x y : α``이 주어진다면 , ``r x y``은 ``x``가 ``y``에 연관된다는 주장을 지칭합니다.

전칭 한정기호 ``∀ x : α, p x`` 은 "모든 ``x : α``에 대해  ``p x``"가 성립한다는 주장을 가리켜야 할 것입니다. 명제적 연결사와 마찬가지로 자연 연역에서 "모든"은  도입과 제거 규칙에 지배받습니다. 비공식적으로 도입 규칙은 다음과 같이 말합니다.

> 임의의 ``x : α``의 상황에서 ``p x``의 증명이 주여졌다고 하자, 그러면 우리는 증명 ``∀ x : α, p x``을 얻는다.

제거 규칙은 이와 같이 말합니다.

> 증명 ``∀ x : α, p x``과 임의의 항 ``t : α``이 있다고 하자, 그러면 우리는 ``p t``의 증명을 얻습니다.

함의의 경우 때와 같이 유형으로써 명제 해석은 이제 제 역할을 하기 시작했습니다. 의존 화살표 유형에 대한 도입과 소거 규칙을 기억하세요.

>  ``β x``형의 항 ``t`` 임의의 ``x : α``에 대해서 주어졌다고 해봅시다. 그러면 우리는 ``(fun x : α => t) : (x : α) → β x``을 갖습니다.

제거 규칙은 이와 같이 말합니다.

> 항 ``s : (x : α) → β x``과 임의의 항 ``t : α``이 주어졌다고 해봅시다. 그러면 우리는 ``s t : β t``을 가집니다.

``p x``는 ``Prop``형을 갖는 이 경우에 대해, 우리가  ``(x : α) → β x``을 ``∀ x : α, p x``으로 대체한다면, 우리는 이것들을 전칭 한정기호를 포함한 증명을 만드는데 옳바른 규칙이라고 읽을 수 있습니다.

그러므로 직관주의 계산법은 의존 화살표 유형을 이처럼 모든-표현식으로 바라봅니다. 만약 ``p``가 임의의 표현식이면, ``∀ x : α, p``은 그저 ``(x : α) → p``에 대한 대체 표현일 뿐입니다. 전자의 생각은  ``p``가 명제인 후자의 경우보다 자연스럽습니다. 일반적으로 표현식 ``p``는 ``x : α``에 의존할 것입니다. 평범한 함수공간의 경우에 대해 우리는 ``α → β``을 ``(x : α) → β``의 특별한 경우로 해석할 수 있음을 생각해보세요. 이때  ``β``는 ``x``에 의존하지 않습니다. 마찬가지로 우리는 명제들 사이의 함의 ``p → q``를 ``∀ x : p, q``의 특별한 경우로써 생각할 수 있습니다. 이때 ``q``는 ``x``에 의존하지 않습니다.

여기에 유형으로써 명제 대응이 현장에서 어떻게 놓이는지에 대한 예제가 있습니다.

```lean
example (α : Type) (p q : α → Prop) : (∀ x : α, p x ∧ q x) → ∀ y : α, p y  :=
  fun h : ∀ x : α, p x ∧ q x =>
  fun y : α =>
  show p y from (h y).left
```

기호 규약으로써 우리는 전칭 한정기호에게 가능한 가장 넓은 범위를 줍니다. 그래서 위의 예제에서 가정의 ``x``에만 한정사를 제한하도록 괄호가 필요합니다. ``∀ y : α, p y``을 증명하는 표준 방법은 임의의 ``y``를 받고  ``p y``임을 증명하는 것 입니다. 이것은 도입 규칙입니다. 이제 ``h``가 ``∀ x : α, p x ∧ q x``형을 갖는다고 해봅시다. 그러면 표현식 ``h y``는  ``p y ∧ q y``형을 갖습니다. 이것은 제거 규칙입니다. 왼쪽의 결합자를 취하는 것은 원하는 결론 ``p y``을 줍니다.

표현식들은 구속변수의 이름이 달라지기까지 동등한 것으로 간주된다는 것을 기억하세요. 그럼 예를들어 우리가 같은 변수 ``x`` 가정과 결론 양쪽에 사용할 수 있어야 합니다. 그리고 증명에서 다른 변수 ``z``에 의해 이것이 개체화됩니다.

```lean
example (α : Type) (p q : α → Prop) : (∀ x : α, p x ∧ q x) → ∀ x : α, p x  :=
  fun h : ∀ x : α, p x ∧ q x =>
  fun z : α =>
  show p z from And.left (h z)
```
또 다른 예제처럼 여기서 관계 ``r``이 추이적이라는 사실을 어떻게 표현할지를 보여줍니다.

```lean
variable (α : Type) (r : α → α → Prop)
variable (trans_r : ∀ x y z, r x y → r y z → r x z)

variable (a b c : α)
variable (hab : r a b) (hbc : r b c)

#check trans_r    -- ∀ (x y z : α), r x y → r y z → r x z
#check trans_r a b c
#check trans_r a b c hab
#check trans_r a b c hab hbc
```

무슨 일이 생긴 건지 생각해보세요. 우리가  ``trans_r``을 값 ``a b c``에 대해 개체화할 때, 우리는 ``r a b → r b c → r a c``의 증명을 갖게됩니다.
이를 "가정"  ``hab : r a b``에 적용함으로써 우리는 함의 ``r b c → r a c``의 증명을 얻습니다. 마침내, 이것을 가정 ``hbc``에 적용하는 것으로 결론 ``r a c``의 증명을 거둡니다.

그들이 ``hab hbc``으로부터 추론될 수 있을 때, 인자 ``a b c``를 제공하는 것은 번거로울 수 있습니다. 이런 이유로 이런 인자를 암시적으로 만드는 것은 흔합니다.

```lean
variable (α : Type) (r : α → α → Prop)
variable (trans_r : ∀ {x y z}, r x y → r y z → r x z)

variable (a b c : α)
variable (hab : r a b) (hbc : r b c)

#check trans_r
#check trans_r hab
#check trans_r hab hbc
```

이것의 장점은 우리가 간단히 ``trans_r hab hbc``을  ``r a c``의 증명으로 쓸 수 있다는 겁니다. 단점은 린이 표현식 ``trans_r``과 ``trans_r hab``에서 인자의 유형을 추론하기에 충분한 정보가 없다는 것 입니다. 처음 ``#check`` 명령의 출력은 ``r ?m.1 ?m.2 → r ?m.2 ?m.3 → r ?m.1 ?m.3``입니다. 이들은 여기에서 명시되지 않은 암시적 인자들을 지칭합니다.

이곳은 우리가 어떻게 동등 관계로 초등적인 추론을 하는지 예시를 보여줍니다.

```lean
variable (α : Type) (r : α → α → Prop)

variable (refl_r : ∀ x, r x x)
variable (symm_r : ∀ {x y}, r x y → r y x)
variable (trans_r : ∀ {x y z}, r x y → r y z → r x z)

example (a b c d : α) (hab : r a b) (hcb : r c b) (hcd : r c d) : r a d :=
  trans_r (trans_r hab (symm_r hcb)) hcd
```

전칭 한정기호 사용에 익숙해지기 위해서 여러분은 이 섹션 끝의 연습문제들을 풀어보아야 합니다.

이것은 의존 화살표 유형에 대한 타자 규칙입니다. 특히 그리고 전칭 한정기호는 ``Prop`` 과 다른 유형들을 구분합니다.  우리가 ``α : Sort i``과 ``β : Sort j``을 갖고 있다고 가정합시다. 여기서 표현식 ``β``는 변수  ``x : α``에 의존할 수도 있습니다. 그러면 ``(x : α) → β``은 ``Sort (imax i j)``의 원소입니다. 여기서 ``imax i j``는 ``i``와 ``j``사이의 최대값이고, ``j``가 0이 아니고, 이외에는 0입니다.

아이디어는 다음과 같습니다. 만약 ``j``가 ``0``이 아니라면 ``(x : α) → β``는 ``Sort (max i j)``의 원소이다. 다시 말하면, ``α``에서 ``β``로의 의존 함수 유형이 그것의 첨자가 ``i``와 ``j`` 중 최대값인 유형세계에 "성립한다"입니다. 그러나 ``β``가 ``Sort 0``형이라고 가정하면 즉, ``Prop``의 원소라면 그 경우 ``α``가 어느 유형세계에 속하였든 상관없이 ``(x : α) → β``도 ``Sort 0``의 원소입니다. 다시 말해서, 만약 ``β``가 ``α``에 의존하는 명제라면 ``∀ x : α, β``도 다시 명제인 것입니다. 이것은 데이터보다는 명제의 유형으로써 ``Prop``의 해석을 반영했습니다. 그리고 이것이 ``Prop``을 *impredicative*하게 만드는 것입니다.

"술어"라는 말은 20세기로 접어드는 시기에 기초수학의 발전으로부터 유래되었습니다.  이때 푸엥카레와 레셀 같은 논리학자들은 정의되는 바로 그 정의되는 성질을 포함하는 모임에 대해 한정함으로써 성질을 정의할 때 발생하는 집합론적 역설 "악순환(vicious circles)"을 비난했습니다. 만약 ``α``가 임의의 유형이면, 우리는  ``α``에 대한 모든 술어에 대해 ``α → Prop``형을 만들 수 있습니다. (" ``α``형의 능력") Prop의 비서술어는 우리가 ``α → Prop``를 한정하는 명제를 세울 수 있음을 의미합니다. 특히, 우리는 ``α``에 대한 술어를 ``α``에 대한 모든 술어를 한정함으로써 정의할 수 있습니다. 그리고 이게 한때 문제라고 여겼던 순환 유형입니다.

동등성
--------

이제 주로 동등 관계라고 하는 린의 라이브러리에 정의된 가장 기초적인 관계 중 하나로 가봅시다. [귀납형 장](inductive_types.md)에서 우리는 *어떻게* 동등이 린의 기초적인 논리 프레임워크로부터 정의되는지 설명할 것입니다.
한편, 여기서는 어떻게 그것을 사용할지 설명합니다.

물론 동등의 기초적인 성질은 등가 관계라는 것입니다.

```lean
#check Eq.refl    -- ∀ (a : ?m.1), a = a
#check Eq.symm    -- ?m.2 = ?m.3 → ?m.3 = ?m.2
#check Eq.trans   -- ?m.2 = ?m.3 → ?m.3 = ?m.4 → ?m.2 = ?m.4
```

우리는 린에게 암시적인 인자를 삽입하지 말라 함으로써 출력을 더 쉽게 읽어들이도록 만들 수 있습니다.(메타변수로서 나타난 인자입니다.)

```lean
universe u

#check @Eq.refl.{u}   -- ∀ {α : Sort u} (a : α), a = a
#check @Eq.symm.{u}   -- ∀ {α : Sort u} {a b : α}, a = b → b = a
#check @Eq.trans.{u}  -- ∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
```

접두사 ``.{u}``은 린에게 세계변수 ``u``로 상수를 개체화하라고 말해줍니다.

따라서, 우리는 이전 섹션에서 동등 관계까지의 예를 특수화 할 수 있습니다.
```lean
variable (α : Type) (a b c d : α)
variable (hab : a = b) (hcb : c = b) (hcd : c = d)

example : a = d :=
  Eq.trans (Eq.trans hab (Eq.symm hcb)) hcd
```

또 우리는 투영 기호(인덱싱 기호)를 사용할 수 있습니다.

```lean
# variable (α : Type) (a b c d : α)
# variable (hab : a = b) (hcb : c = b) (hcd : c = d)
example : a = d := (hab.trans hcb.symm).trans hcd
```

대칭성은 보기 보다 더 강력합니다. 직관주의적 계산법의 항은 계산적인 해석을 갖고 논리 프레임워크는 공통 환원된 항을 같은 것으로 다룬는 것을 기억하세요. 결과적으로 어떤 비직관적인 항등식들이 대칭성으로부터 증명됩니다.

```lean
variable (α β : Type)

example (f : α → β) (a : α) : (fun x => f x) a = f a := Eq.refl _
example (a : α) (b : α) : (a, b).1 = a := Eq.refl _
example : 2 + 3 = 5 := Eq.refl _
```

프레임워크의 이 특징은 너무 중요해서 라이브러리가 ``Eq.refl _``에 대한 기호 ``rfl``을 정의합니다.

```lean
# variable (α β : Type)
example (f : α → β) (a : α) : (fun x => f x) a = f a := rfl
example (a : α) (b : α) : (a, b).1 = a := rfl
example : 2 + 3 = 5 := rfl
```

하지만 동등은 등가 관계 그 이상입니다. 우리가  같은 표현식들을 진리값을 바꾸지 않고 대체할 수 있다는 점에서 등가에 대한 모든 주장은 중요한 성질이 있습니다. 즉, ``h1 : a = b``과 ``h2 : p a``에 대해 ``p b``에 대한 증명을 ``Eq.subst h1 h2``과 같은 대체를 사용하여 만들 수 있습니다.

```lean
example (α : Type) (a b : α) (p : α → Prop)
        (h1 : a = b) (h2 : p a) : p b :=
  Eq.subst h1 h2

example (α : Type) (a b : α) (p : α → Prop)
    (h1 : a = b) (h2 : p a) : p b :=
  h1 ▸ h2
```

두번째 보기에서 삼각형은 ``Eq.subst``과 ``Eq.symm`` 위에 세워진 매크로입니다. 여러분은 이것은 ``\t``을 쳐서 쓸 수 있습니다.

``Eq.subst``의 규칙은 더 명백한 대체를 수행하는 다음의 부가적인 규칙을 정의하는데 사용됩니다. 이들은 응용 항을 다루기 위해 설계되었습니다. 즉,  ``s t`` 꼴의 항입니다. 구체적으로 ``congrArg``은 인수를 대체하는데 사용될 수 있습니다. ``congrFun``은 적용된 항을 대체하는데 사용할 수 있습니다. 그리고 ``congr``는 한번에 둘 다 대체하는데 사용될 수 있습니다.

```lean
variable (α : Type)
variable (a b : α)
variable (f g : α → Nat)
variable (h₁ : a = b)
variable (h₂ : f = g)

example : f a = f b := congrArg f h₁
example : f a = g a := congrFun h₂ a
example : f a = g b := congr h₂ h₁
```

린의 라이브러리는 이와 같은 흔한 항등식들을 많이 가지고 있습니다.

```lean
variable (a b c d : Nat)

example : a + 0 = a := Nat.add_zero a
example : 0 + a = a := Nat.zero_add a
example : a * 1 = a := Nat.mul_one a
example : 1 * a = a := Nat.one_mul a
example : a + b = b + a := Nat.add_comm a b
example : a + b + c = a + (b + c) := Nat.add_assoc a b c
example : a * b = b * a := Nat.mul_comm a b
example : a * b * c = a * (b * c) := Nat.mul_assoc a b c
example : a * (b + c) = a * b + a * c := Nat.mul_add a b c
example : a * (b + c) = a * b + a * c := Nat.left_distrib a b c
example : (a + b) * c = a * c + b * c := Nat.add_mul a b c
example : (a + b) * c = a * c + b * c := Nat.right_distrib a b c
```

``Nat.mul_add``과 ``Nat.add_mul``은 각각 ``Nat.left_distrib``과 ``Nat.right_distrib``에 대한 별명임을 유의하세요.  위의 성질들은 자연수 (type ``Nat``)에 대해 기술되었습니다.

여기 자연수에 대한 대체과 결합성, 교환성, 분배성을 혼합한 계산 예제가 있습니다.

```lean
example (x y z : Nat) : x * (y + z) = x * y + x * z := Nat.mul_add x y z
example (x y z : Nat) : (x + y) * z = x * z + y * z := Nat.add_mul x y z
example (x y z : Nat) : x + y + z = x + (y + z) := Nat.add_assoc x y z

example (x y : Nat) : (x + y) * (x + y) = x * x + y * x + x * y + y * y :=
  have h1 : (x + y) * (x + y) = (x + y) * x + (x + y) * y :=
    Nat.mul_add (x + y) x y
  have h2 : (x + y) * (x + y) = x * x + y * x + (x * y + y * y) :=
    (Nat.add_mul x y x) ▸ (Nat.add_mul x y y) ▸ h1
  h2.trans (Nat.add_assoc (x * x + y * x) (x * y) (y * y)).symm
```

대체가 일어나는 곳에 대한 맥락을 제공하는 두번째 암시적 인수 ``Eq.subst``이 ``α → Prop``형을 가지는 것을 보세요.  이 술어를 추론하는 것은 그러므로 *고차 통합*의 개체를 요구합니다. 완전 일반적으로 고차 통합자가 존재하는지 정하는 문제는 결정 불가능합니다. 그리고 린은 최선을 다해 이 문제에 부정확하지만 근사적인 해를 제공할 수 있습니다. 그러므로 ``Eq.subst``은 여러분이 원하는 대로 항상 행하지 못합니다.  매크로 ``h ▸ e``은 이 암시적 인자를 계산하는데 더욱 효과적인 경험론을 사용합니다. 그리고 종종 ``Eq.subst``의 적용이 실패하는 상황에서 성공적입니다.


방정식적인 추론은 꽤 흔하고 중요하기 때문에 린은 그것을 더 효과적으로 수행하는 다수의 메커니즘을 제공합니다. 다음 섹션은 여러분이 계산 증명을 더 자연스럽고 안목이 있는 방향으로 작성하게 하는 문법을 제공합니다. 그러나 더 중요한 것은 방정식적인 추론은 항 다시쓰기, 단순화, 그리고 여타의 자동화에서도 지원된다는 점 입니다. 항 다시쓰기와 단순화는 다음 섹션에서 간단히 설명합니다. 그러고 나서 다음 장에서 아주 상세하게 다룹니다.

계산 증명
--------------------

계산 증명은 동등의 전달성과 같은 기본 원리로 구성된 것을 의미하는 중간 단계의 결과를 연결할 뿐입니다. 린에서 계산 증명은 키워드 ``calc``로 시작합니다. 그리고 다음 문법을 갖습니다.

```
calc
  <expr>_0  'op_1'  <expr>_1  ':='  <proof>_1
    '_'     'op_2'  <expr>_2  ':='  <proof>_2
     ...
    '_'     'op_n'  <expr>_n  ':='  <proof>_n

```

각  ``<proof>_i``는 ``<expr>_{i-1} op_i <expr>_i``에 대한 증명입니다.

여기 예제가 있습니다.

```lean
variable (a b c d e : Nat)
variable (h1 : a = b)
variable (h2 : b = c + 1)
variable (h3 : c = d)
variable (h4 : e = 1 + d)

theorem T : a = e :=
  calc
    a = b      := h1
    _ = c + 1  := h2
    _ = d + 1  := congrArg Nat.succ h3
    _ = 1 + d  := Nat.add_comm d 1
    _ = e      := Eq.symm h4
```

증명 작성 스타일은 ``simp``와 ``rewrite`` 전략을 결합해 사용되었을 때 가장 효과적입니다. 이것들은 다음 장에서 상세히 논할 것입니다. 예를 들어, 다시쓰기에 대해서 간략히 ``rw``를 쓰는 것으로 위의 증명은 다음과 같이 다시 쓸 수 있습니다.

```lean
# variable (a b c d e : Nat)
# variable (h1 : a = b)
# variable (h2 : b = c + 1)
# variable (h3 : c = d)
# variable (h4 : e = 1 + d)
theorem T : a = e :=
  calc
    a = b      := by rw [h1]
    _ = c + 1  := by rw [h2]
    _ = d + 1  := by rw [h3]
    _ = 1 + d  := by rw [Nat.add_comm]
    _ =  e     := by rw [h4]
```

본질적으로 ``rw`` 전략은 주어진 동등성을 목표(혹은 가정, 정리, 복잡한 항이 될 수도 있음)를 "다시 쓰는데" 사용합니다. 그렇게 하면 항등식 ``t = t``로 목표를 축소합니다. 전략은 그것을 증명하는데 대칭성을 씁니다.

다시쓰기는 연속적으로 쓸 수 있습니다. 따라서 위의 증명은 이와 같이 더 짧아질 수 있습니다.

```lean
# variable (a b c d e : Nat)
# variable (h1 : a = b)
# variable (h2 : b = c + 1)
# variable (h3 : c = d)
# variable (h4 : e = 1 + d)
theorem T : a = e :=
  calc
    a = d + 1  := by rw [h1, h2, h3]
    _ = 1 + d  := by rw [Nat.add_comm]
    _ =  e     := by rw [h4]
```

심지어 이렇게도 됩니다.

```lean
# variable (a b c d e : Nat)
# variable (h1 : a = b)
# variable (h2 : b = c + 1)
# variable (h3 : c = d)
# variable (h4 : e = 1 + d)
theorem T : a = e :=
  by rw [h1, h2, h3, Nat.add_comm, h4]
```

대신 ``simp`` 전략은 주어진 항등식들을 그들이 항에 적용되는 어느 곳이든 임의의 순서대로 반복적으로 사용하여 목표를 다시 씁니다. 또 이것은 시스템에서 전에 선언된 적 있는 다른 규칙을 사용합니다.그리고 무한 루프를 현명하게 피하면서 교환성을 사용합니다. 결론적으로 다음과 같이 정리를 증명할 수도 있습니다.

```lean
# variable (a b c d e : Nat)
# variable (h1 : a = b)
# variable (h2 : b = c + 1)
# variable (h3 : c = d)
# variable (h4 : e = 1 + d)
theorem T : a = e :=
  by simp [h1, h2, h3, Nat.add_comm, h4]
```

다음 장에서 ``rw``와 ``simp``의 변형을 다룰 것입니다.

``calc`` 명령은 전달성의 몇몇 형태를 지원하는 어떤 관계에 대해서 설정될 수 있습니다. 심지어 이것은 다른 관계와 혼합될 수 있습니다.

```lean
example (a b c d : Nat) (h1 : a = b) (h2 : b ≤ c) (h3 : c + 1 < d) : a < d :=
  calc
    a = b     := h1
    _ < b + 1 := Nat.lt_succ_self b
    _ ≤ c + 1 := Nat.succ_le_succ h2
    _ < d     := h3
```

``calc``를 통해서 우리는 지난 섹션에서 증명을 더 자연스럽고 안목있는 방식으로 작성할 수 있었습니다.

```lean
example (x y : Nat) : (x + y) * (x + y) = x * x + y * x + x * y + y * y :=
  calc
    (x + y) * (x + y) = (x + y) * x + (x + y) * y  := by rw [Nat.mul_add]
        _ = x * x + y * x + (x + y) * y            := by rw [Nat.add_mul]
        _ = x * x + y * x + (x * y + y * y)        := by rw [Nat.add_mul]
        _ = x * x + y * x + x * y + y * y          := by rw [←Nat.add_assoc]
```

``Nat.add_assoc`` 앞의 왼쪽 화살표는 항등식을 반대 방향으로 사용해 다시쓰라고 말합니다. (여러분은 이것을 ``\l``을 치거나 아스키 형식 ``<-``을 사용할 수 있습니다.) 우리가 간결함을 추구한다면 ``rw``과``simp``이 알아서 처리해 줄 것입니다.

```lean
example (x y : Nat) : (x + y) * (x + y) = x * x + y * x + x * y + y * y :=
  by rw [Nat.mul_add, Nat.add_mul, Nat.add_mul, ←Nat.add_assoc]

example (x y : Nat) : (x + y) * (x + y) = x * x + y * x + x * y + y * y :=
  by simp [Nat.mul_add, Nat.add_mul, Nat.add_assoc, Nat.add_left_comm]
```

존재 한정기호
--------------------------

마지막으로 ``exists x : α, p x``나 ``∃ x : α, p x``으로 쓸 수 있는 존재 한정기호를 고려해봅시다.  두 버전 다 린의 라이브러리에 정의된 길고 장황한 표현식 ``Exists (fun x : α => p x)``을 위한 기호적으로 편리한 약어입니다.

지금 예상한 대로 라이브러리는 도입 규칙과 소거 규칙 둘 다 가지고 있습니다. 도입 규칙은 직관적입니다. ``∃ x : α, p x``을 증명하기 위해 적절한 항 ``t``와 ``p t``의 증명을 제공하는 것으로 충분합니다. 여기 몇 가지 예제가 있습니다.

```lean
example : ∃ x : Nat, x > 0 :=
  have h : 1 > 0 := Nat.zero_lt_succ 0
  Exists.intro 1 h

example (x : Nat) (h : x > 0) : ∃ y, y < x :=
  Exists.intro 0 h

example (x y z : Nat) (hxy : x < y) (hyz : y < z) : ∃ w, x < w ∧ w < z :=
  Exists.intro y (And.intro hxy hyz)

#check @Exists.intro
```

우리는 맥락으로부터 형이 명백한 경우 익명 생성자 기호 ``⟨t, h⟩``을 ``Exists.intro t h``에 대해 사용할 수 있습니다.

```lean
example : ∃ x : Nat, x > 0 :=
  have h : 1 > 0 := Nat.zero_lt_succ 0
  ⟨1, h⟩

example (x : Nat) (h : x > 0) : ∃ y, y < x :=
  ⟨0, h⟩

example (x y z : Nat) (hxy : x < y) (hyz : y < z) : ∃ w, x < w ∧ w < z :=
  ⟨y, hxy, hyz⟩
```

``Exists.intro``은 암시적인자를 가지고 있음을 유의하세요. 린은 결론 ``∃ x, p x``에서 술어 ``p : α → Prop``를 추론해야만 합니다.  이것은 명백한 문제가 아닙니다. 예를 들어 우리가 have ``hg : g 0 0 = 0``를 갖고 있고 ``Exists.intro 0 hg``을 썼다면 정리  ``∃ x, g x x = x``, ``∃ x, g x x = 0``, ``∃ x, g x 0 = x`` 등에 대응하는 술어 ``p``에 대해 수없이 많은 가능한 값이 존재합니다. 린은 어떤 것이 적절한 지 추론하는데 맥락을 사용합니다. 이것은 다음 예제에서 보여주고 있습니다. 여기서 암시적 인자를 보여주는데 린의 깔끔한 출력을 사용하도록 ``pp.explicit`` 옵션을 참으로 설정하였습니다.

```lean
variable (g : Nat → Nat → Nat)
variable (hg : g 0 0 = 0)

theorem gex1 : ∃ x, g x x = x := ⟨0, hg⟩
theorem gex2 : ∃ x, g x 0 = x := ⟨0, hg⟩
theorem gex3 : ∃ x, g 0 0 = x := ⟨0, hg⟩
theorem gex4 : ∃ x, g x x = 0 := ⟨0, hg⟩

set_option pp.explicit true  -- display implicit arguments
#print gex1
#print gex2
#print gex3
#print gex4
```

주장의 몸체의 발견을 감추기 때문에 우리는 ``Exists.intro``을 정보 감추기 연산으로 볼 수 있습니다. 존재 한정기호 제거 규칙 ``Exists.elim``은 정반대 연산을 수행합니다. 임의의 값 ``w``에 대해 ``p w``로부터 ``q``임을 보임으로써 ``∃ x : α, p x``으로부터 명제 ``q``를 증명하게 해줍니다. 대략 말하자면 ``p x``를 만족하는 ``x``가 있다는 것을 알기 때문에 이것에 ``w``라는 이름을 줄 수 있다는 것입니다. ``q``가  ``w``를 언급하지 않았다면 ``p w``로부터 ``q``가 따름을 보이는 것으로 임의의 ``x``의 존재함으로부터  ``q``를 보이기에 충분합니다. 여기 예제가 있습니다.

```lean
variable (α : Type) (p q : α → Prop)

example (h : ∃ x, p x ∧ q x) : ∃ x, q x ∧ p x :=
  Exists.elim h
    (fun w =>
     fun hw : p w ∧ q w =>
     show ∃ x, q x ∧ p x from ⟨w, hw.right, hw.left⟩)
```

존재-제거 규칙과 논리합-제거 규칙을 비교하는것은 도움이 아마 도움이 될 것입니다. 왜냐하면 ``a``가 모든 ``α``의 요소 범위를 갖기 때문에 명제 ``∃ x : α, p x``은 커다란 명제의 분리자  ``p a``로 생각할 수 있습니다. 익명 생성자 기호 ``⟨w, hw.right, hw.left⟩``가 중첩된 생성자 활용을 간략히 한다는 것을 주목하세요. 우리는 이를 ``⟨w, ⟨hw.right, hw.left⟩⟩``로 동등한 의미를 갖게 쓸 수 있습니다.

존재 명제는 의존 유형론 섹션에서 설명했던 시그마 유형과 아주 비슷한 것을 보세요.  차이점은 ``a : α``와 ``h : p a``에 대해서 항 ``Exists.intro a h``은 e ``(∃ x : α, p x) : Prop`` 형을 가지고 ``Sigma.mk a h``는 ``(Σ x : α, p x) : Type``형을 갖는다는 점입니다. ``∃``과``Σ``의 유사점은 이들이 커리-하워드 동형의 또 다른 개체라는 점입니다.

린은 ``match`` 표현식이 있는 존재 한정기호를 더 편리하게 제거하는 방법을 제공합니다.

```lean
variable (α : Type) (p q : α → Prop)

example (h : ∃ x, p x ∧ q x) : ∃ x, q x ∧ p x :=
  match h with
  | ⟨w, hw⟩ => ⟨w, hw.right, hw.left⟩
```

``match`` 표현식은 복잡한 함수를 정의하는데 편리하고 표현력있는 방식을 제공하는 린의 함수 정의 시스템의 일부분입니다.  한 번 더  커리-하워드 동형은 우리가 증명을 작성하는 데에도 이 메커니즘과 함께 쓰이게 합니다.  ``match`` 구문은 존재 주장 속 성분인 ``w``와 ``hw``로 '파괴'합니다.  이들은 명제를 증명하기 위해 문장의 몸체에서 사용될 수 있습니다. 우리는 더 명확함을 위해 match에서 사용되는 유형을 나타낼 수 있습니다.

```lean
# variable (α : Type) (p q : α → Prop)
example (h : ∃ x, p x ∧ q x) : ∃ x, q x ∧ p x :=
  match h with
  | ⟨(w : α), (hw : p w ∧ q w)⟩ => ⟨w, hw.right, hw.left⟩
```

심지어 우리는 match 문장을 분해하는 동시에 결합하기 위해 사용할 수 있습니다.

```lean
# variable (α : Type) (p q : α → Prop)
example (h : ∃ x, p x ∧ q x) : ∃ x, q x ∧ p x :=
  match h with
  | ⟨w, hpw, hqw⟩ => ⟨w, hqw, hpw⟩
```

또 린은 패턴-매칭 ``let`` 표현식을 제공합니다.<부분 1562 ¶>

```lean
# variable (α : Type) (p q : α → Prop)
example (h : ∃ x, p x ∧ q x) : ∃ x, q x ∧ p x :=
  let ⟨w, hpw, hqw⟩ := h
  ⟨w, hqw, hpw⟩
```

이것은 본질적으로 위의 ``match`` 생성을 위한 대체 기호일 뿐입니다. 더욱이 린은 우리에게 ``fun`` 표현식에서 암시적인 ``match``를 사용할 수 있게 해줍니다.

```lean
# variable (α : Type) (p q : α → Prop)
example : (∃ x, p x ∧ q x) → ∃ x, q x ∧ p x :=
  fun ⟨w, hpw, hqw⟩ => ⟨w, hqw, hpw⟩
```

 [유도와 재귀](./induction_and_recursion.md)에서 더 일반적인 패턴-매칭 생성 개체들의 모든 변형을 볼 겁니다.

다음 예제에서 우리는 ``짝수 a``를 ``∃ b, a = 2*b``와 같이 정의합니다. 그런 뒤 두 짝수의 합이 짝수임을 보일 것 입니다.

```lean
def is_even (a : Nat) := ∃ b, a = 2 * b

theorem even_plus_even (h1 : is_even a) (h2 : is_even b) : is_even (a + b) :=
  Exists.elim h1 (fun w1 (hw1 : a = 2 * w1) =>
  Exists.elim h2 (fun w2 (hw2 : b = 2 * w2) =>
    Exists.intro (w1 + w2)
      (calc
        a + b = 2 * w1 + 2 * w2  := by rw [hw1, hw2]
          _   = 2*(w1 + w2)      := by rw [Nat.mul_add])))
```

여기서 설명한 다양한 도구-match 구문, 익명 생성자,  ``다시쓰기``전략-를 사용하여 다음과 같이 이 증명을 간결하게 쓸 수 있습니다.

```lean
# def is_even (a : Nat) := ∃ b, a = 2 * b
theorem even_plus_even (h1 : is_even a) (h2 : is_even b) : is_even (a + b) :=
  match h1, h2 with
  | ⟨w1, hw1⟩, ⟨w2, hw2⟩ => ⟨w1 + w2, by rw [hw1, hw2, Nat.mul_add]⟩
```

직관주의적 "or"은 고전주의의 "or"보다 강한 것처럼 직관주의적 "존재한다"도 고전주의적 "존재한다"보다 강한 의미를 가집니다. 예를 들어, 직관주의적 관점에서 모든 ``x``가 ``¬p``을 만족하는 경우가 아니라는 것을 아는 것은 ``p``를 만족하는 특정 ``x``를 갖는 것과 같지 않기 때문에 다음의 함의는 고전적인 추론을 필요로 합니다.

```lean
open Classical
variable (p : α → Prop)

example (h : ¬ ∀ x, ¬ p x) : ∃ x, p x :=
  byContradiction
    (fun h1 : ¬ ∃ x, p x =>
      have h2 : ∀ x, ¬ p x :=
        fun x =>
        fun h3 : p x =>
        have h4 : ∃ x, p x :=  ⟨x, h3⟩
        show False from h1 h4
      show False from h h2)
```

다음은 존재 한정기호를 포함한 몇 가지 흔한 항등식들 입니다. 아래 연습 문제에서 여러분이 할 수 있는 가능한 많이 증명해보길 권합니다. 우리는 또한 어떤 것이 비직관주의적인지 결정하는 것을 여러분에게 맡깁니다. 그러므로 일부는 고전 논리의 형식를 요구합니다.

```lean
open Classical

variable (α : Type) (p q : α → Prop)
variable (r : Prop)

example : (∃ x : α, r) → r := sorry
example (a : α) : r → (∃ x : α, r) := sorry
example : (∃ x, p x ∧ r) ↔ (∃ x, p x) ∧ r := sorry
example : (∃ x, p x ∨ q x) ↔ (∃ x, p x) ∨ (∃ x, q x) := sorry

example : (∀ x, p x) ↔ ¬ (∃ x, ¬ p x) := sorry
example : (∃ x, p x) ↔ ¬ (∀ x, ¬ p x) := sorry
example : (¬ ∃ x, p x) ↔ (∀ x, ¬ p x) := sorry
example : (¬ ∀ x, p x) ↔ (∃ x, ¬ p x) := sorry

example : (∀ x, p x → r) ↔ (∃ x, p x) → r := sorry
example (a : α) : (∃ x, p x → r) ↔ (∀ x, p x) → r := sorry
example (a : α) : (∃ x, r → p x) ↔ (r → ∃ x, p x) := sorry
```

두 번째 예제와 마지막 두 예제는 ``α``형의 한 원소 ``a``가 적어도 하나 있다는 가정을 필요로 한다는 것을 유의하세요.

여기 더 어려운 두 문제에 대한 해답이 있습니다.

```lean
open Classical

variable (α : Type) (p q : α → Prop)
variable (a : α)
variable (r : Prop)

example : (∃ x, p x ∨ q x) ↔ (∃ x, p x) ∨ (∃ x, q x) :=
  Iff.intro
    (fun ⟨a, (h1 : p a ∨ q a)⟩ =>
      Or.elim h1
        (fun hpa : p a => Or.inl ⟨a, hpa⟩)
        (fun hqa : q a => Or.inr ⟨a, hqa⟩))
    (fun h : (∃ x, p x) ∨ (∃ x, q x) =>
      Or.elim h
        (fun ⟨a, hpa⟩ => ⟨a, (Or.inl hpa)⟩)
        (fun ⟨a, hqa⟩ => ⟨a, (Or.inr hqa)⟩))

example : (∃ x, p x → r) ↔ (∀ x, p x) → r :=
  Iff.intro
    (fun ⟨b, (hb : p b → r)⟩ =>
     fun h2 : ∀ x, p x =>
     show r from  hb (h2 b))
    (fun h1 : (∀ x, p x) → r =>
     show ∃ x, p x → r from
       byCases
         (fun hap : ∀ x, p x => ⟨a, λ h' => h1 hap⟩)
         (fun hnap : ¬ ∀ x, p x =>
          byContradiction
            (fun hnex : ¬ ∃ x, p x → r =>
              have hap : ∀ x, p x :=
                fun x =>
                byContradiction
                  (fun hnp : ¬ p x =>
                    have hex : ∃ x, p x → r := ⟨x, (fun hp => absurd hp hnp)⟩
                    show False from hnex hex)
              show False from hnap hap)))
```

증명 언어에 대한 자세한 내용
--------------------------

우리는 ``fun``과 ``have``,``show``와 같은 키워드가 비형식적인 수학적 증명의 구조를 반영하는 형식적 증명 용어를 쓸 수 있게 만든 것을 보았습니다. 이 섹션에서는 종종 편리한 증명 언어의 몇 가지 추가적인 기능에 대해 설명합니다.

우선, 우리는 익명 "have" 표현식으로 보조 목표의 이름 없이 도입하는데 사용할 수 있습니다. 이렇게 도입된 마지막 표현식을 키워드 `` this``를 사용하여 참조할 수 있습니다.

```lean
variable (f : Nat → Nat)
variable (h : ∀ x : Nat, f x ≤ f (x + 1))

example : f 0 ≤ f 3 :=
  have : f 0 ≤ f 1 := h 0
  have : f 0 ≤ f 2 := Nat.le_trans this (h 1)
  show f 0 ≤ f 3 from Nat.le_trans this (h 2)
```

증명은 종종 한 사실에서 다음 사실로 이동하기 때문에 이것은 많은 이름으로 생기는 혼동을 없애는 데 효과적입니다.

목표가 추론될 수 있을 때, 우리는 ``by assumption``을 써 증명을 채우는 대신 린에게 물어볼 수도 있습니다.

```lean
# variable (f : Nat → Nat)
# variable (h : ∀ x : Nat, f x ≤ f (x + 1))
example : f 0 ≤ f 3 :=
  have : f 0 ≤ f 1 := h 0
  have : f 0 ≤ f 2 := Nat.le_trans (by assumption) (h 1)
  show f 0 ≤ f 3 from Nat.le_trans (by assumption) (h 2)
```

이것은 린에게 ``assumption`` 전략을 사용하라고 말합니다. 따라서 이 전략은 현재 상황판에서 적절한 가정을 찾아 목표를 증명합니다. 다음 장에서 ``assumption`` 전략에 대해 더 배울 예정입니다.

또 우린 린에게 ``‹p›``라고 써서 증명 속을 채우도록 린에게 요청할수 있습니다. 여기서 ``p``는 명제이고, 그것의 증명은 현재 상황에서 린이 찾기 바라는 것입니다.  여러분은 이런 인용 꺽쇠를 각각 ``\f<``과 ``\f>``을 사용해서 칠 수 있습니다. "f"는 "프랑스"의 첫머리 글자입니다. 왜냐하면 이 유니코드 기호는 프랑스 인용부호로도 사용되기 때문입니다. 사실 린에서 정의된 기호는 다음과 같습니다.

```lean
기호 "‹" p "›" => 은 가정에 의해 p가 참임을 보입니다.
```

추론될 필요가 있는 가정의 유형은 명백하게 주어져야 하므로 이런 접근법은 ``by assumption``을 사용하는 것보다 더 견고합니다. 또 이것은 증명을 더 가독성있게 만듭니다. 여기 더 협력(elaborate)하는 예제들이 있습니다.

```lean
variable (f : Nat → Nat)
variable (h : ∀ x : Nat, f x ≤ f (x + 1))

example : f 0 ≥ f 1 → f 1 ≥ f 2 → f 0 = f 2 :=
  fun _ : f 0 ≥ f 1 =>
  fun _ : f 1 ≥ f 2 =>
  have : f 0 ≥ f 2 := Nat.le_trans ‹f 1 ≥ f 2› ‹f 0 ≥ f 1›
  have : f 0 ≤ f 2 := Nat.le_trans (h 0) (h 1)
  show f 0 = f 2 from Nat.le_antisymm this ‹f 0 ≥ f 2›
```

여러분은 프랑스 인용부호를 맥락 속에서 익명으로 도입된 것들 뿐만 아니라 *어떤 것이든* 참조하기 위해 사용될 수 있다는 점을 명심하세요. 그것의 용도는 명제에마 국한되지 않고 약간 이상하지만 데이터에 대해서도 사용됩니다.

```lean
example (n : Nat) : Nat := ‹Nat›
```

나중에 우리는 린의 매크로 시스템을 사용해서 증명 언어를 확장하는 방법을 소개합니다.

연습문제
---------

1. 이 등가식들을 증명하세요.

```lean
 variable (α : Type) (p q : α → Prop)

 example : (∀ x, p x ∧ q x) ↔ (∀ x, p x) ∧ (∀ x, q x) := sorry
 example : (∀ x, p x → q x) → (∀ x, p x) → (∀ x, q x) := sorry
 example : (∀ x, p x) ∨ (∀ x, q x) → ∀ x, p x ∨ q x := sorry
```
여러분은 왜 명제의 역이 마지막 예제에서 불가능한지 이해하려고 시도해봐야 합니다.

2. 식이 정량화된 변수에 의존하지 않을 때 종종 전칭 한정기호를 식의 바깥 쪽으로 가져올 수 있습니다. 이것들을 증명해 보세요.(이들 두 번째 예제의 한쪽 방향은 고전논리가 필요합니다.)

```lean
variable (α : Type) (p q : α → Prop)
variable (r : Prop)

example : α → ((∀ x : α, r) ↔ r) := sorry
example : (∀ x, p x ∨ r) ↔ (∀ x, p x) ∨ r := sorry
example : (∀ x, r → p x) ↔ (r → ∀ x, p x) := sorry
```

3. "이발사의 역설"을 고려해보세요. 즉, 그들 자신을 면도하지 않는 남자만 면도해 준다고 주장하는 어떤 마을의 (남자) 이발사의 주장입니다. 이것이 모순임을 증명하세요.

```lean
variable (men : Type) (barber : men)
variable  (shaves : men → men → Prop)

example (h : ∀ x : men, shaves barber x ↔ ¬ shaves x x) : False := sorry
```

4. 어떤 매개변수도 없이 ``Prop``형의 표현식은 그저 주장일 뿐이라는 걸 기억하세요. 아래의 ``prime``과 ``Fermat_prime``의 정의를 채우세요. 그리고 주어진 주장의 각각을 생성하세요. 예를 들어, 여러분은 모든 자연수 ``n``에 대해 ``n``보다 큰 소수가 있다고 주장하여 무한히 많은 소수가 있다고 말할 수 있습니다. 골드바흐의 약한 추측은 5보다 큰 모든 홀수 세 소수의 합으로 표현될 수 있다고 말합니다. 페르마 소수의 정의나 필요하다면 다른 문장들을 찾아보세요.

```lean
def even (n : Nat) : Prop := sorry

def prime (n : Nat) : Prop := sorry

def infinitely_many_primes : Prop := sorry

def Fermat_prime (n : Nat) : Prop := sorry

def infinitely_many_Fermat_primes : Prop := sorry

def goldbach_conjecture : Prop := sorry

def Goldbach's_weak_conjecture : Prop := sorry

def Fermat's_last_theorem : Prop := sorry
```

5. 존재 정량자에서 수록된 항등식을 여러분이 할 수 있는 만큼 가능한 많이 증명해보세요.
