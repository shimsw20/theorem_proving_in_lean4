공리와 계산
======================

우리는 린에 구현된 직관주의적 계산의 버전이 의존 함수 유형, 귀납형, 맨 바닥에 증명과 무관한 ``Prop``과 비서술어를 갖는 유형세계 계층을 포함한 것을 봤습니다. 이 장에서 추가 공리와 규칙을 사용해 CIC를 확장하는 방벙을 고려합니다. 이런 식으로 기초 체계를 확장하는 것은 종종 편리합니다. 이는 더 많은 정리를 증명할 수 있게 만들 뿐 아니라 다른 방식으로 증명된 정리를 더 쉽게 증명하도록 만듭니다. 그러나 공리를 추가하는 것은 부정적인 결과가 될 수 있으며 그들의 정확성에 대한 우려를 넘을 수 있습니다. 특히 공리의 사용은 여기서 탐구할 정리와 공리의 계산적 내용에 영향을 미칩니다.

린은 계산적 추론과 고전 추론 모두를 지원하도록 설계되었습니다. 그런 경향이 있는 사용자는 시스템의 닫힌 표현식이 표준 정규 형식으로 평가되도록 보장하는 "계산적으로 순수함" 면을 고수할 수 있습니다. 특히, 예를 들어 ``Nat``형의 임의의 닫힌 계산적으로 순수한 표현식 수치값으로 축약됩니다.

린의 표준 라이브러리는 부가적인 공리, 명제적 확장성과 함수 확장성의 원리를 차례로 함의하는 몫 구성을 정의합니다. 이 확장은 예를 들어 집합과 유한 집합의 이론을 만드는데 사용됩니다. 우리는 아래에서 이 정리들을 사용하여 린의 커널의 평가를 차단해 ``Nat``형의 닫힌 항이 더 이상 수치값으로 평가되지 않게 함을 볼 것입니다. 린의 가상 머신 평가기를 위해 정의를 바이트 코드로 컴파일 할 때 린은 유형과 명제 정보를 지웁니다. 왜냐하면 이런 공리는 새 명제를 더할 뿐이기 때문에 이들은 계산적 해석과도 호환됩니다. 심지어 계산적으로 편향된 사용자들도 계산에 대해 배중률을 포함한 고전 논리를 사용해 추론하기를 바랄 수 있습니다. 이것도 커널에서 평가를 차단하지만 바이트 코드로 컴파일하는 것과 호환됩니다.

또한 표준 라이브러리는 마술처럼 선택 원리의 존재를 주장하는 명제로부터 "데이터"를 만들기 때문에 계산적 해석과 완전히 정반대인 선택 원리를 정의할 수 있습니다. 그 용도는 몇몇 고전적 생성에 필수적입니다. 그리고 사용자는 그것이 필요할 때 불러오기 할 수있습니다. 그러나 데이터를 만들기 위해 이 구성을 사용한 표현식은 계산적 내용을 없으며, 우리는 린에서 이러한 정의를 ``noncomputable``로 표시하여 해당 사실을 나타내도록 요구받습니다.

Diaconescu의 정리로 알려진 영리한 트릭을 사용하여 명제 확장성, 함수 확장성 및 배중률의 법칙을 유도하는 선택을 사용할 수 있습니다. 그러나 위에서 언급한 대로 여전히 배중률의 사용은 다른 고전 원리처럼 데이터를 만드는데 이들이 사용되지만 않는다면 바이트 코드 컴파일 및 코드 추출과 호환됩니다.

요약하자면 표준 라이브러리는 유형 세계, 종속 함수 유형과 귀납형의 기반 프레임워크 위에 세 가지 구성요소를 더합니다.

- 명제 확장성 공리
- 함수 확장성을 함의하는 몫 구성
- 존재 명제로부터 데이터를 만들어내는 선택 원리

이들 중 첫 두 개는 린에서 정규화를 막습니다. 그러나 바이트 코드 평가와 상용되며 반면 세 번째는 계산 해석으로 수정할 수 없습니다. 아래에서 상세한 부분을 더 자세히 말할 것입니다.

역사적이고 철학적인 맥락
------------------------------------

대부분의 역사에서 수학은 본래 계산적이었습니다. 기하학은 기하학적 물체의 구성을 다뤘고, 대수학은 연립방정식의 산술적 해에 관해서 그리고 해석학은 시간의 흐름에 따른 시스템의 향후 거동을 계산하는 수단을 제공했습니다. "모든 ``x``에 대해 ...인 ``y``가 있다"는 정리의 증명에서부터 효과까지, 주어진 ``x``에 대해 그런 ``y``를 계산하는 알고리즘을 추출하는 것은 보통 직관적이었습니다.

그러나 19세기에 수학적 논쟁의 복잡성이 증가함에 따라 수학자들은 알고리즘적 정보를 억제하고 어떻게 이 대상이 표현되는지에 대한 상세함을 추상화시키고 수학적 대상의 설명을 일으키는 새로운 형식의 논리를 만들도록 몰아붙였습니다. 목표는 계산의 세부 사항에 얽매이지 않고 강력한 "개념적" 이해를 얻는 것이지만 직접 계산을 해석하는데 단지 *거짓*인 수학적 정리를 인정하는 효과가 있었습니다.

계산이 수학에 중요하다는 것에 오늘날에도 여전히 꽤 균등한 합의가 있습니다. 그러나 어떻게 계산적 문제를 가장 잘 다루는가에 대해서는 다양한 견해가 있습니다. *직관주의적* 관점에서, 수학을 그것의 계산적 뿌리로부터 나누는 것은 실수입니다. 모든 의미 있는 수학 정리는 직접적인 계산 해석을 가져야 합니다. *고전주의적* 관점에서 관심사를 나눠두는 것은 더 유익합니다. 비직관주의적 이론과 그들에 대한 추론 방법을 쓰는 자유는 내버려두면서 우리는 한 언어와 방법의 몸체를 사용해 컴퓨터 프로그램을 작성합니다. 린은 이 두 접근 모두 지원하도록 설계되었습니다. 라이브러리의 핵심 부분은 직관주의적으로 개발되었지만 시스템은 고전적인 수학추론을 수행하기 위한 지원도 제공합니다.

계산적으로 종속 유형론의 가장 순수한 부분은 완전히 ``Prop``의 사용을 피합니다. 귀납형과 의존 함수 유형은 데이터 유형으로 볼 수 있고, 이들 유형의 항은 더 이상 적용할 규칙이 없을 때까지 제거 규칙을 적용함으로써 "평가"될 수 있습니다. 원리상 임의의 닫힌 항(즉, 자유 변수가 없는 항)의 유형 ``Nat``은 수치값 ``succ(... (succ zero)...)``으로 평가되어야 합니다.

증명에 무관한 ``Prop``을 도입하는 것과 정리가 축약 불가함을 표시하는 것은 문제의 분리를 위한 첫 단계를 나타냅니다. 의도는 ``p : Prop``형의 원소가 계산에서 아무 역할도 하지 않아야 한다는 것입니다. 그래서 특히 항 ``t : p``의 생성은 이 관점에 의해 "무관"합니다. 어떤 이는 여전히 ``Prop``형 원소를 포함하는 계산적 대상을 정의할 수 있습니다. 요점은 이 원소는 계산의 효과에 대해 추론하는 것을 돕지만 항으로부터 "코드"를 추출할 때 무시될 수 있다는 것입니다. 하지만 ``Prop``형 원소는 완전히 무해하지 않습니다. 이들은 임의의 ``α``형에 대한 방정식 ``s = t : α``을 포함하고 그 방정식은 형변환 항의 유형 확인에 사용될 수 있습니다. 아래에서 우리는 어떻게 이런 형변환이 시스템에서 계산을 막을 수 있는지 볼 것입니다. 그러나 명제적 내용은 삭제하고, 중간의 작성된 제약을 무시하고, 이들이 평범한 형태에 도달할 때까지 항을 축소하는 평가 과정 하에서 계산은 여전히 가능합니다. 이는 정확히 린의 가상 머신이 하는 일입니다.

증명 무관한 ``Prop``를 도입하였다면 어떤 이는 예를 들어 ``p`` 가 임의의 명제일 때 이것이 배중률 ``p ∨ ¬p``을 사용해도 적법한지 고려할 지 모릅니다. 당연히 이것도 CIC의 규칙에 따라 계산이 막힙니다. 그러나 위에서 설명했듯이 이것은 바이트 코드 평가를 막지 않습니다. 이론의 증명 무관함과 데이터 연관 부분 사이의 구별을 완전히 지우는 :numref:`선택`에서 논의된 선택 원리입니다.

명제 확장성
----------------------------

명제 확장성은 다음 공리입니다.
```lean
# namespace Hidden
axiom propext {a b : Prop} : (a ↔ b) → a = b
# end Hidden
```

그것은 두 명제가 서로를 함의할 때 그들은 실제로 동등하다고 주장합니다. 이것은 어떤 원소 ``a : Prop``가 비었거나 어떤 구별된 원소 ``*``에 대한 단일 개체 집합 ``{*}``이라는 집합론적인 해석과 일관됩니다. 공리는 동등한 명제는 임의의 맥락 속에서 서로를 대체할 수 있다는 효과를 갖습니다.

```lean
theorem thm₁ (a b c d e : Prop) (h : a ↔ b) : (c ∧ a ∧ d → e) ↔ (c ∧ b ∧ d → e) :=
  propext h ▸ Iff.refl _

theorem thm₂ (a b : Prop) (p : Prop → Prop) (h : a ↔ b) (h₁ : p a) : p b :=
  propext h ▸ h₁
```

<!--
The first example could be proved more laboriously without ``propext``
using the fact that the propositional connectives respect
propositional equivalence. The second example represents a more
essential use of ``propext``. In fact, it is equivalent to ``propext``
itself, a fact which we encourage you to prove.

Given any definition or theorem in Lean, you can use the ``#print
axioms`` command to display the axioms it depends on.

.. code-block:: lean

    variables a b c d e : Prop
    variable p : Prop → Prop

    theorem thm₁ (h : a ↔ b) : (c ∧ a ∧ d → e) ↔ (c ∧ b ∧ d → e) :=
    propext h ▸ iff.refl _

    theorem thm₂ (h : a ↔ b) (h₁ : p a) : p b :=
    propext h ▸ h₁

    -- BEGIN
    #print axioms thm₁  -- propext
    #print axioms thm₂  -- propext
    -- END
-->

함수 확장성
-----------------------

명제 확장성과 비슷하게 함수 확장성은 그들의 모든 입력에 대해 동의하는 ``(x : α) → β x``형인 임의의 두 함수가 동일하다는 주장입니다.

```lean
universe u v
#check (@funext :
           {α : Type u}
         → {β : α → Type u}
         → {f g : (x : α) → β x}
         → (∀ (x : α), f x = g x)
         → f = g)

#print funext
```

고전적인 집합론적 관점에서, 이것은 정확히 두 함수가 동일하다는 의미입니다. 이것을 함수의 "확장된" 관점이라 합니다. 그러나 직관주의적 관점에서 볼 때 함수를 명시적으로 제공되는 알고리즘 또는 컴퓨터 프로그램으로 생각하는 것이 더 자연스러운 경우가 있습니다. 두 개의 컴퓨터 프로그램이 구문론적으로 상당히 다르다는 사실에도 불구하고 모든 입력에 대해 동일한 답을 계산할 수 있는 경우가 확실히 있습니다. 거의 같은 방식으로 동일한 입력/출력 동작을 갖는 두 함수를 식별하도록 강요하지 않는 함수 관점를 유지하기를 원할 수 있습니다. 이것을 함수에 대한 "의도적" 관점이라 합니다.

사실, 함수 확장성은 다음 섹션에서 설명하는 몫의 존재에서 비롯됩니다. 그러므로 린 표준 라이브러리에서 ``funext``는 [몫 생성으로부터 증명됩니다.](https://github.com/leanprover/lean4/blob/master/src/Init/Core.lean)

``α : Type``에 대해 본질적으로 술어를 갖는 부분집합을 식별하는 ``α``의 부분집합 유형을 나타내기 위해 ``Set α:= α → Prop``을 정의한다고 합시다. ``funext``와 ``propext``를 결합하여 이러한 집합의 확장 이론을 얻습니다.

```lean
def Set (α : Type u) := α → Prop

namespace Set

def mem (x : α) (a : Set α) := a x

infix:50 "∈" => mem

theorem setext {a b : Set α} (h : ∀ x, x ∈ a ↔ x ∈ b) : a = b :=
  funext (fun x => propext (h x))

end Set
```

그런 뒤 공집합과 교집합을 정의하고 집합 항등식을 증명해 나갈 수 있습니다.

```lean
# def Set (α : Type u) := α → Prop
# namespace Set
# def mem (x : α) (a : Set α) := a x
# infix:50 "∈" => mem
# theorem setext {a b : Set α} (h : ∀ x, x ∈ a ↔ x ∈ b) : a = b :=
#  funext (fun x => propext (h x))
def empty : Set α := fun x => False

notation (priority := high) "∅" => empty

def inter (a b : Set α) : Set α :=
  fun x => x ∈ a ∧ x ∈ b

infix:70 " ∩ " => inter

theorem inter_self (a : Set α) : a ∩ a = a :=
  setext fun x => Iff.intro
    (fun ⟨h, _⟩ => h)
    (fun h => ⟨h, h⟩)

theorem inter_empty (a : Set α) : a ∩ ∅ = ∅ :=
  setext fun x => Iff.intro
    (fun ⟨_, h⟩ => h)
    (fun h => False.elim h)

theorem empty_inter (a : Set α) : ∅ ∩ a = ∅ :=
  setext fun x => Iff.intro
    (fun ⟨h, _⟩ => h)
    (fun h => False.elim h)

theorem inter.comm (a b : Set α) : a ∩ b = b ∩ a :=
  setext fun x => Iff.intro
    (fun ⟨h₁, h₂⟩ => ⟨h₂, h₁⟩)
    (fun ⟨h₁, h₂⟩ => ⟨h₂, h₁⟩)
# end Set
```

다음은 어떻게 함수 확장이 린 커널 속에서 계산을 막는지에 대한 예입니다.

```lean
def f (x : Nat) := x
def g (x : Nat) := 0 + x

theorem f_eq_g : f = g :=
  funext fun x => (Nat.zero_add x).symm

def val : Nat :=
  Eq.recOn (motive := fun _ _ => Nat) f_eq_g 0

-- does not reduce to 0
#reduce val

-- evaluates to 0
#eval val
```

먼저 두 함수 ``f``와 ``g``가 함수 확장성을 사용하여 동일함을 보여주고 유형에서 ``f``를 ``g``로 대체하여 ``Nat``형의 ``0``을 형변환합니다. 물론 ``Nat``는 ``f``에 의존하지 않기 때문에 캐스트는 무의미합니다. 그러나 그것으로 피해를 입히기에 충분합니다. 우린 시스템의 계산 규칙에 따라 이제 숫치값으로 줄어들지 않는 ``Nat``의 닫힌 항을 갖습니다. 이 경우 식을 ``0``으로 줄이고 싶을 수 있습니다. 그러나 자명하지 않은 예에서 형변환를 제거하는 것은 항의 유형을 변경하여 표현식 주변의 유형이 올바르지 않을 수 있습니다. 하지만 가상 머신은 식을 ``0``으로 평가하는 데 문제가 없습니다. 다음은 마찬가지로 어떻게 ``propext``가 방해할 수 있는지를 보여주도록 고안된 예입니다.

```lean
theorem tteq : (True ∧ True) = True :=
  propext (Iff.intro (fun ⟨h, _⟩ => h) (fun h => ⟨h, h⟩))

def val : Nat :=
  Eq.recOn (motive := fun _ _ => Nat) tteq 0

-- does not reduce to 0
#reduce val

-- evaluates to 0
#eval val
```

*관찰 유형 이론* 및 *입방 유형 이론*에 대한 작업을 포함한 현재 연구 프로그램은 함수 확장성, 몫 등을 포함하는 형변환에 대한 축소를 허용하는 방식으로 유형론을 확장하는 것을 목표로 합니다. 그러나 해법은 그렇게 명확하지 않으며 Lean의 기반 계산 규칙은 그러한 축소를 승인하지 않습니다.

그러나 어떤 의미에서 형변환는 표현식의 의미를 변경하지 않습니다. 오히려 표현식의 유형에 대해 추론하는 메커니즘입니다. 적절한 의미가 주어지면, 축소 유형을 올바르게 만드는 데 필요한 중간 장부를 무시하면서 항의 의미를 보존하는 방식으로 항를 줄이는 것이 합리적입니다. 이 경우 ``Prop``에 새로운 공리를 추가하는 것은 중요하지 않습니다. 증명 무관성에 의해 ``Prop``의 표현식은 정보를 전달하지 않으며 축소 절차에서 안전하게 무시될 수 있습니다.

몫
---------

``α``를 임의의 유형이라고 하고 ``r``이 ``α``과 동등한 관계라고 합시다. "몫" ``α / r``, 즉 ``α`` "나머지 연산(modulo)" ``r``의 원소 유형을 형성하는 것은 수학적으로 흔합니다. 집합론적으로 ``α / r``을  ``α`` 모듈로 ``r``의 클래스와 동등한 집합으로 볼 수 있습니다. ``f : α → β``가 모든 ``x y : α``에 대해 ``r x y``가 ``f x = f y``를 함의하면 ``f``이다를 의미하는 등가 관계에 대한 함수인 경우, ``f' ⟦x⟧ = f x``에 의해 각 등가 클래스 ``⟦x⟧``에 정의된 함수 ``f': α / r → β``로 "상승"합니다. Lean의 표준 라이브러리는 이 생성을 정확히 수행하는 추가 상수로 직관주의적 계산을 확장하고 이 마지막 방정식을 정의로 인한 축소 규칙으로 설치합니다.

가장 기본적인 형태의 몫 생성은 ``r``이 등가 관계일 필요 조차 요구하지 않습니다. 다음 상수들은 린에 내장되었습니다.

```lean
# namespace Hidden
universe u v

axiom Quot : {α : Sort u} → (α → α → Prop) → Sort u

axiom Quot.mk : {α : Sort u} → (r : α → α → Prop) → α → Quot r

axiom Quot.ind :
    ∀ {α : Sort u} {r : α → α → Prop} {β : Quot r → Prop},
      (∀ a, β (Quot.mk r a)) → (q : Quot r) → β q

axiom Quot.lift :
    {α : Sort u} → {r : α → α → Prop} → {β : Sort u} → (f : α → β)
    → (∀ a b, r a b → f a = f b) → Quot r → β
# end Hidden
```

첫 번째 것은 ``α``에 대한 ``r``과의 이항 관계에 의해 ``α``형이 주어지면 ``Quot r``형을 형성합니다. 두 번째는 ``α``를 ``Quot α``로 대응하여서 ``r : α → α → Prop`` 및 ``a : α``이면 , ``Quot.mk r a``는 ``Quot r``의 원소입니다.. 세 번째 원칙인 ``Quot.ind``는 ``Quot.mk r a``의 모든 원소가 이 같은 꼴이라고 말합니다.  ``Quot.lift``의 경우, 함수 ``f : α → β``가 주어지고 ``h``가 ``f`` 관계 ``r``에 대한 함수이면 ``Quot.lift f h``는 ``Quot r``로 대응하는 함수입니다. 아이디어는 ``α``의 각 원소 ``a``에 대해 함수 ``Quot.lift f h``가 ``Quot.mk r a`` (``a``를 포함하는 ``r``-클래스)를  ``f a``로 대응합니다. 여기서 ``h``는 이 함수가 잘 정의되었음을 나타냅니다. 사실, 계산 원리는 아래 증명이 명확하게 하는 것처럼 축소 규칙으로 선언됩니다.

```lean
def mod7Rel (x y : Nat) : Prop :=
  x % 7 = y % 7

-- the quotient type
#check (Quot mod7Rel : Type)

-- the class of a
#check (Quot.mk mod7Rel 4 : Quot mod7Rel)

def f (x : Nat) : Bool :=
   x % 7 = 0

theorem f_respects (a b : Nat) (h : mod7Rel a b) : f a = f b := by
  simp [mod7Rel, f] at *
  rw [h]

#check (Quot.lift f f_respects : Quot mod7Rel → Bool)

-- the computation principle
example (a : Nat) : Quot.lift f f_respects (Quot.mk mod7Rel a) = f a :=
  rfl
```

네 가지 상수 ``Quot``, ``Quot.mk``, ``Quot.ind`` 및 ``Quot.lift`` 자체는 그다지 매우 강하지 않습니다. ``Quot r``을 단순히 ``α``로 취하고 ``Quot.lift``을 항등함수로 취하면 (``h`` 무시) ``Quot.ind``가 만족되는지 확인할 수 있습니다. 이러한 이유로 다음 네 개의 상수는 추가적인 공리로 간주되지 않습니다.

<!--
    variables α β : Type
    variable  r : α → α → Prop
    variable  a : α
    variable  f : α → β
    variable   h : ∀ a₁ a₂, r a₁ a₂ → f a₁ = f a₂
    theorem thm : quot.lift f h (quot.mk r a) = f a := rfl
    -- BEGIN
    #print axioms thm   -- no axioms
    -- END
-->

그것들은 귀납적으로 정의된 유형과 관련 생성자와 재귀자처럼 논리적 프레임워크의 일부로 간주됩니다.

``Quot`` 생성을 진정한 몫으로 만드는 것은 다음과 같은 추가 공리입니다.

```lean
# namespace Hidden
# universe u v
axiom Quot.sound :
      ∀ {α : Type u} {r : α → α → Prop} {a b : α},
        r a b → Quot.mk r a = Quot.mk r b
# end Hidden
```

이것은 ``r``과 관련된 ``α``의 임의의 두 원소가 몫에서 식별된다는 것을 주장하는 공리입니다. 정리 또는 정의가 ``Quot.sound``를 사용하는 경우 ``#print axioms`` 명령 위에 표시됩니다.

물론 몫 생성은 ``r``이 등가 관계인 상황에서 가장 흔히 사용됩니다. 위와 같이 ``r``이 주어지면 ``r' a b``이 ``Quot.mk r a = Quot.mk r b``와 동등관계라는 규칙에 따라 ``r'``을 정의하면, ``r'``이 등가 관계임이 분명합니다. 실제로 ``r'``은 함수 ``a ↦ quot.mk r a``의 *커널*입니다.  공리 ``Quot.sound``는 ``r a b``가 ``r' b``를 함의한다고 합니다. ``r''``이 ``r``을 포함하는 임의의 등가 관계이면 ``r' a b``는 ``r'' a b``를 함의한다는 점에서 ``Quot.lift`` 및 ``Quot.ind``를 사용하여 ``r'``이 ``r``을 포함하는 가장 작은 등가 관계임을 보여줄 수 있습니다. 특히, ``r``이 첫 등가 관계라면 모든 ``a``와 ``b``에 대해 ``r a b``는 ``r' b``와 동등하다가 있습니다.

이 일반적인 사용 사례를 지원하기 위해 표준 라이브러리는 단순히 연관된 등가 관계가 있는 유형인 *setoid* 개념을 정의합니다.

```lean
# namespace Hidden
class Setoid (α : Sort u) where
  r : α → α → Prop
  iseqv {} : Equivalence r

instance {α : Sort u} [Setoid α] : HasEquiv α :=
  ⟨Setoid.r⟩

namespace Setoid

variable {α : Sort u} [Setoid α]

theorem refl (a : α) : a ≈ a :=
  (Setoid.iseqv α).refl a

theorem symm {a b : α} (hab : a ≈ b) : b ≈ a :=
  (Setoid.iseqv α).symm hab

theorem trans {a b c : α} (hab : a ≈ b) (hbc : b ≈ c) : a ≈ c :=
  (Setoid.iseqv α).trans hab hbc

end Setoid
# end Hidden
```

어떤 ``α``형에 대한 관계 ``r`` 및 ``r``와 등가 관계인 증명 ``p``가 주어지면 ``Setoid.mk p``를 setoid 클래스의 개체로 정의할 수 있습니다.

```lean
# namespace Hidden
def Quotient {α : Sort u} (s : Setoid α) :=
  @Quot α Setoid.r
# end Hidden
```

상수 ``Quotient.mk``, ``Quotient.ind``, ``Quotient.lift``와 ``Quotient.sound``는 ``Quot``의 언소에 대응하는 특수화일 뿐입니다. 유형 클래스 추론이 ``α``형과 연관된 setoid를 찾을 수 있다는 사실은 많은 이점을 가져옵니다. 먼저 ``Setoid.r a b``에 대해 ``a ≈ b``(``\approx``로 입력) 표기법을 사용할 수 있습니다. 여기서 ``Setoid``의 개체는 ``Setoid.r`` 표기법에 내포되어 있습니다. 일반 정리 ``Setoid.refl``, ``Setoid.symm``, ``Setoid.trans``를 사용하여 관계를 추론할 수 있습니다. 특히 몫과 함께 ``Quot.mk Setoid.r``에 대한 일반 표기법 ``⟦a⟧``를 사용할 수 있습니다. 여기서 ``Setoid``의 개체는 표기법 ``Setoid.r`` 및 정리 ``Quotient.exact``에 암시되어 있습니다.

```lean
# universe u
#check (@Quotient.exact :
         ∀ {α : Sort u} {s : Setoid α} {a b : α},
           Quotient.mk s a = Quotient.mk s b → a ≈ b)
```

``Quotient.sound``와 함께 이것은 몫의 요소가 ``α`` 속 원소의 등가 클래스와 정확히 일치한다는 것을 의미합니다.

표준 라이브러리에서 ``α × β``는 ``α`` 및 ``β`` 형의 데카르트 곱을 나타냅니다. 몫의 사용을 설명하기 위해 ``α`` 형의 *순서 없는* 순서쌍 유형을 ``α × α`` 형의 몫으로 정의합시다. 먼저 연관 등가 관계를 정의합니다.

```lean
private def eqv (p₁ p₂ : α × α) : Prop :=
  (p₁.1 = p₂.1 ∧ p₁.2 = p₂.2) ∨ (p₁.1 = p₂.2 ∧ p₁.2 = p₂.1)

infix:50 " ~ " => eqv
```

다음 단계는 ``eqv``가 실제로 등가 관계, 즉 반사적, 대칭적, 추이적임을 증명하는 것입니다. 종속 패턴 매칭를 사용하여 사례 분석을 수행하고 가정을 여러 부분으로 나눈 다음 재조합하여 결론을 도출함으로써 이 세 가지 사실을 편리하고 가독성 있는 방식으로 증명할 수 있습니다.

```lean
# private def eqv (p₁ p₂ : α × α) : Prop :=
#  (p₁.1 = p₂.1 ∧ p₁.2 = p₂.2) ∨ (p₁.1 = p₂.2 ∧ p₁.2 = p₂.1)
# infix:50 " ~ " => eqv
private theorem eqv.refl (p : α × α) : p ~ p :=
  Or.inl ⟨rfl, rfl⟩

private theorem eqv.symm  : ∀ {p₁ p₂ : α × α}, p₁ ~ p₂ → p₂ ~ p₁
  | (a₁, a₂), (b₁, b₂), (Or.inl ⟨a₁b₁, a₂b₂⟩) =>
    Or.inl (by simp_all)
  | (a₁, a₂), (b₁, b₂), (Or.inr ⟨a₁b₂, a₂b₁⟩) =>
    Or.inr (by simp_all)

private theorem eqv.trans : ∀ {p₁ p₂ p₃ : α × α}, p₁ ~ p₂ → p₂ ~ p₃ → p₁ ~ p₃
  | (a₁, a₂), (b₁, b₂), (c₁, c₂), Or.inl ⟨a₁b₁, a₂b₂⟩, Or.inl ⟨b₁c₁, b₂c₂⟩ =>
    Or.inl (by simp_all)
  | (a₁, a₂), (b₁, b₂), (c₁, c₂), Or.inl ⟨a₁b₁, a₂b₂⟩, Or.inr ⟨b₁c₂, b₂c₁⟩ =>
    Or.inr (by simp_all)
  | (a₁, a₂), (b₁, b₂), (c₁, c₂), Or.inr ⟨a₁b₂, a₂b₁⟩, Or.inl ⟨b₁c₁, b₂c₂⟩ =>
    Or.inr (by simp_all)
  | (a₁, a₂), (b₁, b₂), (c₁, c₂), Or.inr ⟨a₁b₂, a₂b₁⟩, Or.inr ⟨b₁c₂, b₂c₁⟩ =>
    Or.inl (by simp_all)

private theorem is_equivalence : Equivalence (@eqv α) :=
   { refl := eqv.refl, symm := eqv.symm, trans := eqv.trans }
```

``eqv``가 등가 관계임을 증명했으므로 ``Setoid(α × α)``를 구성하고 이를 사용하여 순서가 없는 쌍 ``UProd α``형을 정의할 수 있습니다.

```lean
# private def eqv (p₁ p₂ : α × α) : Prop :=
#  (p₁.1 = p₂.1 ∧ p₁.2 = p₂.2) ∨ (p₁.1 = p₂.2 ∧ p₁.2 = p₂.1)
# infix:50 " ~ " => eqv
# private theorem eqv.refl (p : α × α) : p ~ p :=
#  Or.inl ⟨rfl, rfl⟩
# private theorem eqv.symm  : ∀ {p₁ p₂ : α × α}, p₁ ~ p₂ → p₂ ~ p₁
#   | (a₁, a₂), (b₁, b₂), (Or.inl ⟨a₁b₁, a₂b₂⟩) =>
#     Or.inl (by simp_all)
#   | (a₁, a₂), (b₁, b₂), (Or.inr ⟨a₁b₂, a₂b₁⟩) =>
#     Or.inr (by simp_all)
# private theorem eqv.trans : ∀ {p₁ p₂ p₃ : α × α}, p₁ ~ p₂ → p₂ ~ p₃ → p₁ ~ p₃
#   | (a₁, a₂), (b₁, b₂), (c₁, c₂), Or.inl ⟨a₁b₁, a₂b₂⟩, Or.inl ⟨b₁c₁, b₂c₂⟩ =>
#     Or.inl (by simp_all)
#   | (a₁, a₂), (b₁, b₂), (c₁, c₂), Or.inl ⟨a₁b₁, a₂b₂⟩, Or.inr ⟨b₁c₂, b₂c₁⟩ =>
#     Or.inr (by simp_all)
#   | (a₁, a₂), (b₁, b₂), (c₁, c₂), Or.inr ⟨a₁b₂, a₂b₁⟩, Or.inl ⟨b₁c₁, b₂c₂⟩ =>
#     Or.inr (by simp_all)
#   | (a₁, a₂), (b₁, b₂), (c₁, c₂), Or.inr ⟨a₁b₂, a₂b₁⟩, Or.inr ⟨b₁c₂, b₂c₁⟩ =>
#     Or.inl (by simp_all)
# private theorem is_equivalence : Equivalence (@eqv α) :=
#   { refl := eqv.refl, symm := eqv.symm, trans := eqv.trans }
instance uprodSetoid (α : Type u) : Setoid (α × α) where
   r     := eqv
   iseqv := is_equivalence

def UProd (α : Type u) : Type u :=
  Quotient (uprodSetoid α)

namespace UProd

def mk {α : Type} (a₁ a₂ : α) : UProd α :=
  Quotient.mk' (a₁, a₂)

notation "{ " a₁ ", " a₂ " }" => mk a₁ a₂

end UProd
```

순서쌍에 대한 표기 ``{a₁, a₂}``을 지역적으로 ``Quotient.mk (a₁, a₂)``로 정의합니다. 이것은 설명 목적으로 유용하지만 일반적으로 이 표기법이 레코드 및 집합 같은 중괄호의 다른 용도를 가리기 때문에 일반적으로 좋은 생각은 아닙니다.

``(a₁, a₂) ~ (a₂, a₁)``를 갖기 때문에 ``quot.sound``을 사용해 ``{a₁, a₂} = {a₂, a₁}``을 쉽게 증명할 수 있습니다.

```lean
# private def eqv (p₁ p₂ : α × α) : Prop :=
#  (p₁.1 = p₂.1 ∧ p₁.2 = p₂.2) ∨ (p₁.1 = p₂.2 ∧ p₁.2 = p₂.1)
# infix:50 " ~ " => eqv
# private theorem eqv.refl (p : α × α) : p ~ p :=
#  Or.inl ⟨rfl, rfl⟩
# private theorem eqv.symm  : ∀ {p₁ p₂ : α × α}, p₁ ~ p₂ → p₂ ~ p₁
#   | (a₁, a₂), (b₁, b₂), (Or.inl ⟨a₁b₁, a₂b₂⟩) =>
#     Or.inl (by simp_all)
#   | (a₁, a₂), (b₁, b₂), (Or.inr ⟨a₁b₂, a₂b₁⟩) =>
#     Or.inr (by simp_all)
# private theorem eqv.trans : ∀ {p₁ p₂ p₃ : α × α}, p₁ ~ p₂ → p₂ ~ p₃ → p₁ ~ p₃
#   | (a₁, a₂), (b₁, b₂), (c₁, c₂), Or.inl ⟨a₁b₁, a₂b₂⟩, Or.inl ⟨b₁c₁, b₂c₂⟩ =>
#     Or.inl (by simp_all)
#   | (a₁, a₂), (b₁, b₂), (c₁, c₂), Or.inl ⟨a₁b₁, a₂b₂⟩, Or.inr ⟨b₁c₂, b₂c₁⟩ =>
#     Or.inr (by simp_all)
#   | (a₁, a₂), (b₁, b₂), (c₁, c₂), Or.inr ⟨a₁b₂, a₂b₁⟩, Or.inl ⟨b₁c₁, b₂c₂⟩ =>
#     Or.inr (by simp_all)
#   | (a₁, a₂), (b₁, b₂), (c₁, c₂), Or.inr ⟨a₁b₂, a₂b₁⟩, Or.inr ⟨b₁c₂, b₂c₁⟩ =>
#     Or.inl (by simp_all)
# private theorem is_equivalence : Equivalence (@eqv α) :=
#   { refl := eqv.refl, symm := eqv.symm, trans := eqv.trans }
# instance uprodSetoid (α : Type u) : Setoid (α × α) where
#    r     := eqv
#    iseqv := is_equivalence
# def UProd (α : Type u) : Type u :=
#   Quotient (uprodSetoid α)
# namespace UProd
# def mk {α : Type} (a₁ a₂ : α) : UProd α :=
#   Quotient.mk' (a₁, a₂)
# notation "{ " a₁ ", " a₂ " }" => mk a₁ a₂
theorem mk_eq_mk (a₁ a₂ : α) : {a₁, a₂} = {a₂, a₁} :=
  Quot.sound (Or.inr ⟨rfl, rfl⟩)
# end UProd
```

예제를 끝내기 위해 ``a : α`` 및 ``u : uprod α``가 주어졌을 때, ``a``는 순서가 지정되지 않은 쌍 ``u``의 원소 중 하나이면 성립해야 하는 명제 ``a ∈ u``를 정의합니다. 먼저 (순서 있는) 쌍에 대해 유사한 명제 ``mem_fn a u``를 정의합니다. 그 뒤 ``mem_fn``이 보조 정리 ``mem_respects``와 등가 관계 ``eqv``를 존중한다는 것을 보여줍니다. 이것은 린 표준 라이브러리에서 광범위하게 사용되는 관용구입니다.

```lean
# private def eqv (p₁ p₂ : α × α) : Prop :=
#  (p₁.1 = p₂.1 ∧ p₁.2 = p₂.2) ∨ (p₁.1 = p₂.2 ∧ p₁.2 = p₂.1)
# infix:50 " ~ " => eqv
# private theorem eqv.refl (p : α × α) : p ~ p :=
#  Or.inl ⟨rfl, rfl⟩
# private theorem eqv.symm  : ∀ {p₁ p₂ : α × α}, p₁ ~ p₂ → p₂ ~ p₁
#   | (a₁, a₂), (b₁, b₂), (Or.inl ⟨a₁b₁, a₂b₂⟩) =>
#     Or.inl (by simp_all)
#   | (a₁, a₂), (b₁, b₂), (Or.inr ⟨a₁b₂, a₂b₁⟩) =>
#     Or.inr (by simp_all)
# private theorem eqv.trans : ∀ {p₁ p₂ p₃ : α × α}, p₁ ~ p₂ → p₂ ~ p₃ → p₁ ~ p₃
#   | (a₁, a₂), (b₁, b₂), (c₁, c₂), Or.inl ⟨a₁b₁, a₂b₂⟩, Or.inl ⟨b₁c₁, b₂c₂⟩ =>
#     Or.inl (by simp_all)
#   | (a₁, a₂), (b₁, b₂), (c₁, c₂), Or.inl ⟨a₁b₁, a₂b₂⟩, Or.inr ⟨b₁c₂, b₂c₁⟩ =>
#     Or.inr (by simp_all)
#   | (a₁, a₂), (b₁, b₂), (c₁, c₂), Or.inr ⟨a₁b₂, a₂b₁⟩, Or.inl ⟨b₁c₁, b₂c₂⟩ =>
#     Or.inr (by simp_all)
#   | (a₁, a₂), (b₁, b₂), (c₁, c₂), Or.inr ⟨a₁b₂, a₂b₁⟩, Or.inr ⟨b₁c₂, b₂c₁⟩ =>
#     Or.inl (by simp_all)
# private theorem is_equivalence : Equivalence (@eqv α) :=
#   { refl := eqv.refl, symm := eqv.symm, trans := eqv.trans }
# instance uprodSetoid (α : Type u) : Setoid (α × α) where
#    r     := eqv
#    iseqv := is_equivalence
# def UProd (α : Type u) : Type u :=
#   Quotient (uprodSetoid α)
# namespace UProd
# def mk {α : Type} (a₁ a₂ : α) : UProd α :=
#   Quotient.mk' (a₁, a₂)
# notation "{ " a₁ ", " a₂ " }" => mk a₁ a₂
# theorem mk_eq_mk (a₁ a₂ : α) : {a₁, a₂} = {a₂, a₁} :=
#   Quot.sound (Or.inr ⟨rfl, rfl⟩)

private def mem_fn (a : α) : α × α → Prop
  | (a₁, a₂) => a = a₁ ∨ a = a₂

--mem_respects를 증명하기 위한 보조 정리 mem_swap {a : α}:
      ∀ {p : α × α}, mem_fn a p = mem_fn a (⟨p.2, p.1⟩)
  | (a₁, a₂) => by
    apply propext
    apply Iff.intro
    . intro
      | Or.inl h => exact Or.inr h
      | Or.inr h => exact Or.inl h
    . intro
      | Or.inl h => exact Or.inr h
      | Or.inr h => exact Or.inl h


private theorem mem_respects
      : {p₁ p₂ : α × α} → (a : α) → p₁ ~ p₂ → mem_fn a p₁ = mem_fn a p₂
  | (a₁, a₂), (b₁, b₂), a, Or.inl ⟨a₁b₁, a₂b₂⟩ => by simp_all
  | (a₁, a₂), (b₁, b₂), a, Or.inr ⟨a₁b₂, a₂b₁⟩ => by simp_all; apply mem_swap

def mem (a : α) (u : UProd α) : Prop :=
  Quot.liftOn u (fun p => mem_fn a p) (fun p₁ p₂ e => mem_respects a e)

infix:50 " ∈ " => mem

theorem mem_mk_left (a b : α) : a ∈ {a, b} :=
  Or.inl rfl

theorem mem_mk_right (a b : α) : b ∈ {a, b} :=
  Or.inr rfl

theorem mem_or_mem_of_mem_mk {a b c : α} : c ∈ {a, b} → c = a ∨ c = b :=
  fun h => h
# end UProd
```

편의를 위해 표준 라이브러리는 이진 함수를 들어 올리는 ``Quotient.lift₂``와 두 변수에 대한 귀납를 위한 ``Quotient.ind₂``도 정의합니다.

몫 구성이 함수 확장성을 의미하는 이유에 대한 몇 가지 힌트로 이 섹션을 마무리합니다. ``(x : α) → β x``에 대한 확장적 동등성이 등가 관계임을 보여주는 것은 어렵지 않으므로  "동등할 때까지" 함수 ``extfun α β``형을 고려할 수 있습니다. 물론 함수 적용은 ``f₁``가 ``f₂``와 동등하면 ``f₁ a``가 ``f₂ a``와 같다는 의미에서 등가를 존중합니다. 따라서 함수 적용은 함수 ``extfun_app : extfun α β → (x : α) → β x``를 발생시킵니다. 그러나 모든 ``f``에 대해 ``extfun_app ⟦f⟧``는 정의상으로 ``fun x => f x``와 동일하며, 이는 다시 정의상으로 ``f``과 같습니다. 그래서 ``f₁``와 ``f₂``가 외연적으로 동일할 때 다음과 같은 등식 연결을 갖습니다.

```
    f₁ = extfun_app ⟦f₁⟧ = extfun_app ⟦f₂⟧ = f₂
```

결과적으로 ``f₁``는 ``f₂``와 같습니다.

선택(Choice)
------

표준 라이브러리에 정의된 최종 공리를 기술하려면 다음과 같이 정의되는 ``Nonempty``형이 필요합니다.

```lean
# namespace Hidden
class inductive Nonempty (α : Sort u) : Prop where
  | intro (val : α) : Nonempty α
# end Hidden
```

``Nonempty α``에는 ``Prop`` 유형이 있고 생성자에 데이터가 포함되어 있기 때문에 ``Prop``으로만 제거할 수 있습니다.
실제로 ``Nonempty α``는 ``∃ x : α, True``와 동일합니다.

```lean
example (α : Type u) : Nonempty α ↔ ∃ x : α, True :=
  Iff.intro (fun ⟨a⟩ => ⟨a, trivial⟩) (fun ⟨a, h⟩ => ⟨a⟩)
```

우리의 선택 공리는 이제 다음과 같이 간단히 표현됩니다.


```lean
# namespace Hidden
# universe u
axiom choice {α : Sort u} : Nonempty α → α
# end Hidden
```

``α``가 비어 있지 않다는 주장 ``h``만 주어지면 ``choice h``는 마술처럼 ``α``의 원소를 생성합니다. 물론 이것은 의미 있는 계산을 막습니다. ``Prop``의 해석에 따르면 ``h``에는 그러한 원소를 찾는 방법에 대한 정보가 전혀 포함되어 있지 않습니다.

이것은 ``Classical`` 이름공간에서 발견되므로 정리의 완전한 이름은 ``Classical.choice``입니다. 선택 원리은 *무한 설명*의 원리과 동일하며, 다음과 같이 하위 유형으로 표현될 수 있습니다.

```lean
# namespace Hidden
# universe u
# axiom choice {α : Sort u} : Nonempty α → α
noncomputable def indefiniteDescription {α : Sort u} (p : α → Prop)
                                        (h : ∃ x, p x) : {x // p x} :=
  choice <| let ⟨x, px⟩ := h; ⟨⟨x, px⟩⟩
# end Hidden
```

``선택(choice)``에 의존하기 때문에 린은 ``무한 설명(indefinite_Description)``에 대한 바이트 코드를 생성할 수 없으므로 ``(noncomputable)계산 불가능``으로 정의를 표시해야 합니다. 또한 ``Classical`` 이름공간에서 함수 ``choose``와 ``choose_spec`` 성질은 ``indefinite_description`` 출력의 두 부분을 분해합니다.

```lean
# open Classical
# namespace Hidden
noncomputable def choose {α : Sort u} {p : α → Prop} (h : ∃ x, p x) : α :=
  (indefiniteDescription p h).val

theorem choose_spec {α : Sort u} {p : α → Prop} (h : ∃ x, p x) : p (choose h) :=
  (indefiniteDescription p h).property
# end Hidden
```

``선택`` 원리은 또 ``비어 있음`` 속성과 보다 건설적인 ``내재`` 속성 간의 구별을 지웁니다.

```lean
# open Classical
theorem inhabited_of_nonempty :Nonempty α → Inhabited α :=
  fun h => choice (let ⟨a⟩ := h; ⟨⟨a⟩⟩)
```

다음 섹션에서는 ``propext``, ``funext`` 및 ``choice``가 함께 배중률과 모든 명제의 결정 가능성을 함의 한다는 것을 알 수 있습니다. 그것들을 사용하여 다음과 같이 무한 설명의 원리을 강화할 수 있습니다.

```lean
# open Classical
# universe u
#check (@strongIndefiniteDescription :
         {α : Sort u} → (p : α → Prop)
         → Nonempty α → {x // (∃ (y : α), p y) → p x})
```

주변 유형 ``α``가 비어 있지 않다고 가정하고, ``strongInReservationDescription p``는 원소가 하나가 있는 경우 ``p``를 충족하는 ``α``의 원소를 생성합니다. 이 정의의 데이터 구성요소는 일반적으로 *Hilbert의 엡실론 함수*로 알려져 있습니다.

```lean
# open Classical
# universe u
#check (@epsilon :
         {α : Sort u} → [Nonempty α]
         → (α → Prop) → α)

#check (@epsilon_spec :
          ∀ {a : Sort u} {p : a → Prop}(hex : ∃ (y : a), p y),
            p (@epsilon _ (nonempty_of_exists hex) p))
```

배중률(The Law of the Excluded Middle)
------------------------------

배중률은 다음과 같습니다.

```lean
open Classical

#check (@em : ∀ (p : Prop), p ∨ ¬p)
```

[디아코네스쿠의 정리(Diaconescu's theorem)](http://en.wikipedia.org/wiki/Diaconescu%27s_theorem)는 선택 공리가 배중률을 도출하기에 충분하다고 말합니다. 보다 정확히 ``Classical.choice``, ``propext``, ``funext``로부터 배중률을 따른다는 것을 보여줍니다. 표준 라이브러리에서 발견한 증명을 그립니다.

먼저 필요한 공리를 불러오고 두 개의 술어 ``U``와 ``V``를 정의합니다.

```lean
# namespace Hidden
open Classical
theorem em (p : Prop) : p ∨ ¬p :=
  let U (x : Prop) : Prop := x = True ∨ p
  let V (x : Prop) : Prop := x = False ∨ p

  have exU : ∃ x, U x := ⟨True, Or.inl rfl⟩
  have exV : ∃ x, V x := ⟨False, Or.inl rfl⟩
#   sorry
# end Hidden
```

``p``가 참이면 ``Prop``의 모든 원소는 ``U``와 ``V`` 둘 다에 있습니다.
``p``가 거짓이면 ``U``는 ``true``를 단일 개체로 갖고 ``V``는 ``false``를 단일 개체로 갖습니다.

다음으로 ``some``을 사용하여 ``U`` 및 ``V`` 각각으로부터 원소를 선택합니다.

```lean
# namespace Hidden
# open Classical
# theorem em (p : Prop) : p ∨ ¬p :=
#   let U (x : Prop) : Prop := x = True ∨ p
#   let V (x : Prop) : Prop := x = False ∨ p
#   have exU : ∃ x, U x := ⟨True, Or.inl rfl⟩
#   have exV : ∃ x, V x := ⟨False, Or.inl rfl⟩
  let u : Prop := choose exU
  let v : Prop := choose exV

  have u_def : U u := choose_spec exU
  have v_def : V v := choose_spec exV
#   sorry
# end Hidden
```

``U``와 ``V``는 각각 논리합이므로 ``u_def``와 ``v_def``는 4가지 경우를 나타냅니다. 이러한 경우 중 하나는 ``u = True`` 및 ``v = False``이고 다른 모든 경우에는 ``p``가 참입니다. 따라서 우리는 다음을 가지고 있습니다.

```lean
# namespace Hidden
# open Classical
# theorem em (p : Prop) : p ∨ ¬p :=
#   let U (x : Prop) : Prop := x = True ∨ p
#   let V (x : Prop) : Prop := x = False ∨ p
#   have exU : ∃ x, U x := ⟨True, Or.inl rfl⟩
#   have exV : ∃ x, V x := ⟨False, Or.inl rfl⟩
#   let u : Prop := choose exU
#   let v : Prop := choose exV
#   have u_def : U u := choose_spec exU
#   have v_def : V v := choose_spec exV
  have not_uv_or_p : u ≠ v ∨ p :=
    match u_def, v_def with
    | Or.inr h, _ => Or.inr h
    | _, Or.inr h => Or.inr h
    | Or.inl hut, Or.inl hvf =>
      have hne : u ≠ v := by simp [hvf, hut, true_ne_false]
      Or.inl hne
#   sorry
# end Hidden
```
한편, ``p``가 참이면, 함수 확장성과 명제 확장성에 의해 ``U``와 ``V``는 같습니다. ``u`` 및 ``v``의 정의에 따르면, 이는 또한 동등함을 함의합니다.

```lean
# namespace Hidden
# open Classical
# theorem em (p : Prop) : p ∨ ¬p :=
#   let U (x : Prop) : Prop := x = True ∨ p
#   let V (x : Prop) : Prop := x = False ∨ p
#   have exU : ∃ x, U x := ⟨True, Or.inl rfl⟩
#   have exV : ∃ x, V x := ⟨False, Or.inl rfl⟩
#   let u : Prop := choose exU
#   let v : Prop := choose exV
#   have u_def : U u := choose_spec exU
#   have v_def : V v := choose_spec exV
#   have not_uv_or_p : u ≠ v ∨ p :=
#     match u_def, v_def with
#     | Or.inr h, _ => Or.inr h
#     | _, Or.inr h => Or.inr h
#     | Or.inl hut, Or.inl hvf =>
#       have hne : u ≠ v := by simp [hvf, hut, true_ne_false]
#       Or.inl hne
  have p_implies_uv : p → u = v :=
    fun hp =>
    have hpred : U = V :=
      funext fun x =>
        have hl : (x = True ∨ p) → (x = False ∨ p) :=
          fun _ => Or.inr hp
        have hr : (x = False ∨ p) → (x = True ∨ p) :=
          fun _ => Or.inr hp
        show (x = True ∨ p) = (x = False ∨ p) from
          propext (Iff.intro hl hr)
    have h₀ : ∀ exU exV, @choose _ U exU = @choose _ V exV := by
      rw [hpred]; intros; rfl
    show u = v from h₀ _ _
#   sorry
# end Hidden
```
이 마지막 두 가지 사실을 종합하면 원하는 결론을 얻을 수 있습니다.

```lean
# namespace Hidden
# open Classical
# theorem em (p : Prop) : p ∨ ¬p :=
#   let U (x : Prop) : Prop := x = True ∨ p
#   let V (x : Prop) : Prop := x = False ∨ p
#   have exU : ∃ x, U x := ⟨True, Or.inl rfl⟩
#   have exV : ∃ x, V x := ⟨False, Or.inl rfl⟩
#   let u : Prop := choose exU
#   let v : Prop := choose exV
#   have u_def : U u := choose_spec exU
#   have v_def : V v := choose_spec exV
#   have not_uv_or_p : u ≠ v ∨ p :=
#     match u_def, v_def with
#     | Or.inr h, _ => Or.inr h
#     | _, Or.inr h => Or.inr h
#     | Or.inl hut, Or.inl hvf =>
#       have hne : u ≠ v := by simp [hvf, hut, true_ne_false]
#       Or.inl hne
#  have p_implies_uv : p → u = v :=
#     fun hp =>
#     have hpred : U = V :=
#       funext fun x =>
#         have hl : (x = True ∨ p) → (x = False ∨ p) :=
#           fun _ => Or.inr hp
#         have hr : (x = False ∨ p) → (x = True ∨ p) :=
#           fun _ => Or.inr hp
#         show (x = True ∨ p) = (x = False ∨ p) from
#           propext (Iff.intro hl hr)
#     have h₀ : ∀ exU exV, @choose _ U exU = @choose _ V exV := by
#       rw [hpred]; intros; rfl
#     show u = v from h₀ _ _
  match not_uv_or_p with
  | Or.inl hne => Or.inr (mt p_implies_uv hne)
  | Or.inr h   => Or.inl h
# end Hidden
```

배중률의 결과는 이중 부정 제거와 경우에 따른 증명 및 귀류법이 포함되며, 모두 [고전 논리 섹션](./propositions_and_proofs.md#classical_logic)에 설명되어 있습니다.
배중률과 명제의 확장성은 명제의 완전성을 함의합니다.

```lean
# namespace Hidden
open Classical
theorem propComplete (a : Prop) : a = True ∨ a = False :=
  match em a with
  | Or.inl ha => Or.inl (propext (Iff.intro (fun _ => ⟨⟩) (fun _ => ha)))
  | Or.inr hn => Or.inr (propext (Iff.intro (fun h => hn h) (fun h => False.elim h)))
# end Hidden
```

선택과 함께 우리는 또한 모든 명제가 결정 가능하다는 더 강력한 원리을 얻습니다. ``Decidable(결정 가능)`` 명제 클래스는 다음과 같이 정의됩니다.

```lean
# namespace Hidden
class inductive Decidable (p : Prop) where
  | isFalse (h : ¬p) : Decidable p
  | isTrue  (h : p)  : Decidable p
# end Hidden
```

``Prop``만 제거할 수 있는 ``p ∨ ¬ p``와 달리 ``decidable p``형은 합계 유형 ``Sum p(¬ p)``과 동일합니다. 이는 임의의 유형을 제거할 수 있습니다. if-then-else 표현식을 작성하는 데 필요한 것은 이 데이터입니다.

고전적 추론의 예로서 ``choose``를 사용하여 ``f : α → β``가 형용사이고 ``α``가 내제된 경우 ``f``는 왼쪽 역함수를 같습니다. 왼쪽 역함수 ``linv``를 정의하기 위해 종속적인 if-then-else 표현식을 사용합니다. ``if h : c then t else e``는 ``dite c (fun h : c => t) (fun h : ¬ c => e)``에 대한 표기법임을 기억하세요. ``linv``의 정의에서 선택은 두 번 사용됩니다. 먼저 ``(∃ a : A, f a = b)``가 "결정 가능"임을 보이는 데 그 뒤 ``f a = b``을 만족하는 ``a``를 선택하는데 사용됩니다. ``propDecidable``은 범위가 지정된 개체이며 `open Classical` 명령에 의해 활성화됩니다. 이 개체를 사용하여 if-then-else 표현식을 정당화합니다. ([결정 ​​가능 명제 섹션](./type_classes.md#decidable_propositions)의 논의를 참조하세요.)

```lean
open Classical

noncomputable def linv [Inhabited α] (f : α → β) : β → α :=
  fun b : β => if ex : (∃ a : α, f a = b) then choose ex else default

theorem linv_comp_self {f : α → β} [Inhabited α]
                       (inj : ∀ {a b}, f a = f b → a = b)
                       : linv f ∘ f = id :=
  funext fun a =>
    have ex  : ∃ a₁ : α, f a₁ = f a := ⟨a, rfl⟩
    have feq : f (choose ex) = f a  := choose_spec ex
    calc linv f (f a) = choose ex := dif_pos ex
               _      = a         := inj feq

```

고전적인 관점에서 ``linv``는 함수입니다. 일반적으로 그러한 기능을 구현할 방법이 없고 생성도 유익하지 않으므로 직관주의적인 관점에서 이는 허용되지 않습니다.
