전략
=======

이 장에서는 *전략*을 사용하여 증명을 생성하는 대체 접근 방식을 설명합니다.  증명 항는 수학적 증명의 표현입니다. 전술은 그러한 증명를 구축하는 방법을 설명하는 명령 또는 지침입니다. 비공식적으로 "앞방향으로 증명하고, 정의를 펼치고, 이전 보조 정리를 적용하고, 단순화하십시오."라고 말함으로써 수학적 증명을 시작할 수 있습니다. 이것이 독자에게 관련 증명을 찾는 방법을 알려주는 지침인 것처럼 전략은 Lean에게 증명 항를 생성하는 방법을 알려주는 지침입니다. 그들은 증명을 분해하고 한 번에 한 단계씩 목표를 달성하는 점진적인 스타일의 증명을 자연스럽게 지원합니다.

우리는 전략의 연쇄로 이뤄진 증명을 "전략 스타일" 증명으로 설명할 것이고, 우리가  "항 스타일" 증명이라고 부를 것이고 이제까지 보았던 증명 항를 작성하는 방법과 대조할 것입니다. 각 스타일은 그것의 장단점을 가지고 있습니다. 예를 들어, 전략 스타일의 증명은 독자가 각 명령의 결과를 예측하거나 추측해야 하기 때문에 읽기가 더 어려울 수 있습니다. 그러나 그것들은 더 짧고 더 쓰기 쉬울 수 있습니다. 게다가 자동화된 절차 자체가 전략이기 때문에 전략은 Lean의 자동화를 사용하기 위한 관문을 제공합니다.

전략 모드 진입
--------------------

개념적으로, 정리를 진술하거나 ``have`` 문장을 도입하는 것은 예상되는 유형으로 항를 생성하는 목표를 만듭니다. 예를 들어 , 다음은 ``p ∧ q ∧ p``형의 항을 상수 ``p q : Prop``과 ``hp : p``,``hq : q``가 있는 현재 상황에 대해 생성하는 목표를 만듭니다.

```lean
theorem test (p q : Prop) (hp : p) (hq : q) : p ∧ q ∧ p :=
  sorry
```

여러분은 이 목표를 다음과 같이 쓸 수 있습니다.

```
    p : Prop, q : Prop, hp : p, hq : q ⊢ p ∧ q ∧ p
```

실제로 위의 예에서 "sorry"를 밑줄로 바꾸면 린은 바로 이 목표가 해결되지 않은 상태로 남아 있다고 보고합니다.

일반적으로 명시적인 항을 작성하여 이런 목표를 달성합니다. 그러나 항이 예상되는 어디든지 린은 우리가 ``by <tactics>`` 블록 대신 ``<tactics>``이 세미콜론이나 줄 분리자로 나눠진 일련의 명령들을 삽입하게 해줍니다. 여러분은 위의 정리를 그와 같이 증명할 수 있습니다.

```lean
theorem test (p q : Prop) (hp : p) (hq : q) : p ∧ q ∧ p :=
  by apply And.intro
     exact hp
     apply And.intro
     exact hq
     exact hp
```

우리는 종종 ``by`` 키워드를 앞줄에 놓고 위의 예를 다음과 같이 작성합니다.

```lean
theorem test (p q : Prop) (hp : p) (hq : q) : p ∧ q ∧ p := by
  apply And.intro
  exact hp
  apply And.intro
  exact hq
  exact hp
```

``apply`` 전략은 0 또는 그 이상의 인수가 있는 함수를 나타내는 것으로 간주되는 표현식을 적용합니다. 결론을 현재 목표의 표현식과 통합하고 이후 인수가 종속되지 않는 한 나머지 인수에 대한 새 목표를 생성합니다. 위의 예에서 ``apply And.intro`` 명령은 두 하위 목표를 얻습니다.

```
    case left
    p : Prop,
    q : Prop,
    hp : p,
    hq : q
    ⊢ p

    case right
    p : Prop,
    q : Prop,
    hp : p,
    hq : q
    ⊢ q ∧ p
```

첫 번째 목표는 ``exact hp``명령으로 달성할 수 있습니다. ``exact``
명령은 목표와 동일한 표현식임을 알리는 ``apply``의 변형일 뿐입니다. 전략 증명모드에서 이것은 사용하기에 좋은 형태입니다.
왜냐하면 그것의 실패는 무언가 잘못되었음을 알려주기 때문입니다. 이것은 ``apply``보다 더 강건합니다. 왜냐하면
협력기는 적용될 표현식을 처리할 때 목표의 대상에 의해
제시된 예상 유형을 받기를 기대하기 때문입니다. 하지만 이 경우 ``apply``도 마찬가지로 잘 작동할 것입니다.

여러분은 ``#print`` 명령으로 증명항의 결과를 볼 수 있습니다.

```lean
# theorem test (p q : Prop) (hp : p) (hq : q) : p ∧ q ∧ p := by
#  apply And.intro
#  exact hp
#  apply And.intro
#  exact hq
#  exact hp
#print test
```

여러분은 점진적으로 전략 스크립트를 쓸 수도 있습니다. VS Code에서 여러분은  ``Ctrl-Shift-Enter``을 눌러 메시지을 보고자 창을 열 수 있습니다.
그러면 이 창은 전략 블록 속의 커서가 어디에 있든지 간에 현재 목표를 여러분에게 보여줄 것입니다. Emacs에서 여러분은 임의의 줄의 끝에서 ``C-c C-g``을 눌러 목표를 볼 수 있습니다.
아니면 마지막 전략의 첫 문자 뒤에 커서를 놓으면 불완전한 증명에 대한 나머지 목표를 볼 수 있습니다. 만일 증명이 불완전하다면, 토큰 ``by``은 빨간색 구불구불한 선으로 장식됩니다.
그리고 오류 메시지가 남은 목표에 포함됩니다.

전략 명령은 하나의 식별자 뿐만 아니라 복합된 식을 받을 수 있습니다. 다음은 이전의 증명보다 더 짧은 버전의 증명입니다.

```lean
theorem test (p q : Prop) (hp : p) (hq : q) : p ∧ q ∧ p := by
  apply And.intro hp
  exact And.intro hq hp
```

놀랄 것 없이, 이것은 정확히 동일한 증명항을 만듭니다.

```lean
# theorem test (p q : Prop) (hp : p) (hq : q) : p ∧ q ∧ p := by
#  apply And.intro hp
#  exact And.intro hq hp
#print test
```

복수의 전략들은 세미콜론으로 연결한 한 줄에 작성될 수 있습니다.

```lean
theorem test (p q : Prop) (hp : p) (hq : q) : p ∧ q ∧ p := by
  apply And.intro hp; exact And.intro hq hp
```

다수의 하위 목표를 생성할 수 있는 전략은 이들에 표식을 붙입니다. 예를 들어, 전략  ``apply And.intro``는 첫번째 목표를 ``left``으로
두번째 목표를 ``right``으로 표식을 붙입니다. ``apply`` 전략의 경우 표식은 ``And.intro``에서 사용된 매개변수의 이름으로부터 추론됩니다. 여러분은 여러분의 전략을 ``case <tag> => <tactics>``기호를 사용해 구조화할 수 있습니다. 다음은 이 장의 첫번째 우리의 전략 증명의 구조화된 버전입니다.

```lean
theorem test (p q : Prop) (hp : p) (hq : q) : p ∧ q ∧ p := by
  apply And.intro
  case left => exact hp
  case right =>
    apply And.intro
    case left => exact hq
    case right => exact hp
```

여러분은 ``case``기호를 사용해서 하위목표 ``left``보다 먼저 ``right``을 풀 수 있습니다.

```lean
theorem test (p q : Prop) (hp : p) (hq : q) : p ∧ q ∧ p := by
  apply And.intro
  case right =>
    apply And.intro
    case left => exact hq
    case right => exact hp
  case left => exact hp
```

린은 ``case``블록 안에 다른 목표를 숨긴 것을 주목하세요. 우리는 이를 선택한 목표에 "초점을 맞췄다"고 합니다.  게다가 린은 선택된 목표가 ``case`` 블록의 끝에서 완전히 풀리지 않았다면 오류를 표시합니다.

간단한 하위목표에 대해 그것의 표식을 이용해 하위목표를 선택하는 것은 불필요할 수 있지만
그래도 여러분은 여전히 증명을 구조화하길 원할지도 모릅니다. 린은 또 구조화한 증명에 대해 "bullet" 기호를 제공합니다.`` <tactics>`` (혹은 ``· <tactics>``)

```lean
theorem test (p q : Prop) (hp : p) (hq : q) : p ∧ q ∧ p := by
  apply And.intro
  . exact hp
  . apply And.intro
    . exact hq
    . exact hp
```

기본 전략들
-------------

``apply``과 ``exact``에 더해 또 다른 유용한 전략은 가정을 도입하는 ``intro``입니다. 다음의 것은 전략을 사용해 증명할 이전 장에서 증명한 명제논리의 항등식의 예시들입니다.

```lean
example (p q r : Prop) : p ∧ (q ∨ r) ↔ (p ∧ q) ∨ (p ∧ r) := by
  apply Iff.intro
  . intro h
    apply Or.elim (And.right h)
    . intro hq
      apply Or.inl
      apply And.intro
      . exact And.left h
      . exact hq
    . intro hr
      apply Or.inr
      apply And.intro
      . exact And.left h
      . exact hr
  . intro h
    apply Or.elim h
    . intro hpq
      apply And.intro
      . exact And.left hpq
      . apply Or.inl
        exact And.right hpq
    . intro hpr
      apply And.intro
      . exact And.left hpr
      . apply Or.inr
        exact And.right hpr
```

``intro``명령은 폭넓게로는 임의 유형의 변수를 도입하는데 사용됩니다.

```lean
example (α : Type) : α → α := by
  intro a
  exact a

example (α : Type) : ∀ x : α, x = x := by
  intro x
  exact Eq.refl x
```

여러분은 몇 개의 변수들을 도입하는데 사용할 수 있습니다.

```lean
example : ∀ a b c : Nat, a = b → a = c → c = b := by
  intro a b c h₁ h₂
  exact Eq.trans (Eq.symm h₂) h₁
```

 ``apply`` 전략이 함수의 활용을 상호작용으로 만드는 명령인 것처럼
``intro`` 전략은 상호작용 방식으로 함수 추상화를 만드는 명령입니다.
(예, ``fun x => e``꼴의 항들).  람다 추상화 기호처럼 ``intro`` 전략은 암시적인 ``match``를 쓸 수 있도록 해줍니다.

```lean
example (α : Type) (p q : α → Prop) : (∃ x, p x ∧ q x) → ∃ x, q x ∧ p x := by
  intro ⟨w, hpw, hqw⟩
  exact ⟨w, hqw, hpw⟩
```

여러분은 ``match`` 표현식에서처럼 여러 가지 변형들을 제공할 수도 있습니다.

```lean
example (α : Type) (p q : α → Prop) : (∃ x, p x ∨ q x) → ∃ x, q x ∨ p x := by
  intro
    | ⟨w, Or.inl h⟩ => exact ⟨w, Or.inr h⟩
    | ⟨w, Or.inr h⟩ => exact ⟨w, Or.inl h⟩
```

``intros`` 전략은 어떠한 인수 없이도 사용될 수 있습니다.
가령, 그것은 이름을 선택할 수 있고, 원하는 한 많이 많은 변수를 도입할 수 있습니다. 어느 때에 여러분은 이에 대한 예를 볼 것입니다.

``assumption`` 전략은 현재 목표의 맥락 속 가정을 훝어 봅니다.
그리고 결론과 대응되는 가정이 있다면 그것을 목표에 적용합니다.

```lean
example (x y z w : Nat) (h₁ : x = y) (h₂ : y = z) (h₃ : z = w) : x = w := by
  apply Eq.trans h₁
  apply Eq.trans h₂
  assumption   -- applied h₃
```

이것은 필요하다면 결론의 메타변수들을 통합할 것 입니다.

```lean
example (x y z w : Nat) (h₁ : x = y) (h₂ : y = z) (h₃ : z = w) : x = w := by
  apply Eq.trans
  assumption      -- solves x = ?b with h₁
  apply Eq.trans
  assumption      -- solves y = ?h₂.b with h₂
  assumption      -- solves z = w with h₃
```

다음 예제는 ``intros`` 명령을 사용해 세 개의 변수와 두 개의 가정을 자동으로 도입합니다.

```lean
example : ∀ a b c : Nat, a = b → a = c → c = b := by
  intros
  apply Eq.trans
  apply Eq.symm
  assumption
  assumption
```

린에 의해 자동으로 생성된 이름들은 기본적으로 접근할 수 없습니다. 그 이유는 여러분의 전략 증명이 자동으로 생성된 이름에 의존하지 않도록 보장하기 위함입니다. 그리고 그 결과로 증명은 더 튼튼하게 됩니다.
하지만 여러분은 ``unhygienic`` 조합자를 사용해서 이 제한을 해제할 수 있습니다.

```lean
example : ∀ a b c : Nat, a = b → a = c → c = b := by unhygienic
  intros
  apply Eq.trans
  apply Eq.symm
  exact a_2
  exact a_1
```

혹은 ``rename_i`` 전략으로 여러분의 상황에 가장 최근에 접속불가한 이름을 바꿀 수 있습니다.
다음 예제에서는 ``rename_i h1 _ h2`` 전략이 여러분의 상황 속 세 가정 중 마지막 두 개의 이름을 바꿉니다.

```lean
example : ∀ a b c d : Nat, a = b → a = d → a = c → c = b := by
  intros
  rename_i h1 _ h2
  apply Eq.trans
  apply Eq.symm
  exact h2
  exact h1
```

``rfl``은 ``exact rfl``에 대한 문법 설탕입니다.
```lean
example (y : Nat) : (fun x : Nat => 0) y = 0 :=
  by rfl
```

조합자  ``repeat``는 한 전략을 여러 차례 적용하는데 사용될 수 있습니다.

```lean
example : ∀ a b c : Nat, a = b → a = c → c = b := by
  intros
  apply Eq.trans
  apply Eq.symm
  repeat assumption
```

때떄로 유용한 또 다른 전략은 ``revert``는 ``intro``의 역방향 전략입니다.

```lean
example (x : Nat) : x = x := by
  revert x
  -- goal is ⊢ ∀ (x : Nat), x = x
  intro y
  -- goal is y : Nat ⊢ y = y
  rfl
```

가정을 목표 속으로 옮김으로써 함의를 얻습니다.

```lean
example (x y : Nat) (h : x = y) : y = x := by
  revert h
  -- goal is x y : Nat ⊢ x = y → y = x
  intro h₁
  -- goal is x y : ℕ, h₁ : x = y ⊢ y = x
  apply Eq.symm
  assumption
```

그러나 ``revert``는 맥락 속 요소들 뿐만 아니라 그에 의존하는 맥락의 뒤에 올 모든 요소를 되돌려 놓는 다는 점에서 아주 영리합니다. 예를 들어 위의 예제에서 ``x``를 되돌려 놓는 것은 그것과 붙은 ``h``를 가져옵니다.

```lean
example (x y : Nat) (h : x = y) : y = x := by
  revert x
  -- goal is y : Nat ⊢ ∀ (x : Nat), x = y → y = x
  intros
  apply Eq.symm
  assumption
```

여러분은 맥락 속 다수의 요소들을 한번에 되돌려 놓을 수 있습니다.
```lean
example (x y : Nat) (h : x = y) : y = x := by
  revert x y
  -- goal is ⊢ ∀ (x y : Nat), x = y → y = x
  intros
  apply Eq.symm
  assumption
```

여러분은 국부적인 상황 속 요소 즉, 지역변수나 가정을 ``revert`` 할 수 있습니다. 하지만 여러분은 목표 속 임의의 표현식을 ``generalize`` 전략을 사용해 새 변수로 대체할 수 있습니다.

```lean
example : 3 = 3 := by
  generalize 3 = x
  -- goal is x : Nat ⊢ x = x,
  revert x
  -- goal is ⊢ ∀ (x : Nat), x = x
  intro y
  -- goal is y : Nat ⊢ y = y
  rfl
```

위의 표기에 대한 기억법은 여러분이 ``3``으로 설정한 목표을 임의의 변수 ``x``로 일반화시키는 것입니다. 조심하세요. 모든 일반화가 목표의 유효성을 보존하지는 않습니다. 여기서 ``generalize``는 ``rfl``을 사용해 증명할 수 있는 목표를
증명가능하지 않은 것으로 바꿉니다.

```lean
example : 2 + 3 = 5 := by
  generalize  3 = x
  -- goal is x : Nat ⊢ 2 + x = 5
  admit
```

이 예제에서 ``admit`` 전략은 증명항 ``sorry``와 유사합니다. 이것은 현재 목표를 마무리 짓고, ``sorry``를 사용했을 때처럼 경고를 만듭니다. 앞선 목표의 유효성을 보존하기 위해 ``generalize`` 전략은 ``3``이
``x``로 대체되었음에 대한 사실을 기록하게 해줍니다. 여러분이 해야할 것은 레이블을 제공하는 것과 ``generalize``가 그 레이블을 지역 상황에 할당물을 저장하는데 사용하도록 하는 것입니다.

```lean
example : 2 + 3 = 5 := by
  generalize h : 3 = x
  -- goal is x : Nat, h : 3 = x ⊢ 2 + x = 5
  rw [← h]
```

여기 ``rewrite`` 전략은 ``rw``로 축약되었고, ``h``를 써서 ``x``가 다시 ``3``으로 바뀌게 했습니다. ``rewrite``전략은 아래에서 더 논의할 것 입니다.


이 외의 전략들
------------

몇 가지 추가적인 전략들은 명제와 데이터를 생성하고 파괴하는데 유용합니다. 예를 들어, ``p ∨ q``꼴의 목표에 적용했을 때, 여러분은 ``apply Or.inl``과 ``apply
Or.inr`` 같은 전략들을 사용합니다.  반대로 ``cases`` 전략은 분리자를 분해하는데 사용할 수 있습니다.

```lean
example (p q : Prop) : p ∨ q → q ∨ p := by
  intro h
  cases h with
  | inl hp => apply Or.inr; exact hp
  | inr hq => apply Or.inl; exact hq
```

문법이 `match` 표현식에서의 것과 비슷함에 주목하세요.
새로운 하위 목표는 임의의 순서로 풀릴 수 있습니다.

```lean
example (p q : Prop) : p ∨ q → q ∨ p := by
  intro h
  cases h with
  | inr hq => apply Or.inl; exact hq
  | inl hp => apply Or.inr; exact hp
```

여러분은 (비구조화된)``cases``를 각각의 변형과 전략에 대해 ``with`` 없이 사용할 수 있습니다.

```lean
example (p q : Prop) : p ∨ q → q ∨ p := by
  intro h
  cases h
  apply Or.inr
  assumption
  apply Or.inl
  assumption
```

(비구조화된)``cases``는 여러분이 여러 개의 하위목표를 같은 전략을 사용해 끝낼 때 특히 유용합니다.

```lean
example (p : Prop) : p ∨ p → p := by
  intro h
  cases h
  repeat assumption
```

또 여러분은 조합자  ``tac1 <;> tac2``를 각각의 하위 목표가 만든
 ``tac2``에 ``tac1``의 전략을 적용하여 사용할 수 있습니다.

```lean
example (p : Prop) : p ∨ p → p := by
  intro h
  cases h <;> assumption
```

여러분은 비구조화된 ``cases`` 전략을  ``case``와 ``.`` 기호와 결합할 수 있습니다.

```lean
example (p q : Prop) : p ∨ q → q ∨ p := by
  intro h
  cases h
  . apply Or.inr
    assumption
  . apply Or.inl
    assumption

example (p q : Prop) : p ∨ q → q ∨ p := by
  intro h
  cases h
  case inr h =>
    apply Or.inl
    assumption
  case inl h =>
    apply Or.inr
    assumption

example (p q : Prop) : p ∨ q → q ∨ p := by
  intro h
  cases h
  case inr h =>
    apply Or.inl
    assumption
  . apply Or.inr
    assumption
```


``cases`` 전략은 결합자를 분해하는데 사용될 수 있습니다.

```lean
example (p q : Prop) : p ∧ q → q ∧ p := by
  intro h
  cases h with
  | intro hp hq => constructor; exact hq; exact hp
```

이 예제에서,``cases`` 전략이 ``h : p ∧ q``에서 가정
``hp : p``과 ``hq : q``을 적용한  이후에는 한 목표만 남습니다. ``constructor`` 전략은 결합자 ``And.intro``에 대한 단일 생성자를 적용합니다. 이 전략으로 이전 섹션의 예제를 다음과 같이 다시 쓸 수 있습니다.

```lean
example (p q r : Prop) : p ∧ (q ∨ r) ↔ (p ∧ q) ∨ (p ∧ r) := by
  apply Iff.intro
  . intro h
    cases h with
    | intro hp hqr =>
      cases hqr
      . apply Or.inl; constructor <;> assumption
      . apply Or.inr; constructor <;> assumption
  . intro h
    cases h with
    | inl hpq =>
      cases hpq with
      | intro hp hq => constructor; exact hp; apply Or.inl; exact hq
    | inr hpr =>
      cases hpr with
      | intro hp hr => constructor; exact hp; apply Or.inr; exact hr
```

[유도형 장](./inductive_types.md)에서 이 전략들은 꽤나 일반적임을 볼 것입니다. ``cases`` 전략은 유도적으로 정의된 유형의 임의의 원소를 분해하는데 사용될 수 있습니다.
``constructor``는 항상 유도적으로 정의된 유형의 처음으로 활용할 수 있는 생성자에 적용할 수 있습니다.
예를 들어, 여러분은``cases``와 ``constructor``을 존재 정량자와 사용할 수 있습니다.

```lean
example (p q : Nat → Prop) : (∃ x, p x) → ∃ x, p x ∨ q x := by
  intro h
  cases h with
  | intro x px => constructor; apply Or.inl; exact px
```

여기서  ``constructor`` 전략은 존재 가정의 첫 요소 암시적으로 ``x``의 값으로 남깁니다. 이는 메타변수로 표현되며 나중에 반드시 개체화되어야 합니다. 이전 예제에서 메타변수의 적절한 값은``exact px`` 전략에 의해 결정됩니다.
그 이유는 ``px``가 ``p x``형을 갖기 때문입니다. 여러분이 명시적으로 존재정량자를 나타내 보도록하길 원한다면,
대신``exists`` 전략을 사용하면 됩니다.

```lean
example (p q : Nat → Prop) : (∃ x, p x) → ∃ x, p x ∨ q x := by
  intro h
  cases h with
  | intro x px => exists x; apply Or.inl; exact px
```

여기 또 다른 예제가 있습니다.

```lean
example (p q : Nat → Prop) : (∃ x, p x ∧ q x) → ∃ x, q x ∧ p x := by
  intro h
  cases h with
  | intro x hpq =>
    cases hpq with
    | intro hp hq =>
      exists x
      constructor <;> assumption
```

이 전략들은 명제와 마찬가지로 데이터에 사용될 수 있습니다. 다음 두 예제에서, 이들은 곱과 합 유형의 요소를 바꾸는 함수를 정의하는데 사용됩니다.

```lean
def swap_pair : α × β → β × α := by
  intro p
  cases p
  constructor <;> assumption
```

```lean
def swap_sum : Sum α β → Sum β α := by
  intro p
  cases p
  . apply Sum.inr; assumption
  . apply Sum.inl; assumption
```

Note that up to the names we have chosen for the variables, the
definitions are identical to the proofs of the analogous propositions
for conjunction and disjunction. The ``cases`` tactic will also do a
case distinction on a natural number:

```lean
open Nat
example (P : Nat → Prop) (h₀ : P 0) (h₁ : ∀ n, P (succ n)) (m : Nat) : P m := by
 cases m with
 | zero    => exact h₀
 | succ m' => exact h₁ m'
```

The ``cases`` tactic, and its companion, the ``induction`` tactic, are discussed in greater detail in
the [Tactics for Inductive Types](./inductive_types.md#tactics_for_inductive_types) section.

The ``contradiction`` tactic searches for a contradiction among the hypotheses of the current goal:

```lean
example (p q : Prop) : p ∧ ¬ p → q := by
  intro h
  cases h
  contradiction
```

You can also use ``match`` in tactic blocks.

```lean
example (p q r : Prop) : p ∧ (q ∨ r) ↔ (p ∧ q) ∨ (p ∧ r) := by
  apply Iff.intro
  . intro h
    match h with
    | ⟨_, Or.inl _⟩ => apply Or.inl; constructor <;> assumption
    | ⟨_, Or.inr _⟩ => apply Or.inr; constructor <;> assumption
  . intro h
    match h with
    | Or.inl ⟨hp, hq⟩ => constructor; exact hp; apply Or.inl; exact hq
    | Or.inr ⟨hp, hr⟩ => constructor; exact hp; apply Or.inr; exact hr
```

You can "combine" ``intro h`` with ``match h ...`` and write the previous examples as follows

```lean
example (p q r : Prop) : p ∧ (q ∨ r) ↔ (p ∧ q) ∨ (p ∧ r) := by
  apply Iff.intro
  . intro
     | ⟨hp, Or.inl hq⟩ => apply Or.inl; constructor <;> assumption
     | ⟨hp, Or.inr hr⟩ => apply Or.inr; constructor <;> assumption
  . intro
     | Or.inl ⟨hp, hq⟩ => constructor; assumption; apply Or.inl; assumption
     | Or.inr ⟨hp, hr⟩ => constructor; assumption; apply Or.inr; assumption

```

Structuring Tactic Proofs
-------------------------

Tactics often provide an efficient way of building a proof, but long
sequences of instructions can obscure the structure of the
argument. In this section, we describe some means that help provide
structure to a tactic-style proof, making such proofs more readable
and robust.

One thing that is nice about Lean's proof-writing syntax is that it is
possible to mix term-style and tactic-style proofs, and pass between
the two freely. For example, the tactics ``apply`` and ``exact``
expect arbitrary terms, which you can write using ``have``, ``show``,
and so on. Conversely, when writing an arbitrary Lean term, you can
always invoke the tactic mode by inserting a ``by``
block. The following is a somewhat toy example:

```lean
example (p q r : Prop) : p ∧ (q ∨ r) → (p ∧ q) ∨ (p ∧ r) := by
  intro h
  exact
    have hp : p := h.left
    have hqr : q ∨ r := h.right
    show (p ∧ q) ∨ (p ∧ r) by
      cases hqr with
      | inl hq => exact Or.inl ⟨hp, hq⟩
      | inr hr => exact Or.inr ⟨hp, hr⟩
```

The following is a more natural example:

```lean
example (p q r : Prop) : p ∧ (q ∨ r) ↔ (p ∧ q) ∨ (p ∧ r) := by
  apply Iff.intro
  . intro h
    cases h.right with
    | inl hq => exact Or.inl ⟨h.left, hq⟩
    | inr hr => exact Or.inr ⟨h.left, hr⟩
  . intro h
    cases h with
    | inl hpq => exact ⟨hpq.left, Or.inl hpq.right⟩
    | inr hpr => exact ⟨hpr.left, Or.inr hpr.right⟩
```

In fact, there is a ``show`` tactic, which is similar to the
``show`` expression in a proof term. It simply declares the type of the
goal that is about to be solved, while remaining in tactic
mode.

```lean
example (p q r : Prop) : p ∧ (q ∨ r) ↔ (p ∧ q) ∨ (p ∧ r) := by
  apply Iff.intro
  . intro h
    cases h.right with
    | inl hq =>
      show (p ∧ q) ∨ (p ∧ r)
      exact Or.inl ⟨h.left, hq⟩
    | inr hr =>
      show (p ∧ q) ∨ (p ∧ r)
      exact Or.inr ⟨h.left, hr⟩
  . intro h
    cases h with
    | inl hpq =>
      show p ∧ (q ∨ r)
      exact ⟨hpq.left, Or.inl hpq.right⟩
    | inr hpr =>
      show p ∧ (q ∨ r)
      exact ⟨hpr.left, Or.inr hpr.right⟩
```

The ``show`` tactic can actually be used to rewrite a goal to something definitionally equivalent:

```lean
example (n : Nat) : n + 1 = Nat.succ n := by
  show Nat.succ n = Nat.succ n
  rfl
```

There is also a ``have`` tactic, which introduces a new subgoal, just as when writing proof terms:

```lean
example (p q r : Prop) : p ∧ (q ∨ r) → (p ∧ q) ∨ (p ∧ r) := by
  intro ⟨hp, hqr⟩
  show (p ∧ q) ∨ (p ∧ r)
  cases hqr with
  | inl hq =>
    have hpq : p ∧ q := And.intro hp hq
    apply Or.inl
    exact hpq
  | inr hr =>
    have hpr : p ∧ r := And.intro hp hr
    apply Or.inr
    exact hpr
```

As with proof terms, you can omit the label in the ``have`` tactic, in
which case, the default label ``this`` is used:

```lean
example (p q r : Prop) : p ∧ (q ∨ r) → (p ∧ q) ∨ (p ∧ r) := by
  intro ⟨hp, hqr⟩
  show (p ∧ q) ∨ (p ∧ r)
  cases hqr with
  | inl hq =>
    have : p ∧ q := And.intro hp hq
    apply Or.inl
    exact this
  | inr hr =>
    have : p ∧ r := And.intro hp hr
    apply Or.inr
    exact this
```

The types in a ``have`` tactic can be omitted, so you can write ``have
hp := h.left`` and ``have hqr := h.right``.  In fact, with this
notation, you can even omit both the type and the label, in which case
the new fact is introduced with the label ``this``.

```lean
example (p q r : Prop) : p ∧ (q ∨ r) → (p ∧ q) ∨ (p ∧ r) := by
  intro ⟨hp, hqr⟩
  cases hqr with
  | inl hq =>
    have := And.intro hp hq
    apply Or.inl; exact this
  | inr hr =>
    have := And.intro hp hr
    apply Or.inr; exact this
```

Lean also has a ``let`` tactic, which is similar to the ``have``
tactic, but is used to introduce local definitions instead of
auxiliary facts. It is the tactic analogue of a ``let`` in a proof
term.

```lean
example : ∃ x, x + 2 = 8 := by
  let a : Nat := 3 * 2
  exists a
  rfl
```

As with ``have``, you can leave the type implicit by writing ``let a
:= 3 * 2``. The difference between ``let`` and ``have`` is that
``let`` introduces a local definition in the context, so that the
definition of the local declaration can be unfolded in the proof.

We have used ``.`` to create nested tactic blocks.  In a nested block,
Lean focuses on the first goal, and generates an error if it has not
been fully solved at the end of the block. This can be helpful in
indicating the separate proofs of multiple subgoals introduced by a
tactic. The notation ``.`` is whitespace sensitive and relies on the indentation
to detect whether the tactic block ends. Alternatively, you can
define tactic blocks usind curly braces and semicolons.

```lean
example (p q r : Prop) : p ∧ (q ∨ r) ↔ (p ∧ q) ∨ (p ∧ r) := by
  apply Iff.intro
  { intro h;
    cases h.right;
    { show (p ∧ q) ∨ (p ∧ r);
      exact Or.inl ⟨h.left, ‹q›⟩ }
    { show (p ∧ q) ∨ (p ∧ r);
      exact Or.inr ⟨h.left, ‹r›⟩ } }
  { intro h;
    cases h;
    { show p ∧ (q ∨ r);
      rename_i hpq;
      exact ⟨hpq.left, Or.inl hpq.right⟩ }
    { show p ∧ (q ∨ r);
      rename_i hpr;
      exact ⟨hpr.left, Or.inr hpr.right⟩ } }
```

It useful to use indendation to structure proof: every time a tactic
leaves more than one subgoal, we separate the remaining subgoals by
enclosing them in blocks and indenting.  Thus if the application of
theorem ``foo`` to a single goal produces four subgoals, one would
expect the proof to look like this:

```
  apply foo
  . <proof of first goal>
  . <proof of second goal>
  . <proof of third goal>
  . <proof of final goal>
```

or

```
  apply foo
  case <tag of first goal>  => <proof of first goal>
  case <tag of second goal> => <proof of second goal>
  case <tag of third goal>  => <proof of third goal>
  case <tag of final goal>  => <proof of final goal>
```

or

```
  apply foo
  { <proof of first goal>  }
  { <proof of second goal> }
  { <proof of third goal>  }
  { <proof of final goal>  }
```


Tactic Combinators
------------------

*Tactic combinators* are operations that form new tactics from old
ones. A sequencing combinator is already implicit in the ``by`` block:

```lean
example (p q : Prop) (hp : p) : p ∨ q :=
  by apply Or.inl; assumption
```

Here, ``apply Or.inl; assumption`` is functionally equivalent to a
single tactic which first applies ``apply Or.inl`` and then applies
``assumption``.

In ``t₁ <;> t₂``, the ``<;>`` operator provides a *parallel* version of the sequencing operation:
``t₁`` is applied to the current goal, and then ``t₂`` is applied to *all* the resulting subgoals:

```lean
example (p q : Prop) (hp : p) (hq : q) : p ∧ q :=
  by constructor <;> assumption
```

This is especially useful when the resulting goals can be finished off
in a uniform way, or, at least, when it is possible to make progress
on all of them uniformly.

The ``first | t₁ | t₂ | ... | tₙ`` applies each `tᵢ` until one succeeds, or else fails:

```lean
example (p q : Prop) (hp : p) : p ∨ q := by
  first | apply Or.inl; assumption | apply Or.inr; assumption
```

In the first example, the left branch succeeds, whereas in the second one, it is the right one that succeeds.
In the next three examples, the same compound tactic succeeds in each case.

```lean
example (p q r : Prop) (hp : p) : p ∨ q ∨ r :=
  by repeat (first | apply Or.inl; assumption | apply Or.inr | assumption)

example (p q r : Prop) (hq : q) : p ∨ q ∨ r :=
  by repeat (first | apply Or.inl; assumption | apply Or.inr | assumption)

example (p q r : Prop) (hr : r) : p ∨ q ∨ r :=
  by repeat (first | apply Or.inl; assumption | apply Or.inr | assumption)
```

The tactic tries to solve the left disjunct immediately by assumption;
if that fails, it tries to focus on the right disjunct; and if that
doesn't work, it invokes the assumption tactic.

You will have no doubt noticed by now that tactics can fail. Indeed,
it is the "failure" state that causes the *first* combinator to
backtrack and try the next tactic. The ``try`` combinator builds a
tactic that always succeeds, though possibly in a trivial way:
``try t`` executes ``t`` and reports success, even if ``t`` fails. It is
equivalent to ``first | t | skip``, where ``skip`` is a tactic that does
nothing (and succeeds in doing so). In the next example, the second
``constructor`` succeeds on the right conjunct ``q ∧ r`` (remember that
disjunction and conjunction associate to the right) but fails on the
first. The ``try`` tactic ensures that the sequential composition
succeeds.

```lean
example (p q r : Prop) (hp : p) (hq : q) (hr : r) : p ∧ q ∧ r := by
  constructor <;> (try constructor) <;> assumption
```

Be careful: ``repeat (try t)`` will loop forever, because the inner tactic never fails.

In a proof, there are often multiple goals outstanding. Parallel
sequencing is one way to arrange it so that a single tactic is applied
to multiple goals, but there are other ways to do this. For example,
``all_goals t`` applies ``t`` to all open goals:

```lean
example (p q r : Prop) (hp : p) (hq : q) (hr : r) : p ∧ q ∧ r := by
  constructor
  all_goals (try constructor)
  all_goals assumption
```

In this case, the ``any_goals`` tactic provides a more robust solution.
It is similar to ``all_goals``, except it fails unless its argument
succeeds on at least one goal.

```lean
example (p q r : Prop) (hp : p) (hq : q) (hr : r) : p ∧ q ∧ r := by
  constructor
  any_goals constructor
  any_goals assumption
```

The first tactic in the ``by`` block below repeatedly splits
conjunctions:

```lean
example (p q r : Prop) (hp : p) (hq : q) (hr : r) :
      p ∧ ((p ∧ q) ∧ r) ∧ (q ∧ r ∧ p) := by
  repeat (any_goals constructor)
  all_goals assumption
```

In fact, we can compress the full tactic down to one line:

```lean
example (p q r : Prop) (hp : p) (hq : q) (hr : r) :
      p ∧ ((p ∧ q) ∧ r) ∧ (q ∧ r ∧ p) := by
  repeat (any_goals (first | constructor | assumption))
```

The combinator ``focus t`` ensures that ``t`` only effects the current
goal, temporarily hiding the others from the scope. So, if ``t``
ordinarily only effects the current goal, ``focus (all_goals t)`` has
the same effect as ``t``.

Rewriting
---------

The ``rewrite`` tactic (abbreviated ``rw``) and the ``simp`` tactic
were introduced briefly in [Calculational Proofs](./quantifiers_and_equality.md#calculational_proofs). In this
section and the next, we discuss them in greater detail.

The ``rewrite`` tactic provides a basic mechanism for applying
substitutions to goals and hypotheses, providing a convenient and
efficient way of working with equality. The most basic form of the
tactic is ``rewrite [t]``, where ``t`` is a term whose type asserts an
equality. For example, ``t`` can be a hypothesis ``h : x = y`` in the
context; it can be a general lemma, like
``add_comm : ∀ x y, x + y = y + x``, in which the rewrite tactic tries to find suitable
instantiations of ``x`` and ``y``; or it can be any compound term
asserting a concrete or general equation. In the following example, we
use this basic form to rewrite the goal using a hypothesis.

```lean
example (f : Nat → Nat) (k : Nat) (h₁ : f 0 = 0) (h₂ : k = 0) : f k = 0 := by
  rw [h₂] -- replace k with 0
  rw [h₁] -- replace f 0 with 0
```

In the example above, the first use of ``rw`` replaces ``k`` with
``0`` in the goal ``f k = 0``. Then, the second one replaces ``f 0``
with ``0``. The tactic automatically closes any goal of the form
``t = t``. Here is an example of rewriting using a compound expression:

```lean
example (x y : Nat) (p : Nat → Prop) (q : Prop) (h : q → x = y)
        (h' : p y) (hq : q) : p x := by
  rw [h hq]; assumption
```

Here, ``h hq`` establishes the equation ``x = y``. The parentheses
around ``h hq`` are not necessary, but we have added them for clarity.

Multiple rewrites can be combined using the notation ``rw [t_1, ..., t_n]``,
which is just shorthand for ``rw t_1; ...; rw t_n``. The previous example can be written as follows:

```lean
example (f : Nat → Nat) (k : Nat) (h₁ : f 0 = 0) (h₂ : k = 0) : f k = 0 := by
  rw [h₂, h₁]
```

By default, ``rw`` uses an equation in the forward direction, matching
the left-hand side with an expression, and replacing it with the
right-hand side. The notation ``←t`` can be used to instruct the
tactic to use the equality ``t`` in the reverse direction.

```lean
example (f : Nat → Nat) (a b : Nat) (h₁ : a = b) (h₂ : f a = 0) : f b = 0 := by
  rw [←h₁, h₂]
```

In this example, the term ``←h₁`` instructs the rewriter to replace
``b`` with ``a``. In the editors, you can type the backwards arrow as
``\l``. You can also use the ascii equivalent, ``<-``.

Sometimes the left-hand side of an identity can match more than one
subterm in the pattern, in which case the ``rw`` tactic chooses the
first match it finds when traversing the term. If that is not the one
you want, you can use additional arguments to specify the appropriate
subterm.

```lean
example (a b c : Nat) : a + b + c = a + c + b := by
  rw [Nat.add_assoc, Nat.add_comm b, ← Nat.add_assoc]

example (a b c : Nat) : a + b + c = a + c + b := by
  rw [Nat.add_assoc, Nat.add_assoc, Nat.add_comm b]

example (a b c : Nat) : a + b + c = a + c + b := by
  rw [Nat.add_assoc, Nat.add_assoc, Nat.add_comm _ b]
```

In the first example above, the first step rewrites ``a + b + c`` to
``a + (b + c)``. Then next applies commutativity to the term
``b + c``; without specifying the argument, the tactic would instead rewrite
``a + (b + c)`` to ``(b + c) + a``. Finally, the last step applies
associativity in the reverse direction rewriting ``a + (c + b)`` to
``a + c + b``. The next two examples instead apply associativity to
move the parenthesis to the right on both sides, and then switch ``b``
and ``c``. Notice that the last example specifies that the rewrite
should take place on the right-hand side by specifying the second
argument to ``Nat.add_comm``.

By default, the ``rewrite`` tactic affects only the goal. The notation
``rw [t] at h`` applies the rewrite ``t`` at hypothesis ``h``.

```lean
example (f : Nat → Nat) (a : Nat) (h : a + 0 = 0) : f a = f 0 := by
  rw [Nat.add_zero] at h
  rw [h]
```

The first step, ``rw [Nat.add_zero] at h``, rewrites the hypothesis ``a + 0 = 0`` to ``a = 0``.
Then the new hypothesis ``a = 0`` is used to rewrite the goal to ``f 0 = f 0``.

The ``rewrite`` tactic is not restricted to propositions.
In the following example, we use ``rw [h] at t`` to rewrite the hypothesis ``t : Tuple α n`` to ``t : Tuple α 0``.

```lean
def Tuple (α : Type) (n : Nat) :=
  { as : List α // as.length = n }

example (n : Nat) (h : n = 0) (t : Tuple α n) : Tuple α 0 := by
  rw [h] at t
  exact t
```

Using the Simplifier
--------------------

Whereas ``rewrite`` is designed as a surgical tool for manipulating a
goal, the simplifier offers a more powerful form of automation. A
number of identities in Lean's library have been tagged with the
``[simp]`` attribute, and the ``simp`` tactic uses them to iteratively
rewrite subterms in an expression.

```lean
example (x y z : Nat) (p : Nat → Prop) (h : p (x * y))
        : (x + 0) * (0 + y * 1 + z * 0) = x * y := by
  simp

example (x y z : Nat) (p : Nat → Prop) (h : p (x * y))
        : p ((x + 0) * (0 + y * 1 + z * 0)) := by
  simp; assumption
```

In the first example, the left-hand side of the equality in the goal
is simplified using the usual identities involving 0 and 1, reducing
the goal to ``x * y = x * y``. At that point, ``simp`` applies
reflexivity to finish it off. In the second example, ``simp`` reduces
the goal to ``p (x * y)``, at which point the assumption ``h``
finishes it off. Here are some more examples
with lists:

```lean
open List

example (xs : List Nat)
        : reverse (xs ++ [1, 2, 3]) = [3, 2, 1] ++ reverse xs := by
 simp

example (xs ys : List α)
        : length (reverse (xs ++ ys)) = length xs + length ys := by
 simp [Nat.add_comm]
```

As with ``rw``, you can use the keyword ``at`` to simplify a hypothesis:

```lean
example (x y z : Nat) (p : Nat → Prop)
        (h : p ((x + 0) * (0 + y * 1 + z * 0))) : p (x * y) := by
  simp at h; assumption
```

Moreover, you can use a "wildcard" asterisk to simplify all the hypotheses and the goal:

```lean
attribute [local simp] Nat.mul_comm Nat.mul_assoc Nat.mul_left_comm
attribute [local simp] Nat.add_assoc Nat.add_comm Nat.add_left_comm

example (w x y z : Nat) (p : Nat → Prop)
        (h : p (x * y + z * w  * x)) : p (x * w * z + y * x) := by
  simp at *; assumption

example (x y z : Nat) (p : Nat → Prop)
        (h₁ : p (1 * x + y)) (h₂ : p  (x * z * 1))
        : p (y + 0 + x) ∧ p (z * x) := by
  simp at * <;> constructor <;> assumption
```

For operations that are commutative and associative, like
multiplication on the natural numbers, the simplifier uses these two
facts to rewrite an expression, as well as *left commutativity*. In
the case of multiplication the latter is expressed as follows:
``x * (y * z) = y * (x * z)``. The ``local`` modifier tells the simplifier
to use these rules in the current file (or section or namespace, as
the case may be). It may seem that commutativity and
left-commutativity are problematic, in that repeated application of
either causes looping. But the simplifier detects identities that
permute their arguments, and uses a technique known as *ordered
rewriting*. This means that the system maintains an internal ordering
of terms, and only applies the identity if doing so decreases the
order. With the three identities mentioned above, this has the effect
that all the parentheses in an expression are associated to the right,
and the expressions are ordered in a canonical (though somewhat
arbitrary) way. Two expressions that are equivalent up to
associativity and commutativity are then rewritten to the same
canonical form.

```lean
# attribute [local simp] Nat.mul_comm Nat.mul_assoc Nat.mul_left_comm
# attribute [local simp] Nat.add_assoc Nat.add_comm Nat.add_left_comm
example (w x y z : Nat) (p : Nat → Prop)
        : x * y + z * w  * x = x * w * z + y * x := by
  simp

example (w x y z : Nat) (p : Nat → Prop)
        (h : p (x * y + z * w  * x)) : p (x * w * z + y * x) := by
  simp; simp at h; assumption
```

As with ``rewrite``, you can send ``simp`` a list of facts to use,
including general lemmas, local hypotheses, definitions to unfold, and
compound expressions. The ``simp`` tactic also recognizes the ``←t``
syntax that ``rewrite`` does. In any case, the additional rules are
added to the collection of identities that are used to simplify a
term.

```lean
def f (m n : Nat) : Nat :=
  m + n + m

example {m n : Nat} (h : n = 1) (h' : 0 = m) : (f m n) = n := by
  simp [h, ←h', f]
```

A common idiom is to simplify a goal using local hypotheses:


```lean
example (f : Nat → Nat) (k : Nat) (h₁ : f 0 = 0) (h₂ : k = 0) : f k = 0 := by
  simp [h₁, h₂]
```

To use all the hypotheses present in the local context when
simplifying, we can use the wildcard symbol, ``*``:

```lean
example (f : Nat → Nat) (k : Nat) (h₁ : f 0 = 0) (h₂ : k = 0) : f k = 0 := by
  simp [*]
```

여기 또 다른 예제가 있습니다.

```lean
example (u w x y z : Nat) (h₁ : x = y + z) (h₂ : w = u + x)
        : w = z + y + u := by
  simp [*, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
```

The simplifier will also do propositional rewriting. For example,
using the hypothesis ``p``, it rewrites ``p ∧ q`` to ``q`` and ``p ∨
q`` to ``true``, which it then proves trivially. Iterating such
rewrites produces nontrivial propositional reasoning.

```lean
example (p q : Prop) (hp : p) : p ∧ q ↔ q := by
  simp [*]

example (p q : Prop) (hp : p) : p ∨ q := by
  simp [*]

example (p q r : Prop) (hp : p) (hq : q) : p ∧ (q ∨ r) := by
  simp [*]
```

The next example simplifies all the hypotheses, and then uses them to prove the goal.

```lean
example (u w x x' y y' z : Nat) (p : Nat → Prop)
        (h₁ : x + 0 = x') (h₂ : y + 0 = y')
        : x + y + 0 = x' + y' := by
  simp at *
  simp [*]
```

One thing that makes the simplifier especially useful is that its
capabilities can grow as a library develops. For example, suppose we
define a list operation that symmetrizes its input by appending its
reversal:

```lean
def mk_symm (xs : List α) :=
  xs ++ xs.reverse
```

Then for any list ``xs``, ``reverse (mk_symm xs)`` is equal to ``mk_symm xs``,
which can easily be proved by unfolding the definition:

```lean
# def mk_symm (xs : List α) :=
#  xs ++ xs.reverse
theorem reverse_mk_symm (xs : List α)
        : (mk_symm xs).reverse = mk_symm xs := by
  simp [mk_symm]
```

We can now use this theorem to prove new results:

```lean
# def mk_symm (xs : List α) :=
#  xs ++ xs.reverse
# theorem reverse_mk_symm (xs : List α)
#        : (mk_symm xs).reverse = mk_symm xs := by
#  simp [mk_symm]
example (xs ys : List Nat)
        : (xs ++ mk_symm ys).reverse = mk_symm ys ++ xs.reverse := by
  simp [reverse_mk_symm]

example (xs ys : List Nat) (p : List Nat → Prop)
        (h : p (xs ++ mk_symm ys).reverse)
        : p (mk_symm ys ++ xs.reverse) := by
  simp [reverse_mk_symm] at h; assumption
```

But using ``reverse_mk_symm`` is generally the right thing to do, and
it would be nice if users did not have to invoke it explicitly. You can
achieve that by marking it as a simplification rule when the theorem
is defined:

```lean
# def mk_symm (xs : List α) :=
#  xs ++ xs.reverse
@[simp] theorem reverse_mk_symm (xs : List α)
        : (mk_symm xs).reverse = mk_symm xs := by
  simp [mk_symm]

example (xs ys : List Nat)
        : (xs ++ mk_symm ys).reverse = mk_symm ys ++ xs.reverse := by
  simp

example (xs ys : List Nat) (p : List Nat → Prop)
        (h : p (xs ++ mk_symm ys).reverse)
        : p (mk_symm ys ++ xs.reverse) := by
  simp at h; assumption
```

The notation ``@[simp]`` declares ``reverse_mk_symm`` to have the
``[simp]`` attribute, and can be spelled out more explicitly:

```lean
# def mk_symm (xs : List α) :=
#  xs ++ xs.reverse
theorem reverse_mk_symm (xs : List α)
        : (mk_symm xs).reverse = mk_symm xs := by
  simp [mk_symm]

attribute [simp] reverse_mk_symm

example (xs ys : List Nat)
        : (xs ++ mk_symm ys).reverse = mk_symm ys ++ xs.reverse := by
  simp

example (xs ys : List Nat) (p : List Nat → Prop)
        (h : p (xs ++ mk_symm ys).reverse)
        : p (mk_symm ys ++ xs.reverse) := by
  simp at h; assumption
```

The attribute can also be applied any time after the theorem is declared:

```lean
# def mk_symm (xs : List α) :=
#  xs ++ xs.reverse
theorem reverse_mk_symm (xs : List α)
        : (mk_symm xs).reverse = mk_symm xs := by
  simp [mk_symm]

example (xs ys : List Nat)
        : (xs ++ mk_symm ys).reverse = mk_symm ys ++ xs.reverse := by
  simp[reverse_mk_symm]

attribute [simp] reverse_mk_symm

example (xs ys : List Nat) (p : List Nat → Prop)
        (h : p (xs ++ mk_symm ys).reverse)
        : p (mk_symm ys ++ xs.reverse) := by
  simp at h; assumption
```

Once the attribute is applied, however, there is no way to permanently
remove it; it persists in any file that imports the one where the
attribute is assigned. As we will discuss further in
[Attributes](TBD), one can limit the scope of an attribute to the
current file or section using the ``local`` modifier:

```lean
# def mk_symm (xs : List α) :=
#  xs ++ xs.reverse
theorem reverse_mk_symm (xs : List α)
        : (mk_symm xs).reverse = mk_symm xs := by
  simp [mk_symm]

section
attribute [local simp] reverse_mk_symm

example (xs ys : List Nat)
        : (xs ++ mk_symm ys).reverse = mk_symm ys ++ xs.reverse := by
  simp

example (xs ys : List Nat) (p : List Nat → Prop)
        (h : p (xs ++ mk_symm ys).reverse)
        : p (mk_symm ys ++ xs.reverse) := by
  simp at h; assumption
end
```

Outside the section, the simplifier will no longer use
``reverse_mk_symm`` by default.

Note that the various ``simp`` options we have discussed --- giving an
explicit list of rules, and using ``at`` to specify the location --- can be combined,
but the order they are listed is rigid. You can see the correct order
in an editor by placing the cursor on the ``simp`` identifier to see
the documentation string that is associated with it.

There are two additional modifiers that are useful. By default,
``simp`` includes all theorems that have been marked with the
attribute ``[simp]``. Writing ``simp only`` excludes these defaults,
allowing you to use a more explicitly crafted list of
rules. In the examples below, the minus sign and
``only`` are used to block the application of ``reverse_mk_symm``.

```lean
def mk_symm (xs : List α) :=
  xs ++ xs.reverse
@[simp] theorem reverse_mk_symm (xs : List α)
        : (mk_symm xs).reverse = mk_symm xs := by
  simp [mk_symm]

example (xs ys : List Nat) (p : List Nat → Prop)
        (h : p (xs ++ mk_symm ys).reverse)
        : p (mk_symm ys ++ xs.reverse) := by
  simp at h; assumption

example (xs ys : List Nat) (p : List Nat → Prop)
        (h : p (xs ++ mk_symm ys).reverse)
        : p ((mk_symm ys).reverse ++ xs.reverse) := by
  simp [-reverse_mk_symm] at h; assumption

example (xs ys : List Nat) (p : List Nat → Prop)
        (h : p (xs ++ mk_symm ys).reverse)
        : p ((mk_symm ys).reverse ++ xs.reverse) := by
  simp only [List.reverse_append] at h; assumption
```

Extensible Tactics
-----------------

In the following example, we define the notation `triv` using the command `syntax`.
Then, we use the command `macro_rules` to specify what should
be done when `triv` is used. You can provide different expansions, and the tactic
interpreter will try all of them until one succeeds.

```lean
-- Define a new tactic notation
syntax "triv" : tactic

macro_rules
  | `(tactic| triv) => `(tactic| assumption)

example (h : p) : p := by
  triv

-- You cannot prove the following theorem using `triv`
-- example (x : α) : x = x := by
--  triv

-- Let's extend `triv`. The tactic interpreter
-- tries all possible macro extensions for `triv` until one succeeds
macro_rules
  | `(tactic| triv) => `(tactic| rfl)

example (x : α) : x = x := by
  triv

example (x : α) (h : p) : x = x ∧ p := by
  apply And.intro <;> triv

-- We now add a (recursive) extension
macro_rules | `(tactic| triv) => `(tactic| apply And.intro <;> triv)

example (x : α) (h : p) : x = x ∧ p := by
  triv
```

연습문제
---------

1. Go back to the exercises in [Chapter Propositions and
   Proofs](./propositions_and_proofs.md) and
   [Chapter Quantifiers and Equality](./quantifiers_and_equality.md) and
   redo as many as you can now with tactic proofs, using also ``rw``
   and ``simp`` as appropriate.

2. Use tactic combinators to obtain a one line proof of the following:

```lean
 example (p q r : Prop) (hp : p)
         : (p ∨ q ∨ r) ∧ (q ∨ p ∨ r) ∧ (q ∨ r ∨ p) := by
   admit
```
