전략
=======

이 장에서는 *전략*을 사용하여 증명을 구성하는 다른 접근 방식을 설명합니다.  증명 항는 수학적 증명을 나타냅니다. 전술은 그러한 증명를 구축하는 법을 설명하는 명령 혹은 지시사항입니다. 비형식적으로 "앞 방향으로 증명하고, 정의를 펼치고, 이전 보조 정리를 적용하고, 단순화하라"고 말함으로써 수학 증명을 시작할 수 있습니다. 이것이 독자에게 연관된 증명을 찾는 법을 알려주는 지시사항인 것처럼 전략은 린에게 증명 항를 구성하는 법을 알려주는 지시사항입니다. 그들은 자연스럽게 증명을 분해하고 한 번에 한 단계씩 목표를 달성하는 점진적인 증명 작성 스타일을 지원합니다.

우리는 전략의 연쇄로 이뤄진 증명을 "전략 스타일" 증명으로 설명할 것이고, 우리가 이제까지 보았던 증명 항를 작성하는 방법을 "항 스타일" 증명이라고 하는 것과 대조할 것입니다. 각 스타일은 그것의 장단점을 가지고 있습니다. 예를 들어, 전략 스타일의 증명은 독자가 각 명령의 결과를 예측하거나 추측해야 하기 때문에 읽기 더 어려울 수 있습니다. 그러나 그것들은 더 짧고 더 쓰기 쉬울 수 있습니다. 게다가 자동화된 절차 자체가 전략이므로 전략은 린의 자동화를 사용하기 위한 관문을 제공합니다.

전략 모드 진입
--------------------

개념적으로, 정리를 진술하거나 ``have`` 구문을 도입하여 기대하는 유형으로 항를 구성하라는 목표를 만듭니다. 예를 들어 , 다음은 상수 ``p q : Prop``과 ``hp : p``,``hq : q``가 있는 맥락에 대해 ``p ∧ q ∧ p``형의 항을 생성하라는 목표를 만듭니다.

```lean
theorem test (p q : Prop) (hp : p) (hq : q) : p ∧ q ∧ p :=
  sorry
```

여러분은 이 목표를 다음과 같이 작성할 수 있습니다.

```
    p : Prop, q : Prop, hp : p, hq : q ⊢ p ∧ q ∧ p
```

실제로 위의 예에서 "sorry"를 밑줄로 바꾸면 린은 이 목표가 해결되지 않은 것으로 보고합니다.

일반적으로 명시적인 항을 작성하여 이 목표를 달성합니다. 그러나 항을 기대하는 어디든지 린은 우리가 ``by <tactics>`` 블록 대신 이를 삽입하게 해줍니다. 여기서 세미콜론이나 줄 분리자로 분리된 ``<tactics>``은 일련의 명령들 입니다. 여러분은 위의 정리를 그와 같이 증명할 수 있습니다.

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

``apply`` 전략은 0 또는 그 이상의 인수가 있는 함수를 나타내는 것으로 간주되는 표현식에 사용합니다. 결론을 현재 목표의 표현식과 통합하고 이후 인수가 종속되지 않는 한 나머지 인수에 대한 새 목표를 생성합니다. 위의 예에서 ``apply And.intro`` 명령은 두 하위 목표를 얻습니다.

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

첫 번째 목표는 ``exact hp``명령으로 충족됩니다. ``exact`` 명령은 주어진 식이 목표를 정확히 채움을 알리는 신호인 ``apply``의 변형입니다. 전략 증명에서 이것은 사용하기에 좋은 형태입니다. 
왜냐하면 그것의 실패는 무언가 잘못되었음을 알려주기 때문입니다. 협력기는 적용될 표현식을 처리할 때 고려하는 목표에 의해 주어진 기대 유형을 받으므로
이것은 ``apply``보다 더 강건합니다. 하지만 이 경우 ``apply``도 잘 작동할 것입니다.

여러분은 ``#print`` 명령으로 증명 항의 결과를 볼 수 있습니다.

```lean
# theorem test (p q : Prop) (hp : p) (hq : q) : p ∧ q ∧ p := by
#  apply And.intro
#  exact hp
#  apply And.intro
#  exact hq
#  exact hp
#print test
```

여러분은 점진적으로 전략 스크립트를 작성할 수 있습니다. VS Code에서 여러분은  ``Ctrl-Shift-Enter``을 눌러 메시지을 보고자 창을 열 수 있습니다. 
그러면 그 창은 전략 블록 속의 커서가 어디에 있든지 간에 현재 목표를 여러분에게 보여줄 것입니다. Emacs에서 여러분은 임의의 줄의 끝에서 ``C-c C-g``을 눌러 목표를 볼 수 있습니다. 
아니면 마지막 전략의 첫 문자 뒤에 커서를 놓으면 불완전한 증명에 대한 남은 목표를 볼 수 있습니다. 만일 증명이 불완전하다면, 토큰 ``by``은 빨간색 구불구불한 선으로 장식됩니다.
그리고 오류 메시지가 남은 목표를 포함됩니다.

전략 명령은 하나의 식별자 뿐만 아니라 복합적인 식을 받을 수 있습니다. 다음은 이전의 증명보다 더 짧은 버전의 증명입니다.

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

다수의 전략들은 세미콜론으로 연결해 한 줄로 작성될 수 있습니다.

```lean
theorem test (p q : Prop) (hp : p) (hq : q) : p ∧ q ∧ p := by
  apply And.intro hp; exact And.intro hq hp
```

다수의 하위 목표를 생성할 수 있는 전략은 이들에 태그를 붙입니다. 예를 들어, 전략  ``apply And.intro``는 첫 목표를 ``left``으로,
두 번째 목표를 ``right``라고 표식을 붙입니다. ``apply`` 전략의 경우 태그는 ``And.intro`` 선언에서 사용된 매개변수의 이름으로부터 추론됩니다. 여러분은 여러분의 전략을 ``case <tag> => <tactics>``기호를 사용해 구조화할 수 있습니다. 다음은 이 장의 첫 전략 증명의 구조화된 버전입니다.

```lean
theorem test (p q : Prop) (hp : p) (hq : q) : p ∧ q ∧ p := by
  apply And.intro
  case left => exact hp
  case right =>
    apply And.intro
    case left => exact hq
    case right => exact hp
```

여러분은 ``case`` 기호를 사용해서 하위목표 ``left``보다 먼저 ``right``을 풀 수 있습니다.

```lean
theorem test (p q : Prop) (hp : p) (hq : q) : p ∧ q ∧ p := by
  apply And.intro
  case right =>
    apply And.intro
    case left => exact hq
    case right => exact hp
  case left => exact hp
```

린은 ``case`` 블록 속의 다른 목표를 숨깁니다. 우리는 이를 선택한 목표에 "초점을 맞췄다"고 합니다.  게다가 린은 선택된 목표가 ``case`` 블록의 끝에서 완전히 풀리지 않았다면 오류를 표시합니다.

간단한 하위목표에 대해 그것의 태그을 이용해 하위목표를 선택하는 것은 불필요할 수 있지만
그래도 여러분은 여전히 증명을 구조화하길 원할지도 모릅니다. 린은 또 구조화한 증명에 대해 "총알(bullet)" 기호 ``.<tactics>`` (혹은 ``· <tactics>``)를 제공합니다.`` 

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

``apply``과 ``exact``에 더해 또 다른 유용한 전략은 가정을 도입하는 ``intro``입니다. 다음은 이전 장에서 증명한 명제 논리의 항등식들 중 전략으로 증명해 볼 예제입니다.

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

``intro``명령은 일반적으로 임의 유형의 변수를 도입하는데 사용됩니다.

```lean
example (α : Type) : α → α := by
  intro a
  exact a

example (α : Type) : ∀ x : α, x = x := by
  intro x
  exact Eq.refl x
```

여러분은 여러 변수들을 도입하는데 사용할 수 있습니다.

```lean
example : ∀ a b c : Nat, a = b → a = c → c = b := by
  intro a b c h₁ h₂
  exact Eq.trans (Eq.symm h₂) h₁
```

 ``apply`` 전략이 함수의 활용을 상호작용 방식으로 구성하는 명령인 것처럼 
``intro`` 전략은 상호작용 방식으로 함수 추상화를 구성하는 명령입니다. 
(즉, ``fun x => e`` 꼴의 항들)  람다 추상화 기호처럼 ``intro`` 전략은 암시적인 ``match``를 쓸 수 있도록 해줍니다.

```lean
example (α : Type) (p q : α → Prop) : (∃ x, p x ∧ q x) → ∃ x, q x ∧ p x := by
  intro ⟨w, hpw, hqw⟩
  exact ⟨w, hqw, hpw⟩
```

여러분은 ``match`` 표현식처럼 여러 가지 변형들을 제공할 수도 있습니다.

```lean
example (α : Type) (p q : α → Prop) : (∃ x, p x ∨ q x) → ∃ x, q x ∨ p x := by
  intro
    | ⟨w, Or.inl h⟩ => exact ⟨w, Or.inr h⟩
    | ⟨w, Or.inr h⟩ => exact ⟨w, Or.inl h⟩
```

``intros`` 전략은 어떠한 인수 없이도 사용될 수 있습니다. 
가령, 그것은 이름을 정하고, 가능한 많은 변수를 도입할 수 있습니다. 여러분은 곧 이에 대한 예를 볼 것입니다.

``assumption`` 전략은 현재 목표의 맥락 속 가정을 훑어 봅니다. 
그리고 결론과 대응되는 가정이 있다면 그것을 목표에 적용합니다.

```lean
example (x y z w : Nat) (h₁ : x = y) (h₂ : y = z) (h₃ : z = w) : x = w := by
  apply Eq.trans h₁
  apply Eq.trans h₂
  assumption   -- applied h₃
```

이 전략은 필요하다면 결론의 메타변수들을 통합할 것 입니다.

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

린에 의해 자동으로 생성된 이름들은 기본적으로 접근할 수 없습니다. 그 이유는 여러분의 전략 증명이 자동으로 생성된 이름에 의존하지 않고 증명을 더 견고하게 만들기 위함입니다.
하지만 여러분은 ``unhygienic`` 조합자를 사용해서 이 제한을 풀 수 있습니다.

```lean
example : ∀ a b c : Nat, a = b → a = c → c = b := by unhygienic
  intros
  apply Eq.trans
  apply Eq.symm
  exact a_2
  exact a_1
```

혹은 ``rename_i`` 전략으로 맥락에서 가장 최근에 접근 불가한 이름을 다시 지을 수 있습니다.
다음 예제에서 ``rename_i h1 _ h2`` 전략은 맥락 속  마지막 세 가정 중 두 개의 이름을 바꿉니다.

```lean
example : ∀ a b c d : Nat, a = b → a = d → a = c → c = b := by
  intros
  rename_i h1 _ h2
  apply Eq.trans
  apply Eq.symm
  exact h2
  exact h1
```

``rfl`` 전략은 ``exact rfl``에 대한 문법 설탕입니다.
```lean
example (y : Nat) : (fun x : Nat => 0) y = 0 :=
  by rfl
```

조합자 ``repeat``는 한 전략을 여러 번 적용하는데 사용될 수 있습니다.

```lean
example : ∀ a b c : Nat, a = b → a = c → c = b := by
  intros
  apply Eq.trans
  apply Eq.symm
  repeat assumption
```

때때로 유용한 또 다른 전략은 ``revert``전략입니다. 이는 ``intro``의 역 입니다.

```lean
example (x : Nat) : x = x := by
  revert x
  -- goal is ⊢ ∀ (x : Nat), x = x
  intro y
  -- goal is y : Nat ⊢ y = y
  rfl
```

가정을 목표 속으로 옮겨 함의를 얻습니다.

```lean
example (x y : Nat) (h : x = y) : y = x := by
  revert h
  -- goal is x y : Nat ⊢ x = y → y = x
  intro h₁
  -- goal is x y : ℕ, h₁ : x = y ⊢ y = x
  apply Eq.symm
  assumption
```

그러나 ``revert``는 맥락 속 요소들 뿐만 아니라 그에 의존하는 맥락의 후행 요소도 되돌려 놓는다는 점에서 아주 영리합니다. 예를 들어, 위의 예제에서 ``x``를 되돌리는 것은 그것을 따르는 ``h``도 가져옵니다.

```lean
example (x y : Nat) (h : x = y) : y = x := by
  revert x
  -- goal is y : Nat ⊢ ∀ (x : Nat), x = y → y = x
  intros
  apply Eq.symm
  assumption
```

또 맥락 속 다수의 요소들을 한 번에 되돌릴 수 있습니다.
```lean
example (x y : Nat) (h : x = y) : y = x := by
  revert x y
  -- goal is ⊢ ∀ (x y : Nat), x = y → y = x
  intros
  apply Eq.symm
  assumption
```

여러분은 국부적인 맥락 속 요소 즉, 지역 변수나 가정만 ``되돌릴`` 수 있습니다. 하지만 목표 속 임의의 표현식을 ``generalize`` 전략을 사용해 새 변수로 바꿀 수 있습니다.

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

위의 표기에 대한 기억법은 여러분이 ``3``을 임의의 변수 ``x`` 설정하여 목표을 일반화시키는 것입니다. 조심하세요. 모든 일반화가 목표의 유효성을 보존하지는 않습니다. 여기서 ``generalize``는 ``rfl``을 사용해 증명할 수 있는 목표를 
증명할 수 없는 것으로 바꿉니다.

```lean
example : 2 + 3 = 5 := by
  generalize  3 = x
  -- goal is x : Nat ⊢ 2 + x = 5
  admit
```

이 예제에서 ``admit`` 전략은 증명항 ``sorry``와 유사합니다. 이것은 현재 목표를 끝내고, ``sorry``를 사용했다는 경고를 만듭니다. 이전 목표의 유효성을 보존하기 위해 ``generalize`` 전략은 ``3``이 
``x``로 대체되었다는 사실을 기록하게 해줍니다. 여러분이 해야할 것은 레이블을 제공하는 것이고 그러면 ``generalize``가 지역 맥락에서 이를 사용해 할당물을 저장하는데 사용합니다.

```lean
example : 2 + 3 = 5 := by
  generalize h : 3 = x
  -- goal is x : Nat, h : 3 = x ⊢ 2 + x = 5
  rw [← h]
```

여기 ``rewrite`` 전략은 ``rw``로 축약되었고, ``h``로 ``x``가 다시 ``3``으로 바뀌게 했습니다. ``rewrite``전략은 아래에서 더 논의할 것 입니다.


이 외의 전략들
------------

몇몇 추가적인 전략들은 명제와 데이터를 생성하고 파괴하는데 유용합니다. 예를 들어, ``p ∨ q``꼴의 목표에 적용했을 때, 여러분은 ``apply Or.inl``과 ``apply
Or.inr`` 같은 전략들을 사용합니다.  반대로 ``cases`` 전략은 논리합를 분해하는데 사용할 수 있습니다.

```lean
example (p q : Prop) : p ∨ q → q ∨ p := by
  intro h
  cases h with
  | inl hp => apply Or.inr; exact hp
  | inr hq => apply Or.inl; exact hq
```

이 문법은 `match` 표현식에서 사용된 것과 비슷합니다.
새로운 하위 목표는 원하는 순서로 풀 수 있습니다.

```lean
example (p q : Prop) : p ∨ q → q ∨ p := by
  intro h
  cases h with
  | inr hq => apply Or.inl; exact hq
  | inl hp => apply Or.inr; exact hp
```

여러분은 (비구조화된)``cases``를 ``with`` 없이 각 대체표현된 전략에 대해 쓸 수 있습니다.

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

또 여러분은 조합자  ``tac1 <;> tac2``를 ``tac1``을 사용해 생긴 각 하위 목표에
``tac2``를 적용하는데 쓸 수 있습니다.

```lean
example (p : Prop) : p ∨ p → p := by
  intro h
  cases h <;> assumption
```

여러분은 비구조화된 ``cases`` 전략을  ``case``와 ``.`` 기호로 결합할 수 있습니다.

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


``cases`` 전략은 논리곱를 분해하는데 사용될 수 있습니다.

```lean
example (p q : Prop) : p ∧ q → q ∧ p := by
  intro h
  cases h with
  | intro hp hq => constructor; exact hq; exact hp
```

이 예제에서, 한 쌍의 가정 ``hp : p``과 ``hq : q``로 ``h : p ∧ q``가 대체되어 
``cases`` 전략이 적용된 뒤에는 한 목표만 남습니다. ``constructor`` 전략은 논리곱 ``And.intro``의 유일한 생성자를 적용합니다. 이 전략으로 이전 섹션의 예제를 다음과 같이 재작성할 수 있습니다.

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

[귀납형 장](./inductive_types.md)에서 이 전략들은 꽤나 일반적임을 볼 것입니다. ``cases`` 전략은 귀납적으로 정의된 유형의 임의의 원소를 분해하는데 사용될 수 있습니다.
``constructor``는 항상 귀납적으로 정의된 유형의 첫 적용 가능한 생성자를 사용합니다.
예를 들어, 여러분은``cases``와 ``constructor``을 존재 한정기호와 사용할 수 있습니다.

```lean
example (p q : Nat → Prop) : (∃ x, p x) → ∃ x, p x ∨ q x := by
  intro h
  cases h with
  | intro x px => constructor; apply Or.inl; exact px
```

여기서 ``constructor`` 전략은 존재 주장의 첫 구성요소를 암시적인 ``x``의 값으로 남깁니다. 이는 메타변수로 나타나며 나중에 반드시 인스턴스화되어야 합니다. 이전 예제에서 메타변수의 적절한 값은``exact px`` 전략에 의해 결정됩니다. 
그 이유는 ``px``가 ``p x``형을 갖기 때문입니다. 여러분이 명시적으로 존재 한정기호에 대한 발견을 나타내길 원한다면,
``exists`` 전략을 대신 사용할 수 있습니다.

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

이 전략들은 명제와 마찬가지로 데이터에도 사용될 수 있습니다. 다음 두 예제에서, 이들은 곱과 합 유형의 교환하는 함수를 정의하는데 사용됩니다.

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

우리가 변수로 선택한 이름에 한해 한 정의들은 
논리곱와 논리합에 대한 유사한 명제의 증명과 
동일함을 보세요. ``cases`` 전략은 자연수의 경우를 나눕니다.

```lean
open Nat
example (P : Nat → Prop) (h₀ : P 0) (h₁ : ∀ n, P (succ n)) (m : Nat) : P m := by
 cases m with
 | zero    => exact h₀
 | succ m' => exact h₁ m'
```

``cases`` 전략 그리고 그것의 동반자인 ``induction`` 전략은 
[귀납형을 위한 전략](./inductive_types.md#tactics_for_inductive_types)  섹션에서 더욱 상세히 논의될 예정입니다.

``contradiction`` 전략은 현재 목표의 가정들 중에 서로 모순인 것을 탐색합니다.

```lean
example (p q : Prop) : p ∧ ¬ p → q := by
  intro h
  cases h
  contradiction
```

여러분은 전략 블록에서 ``match``를 사용할 수 있습니다.

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

여러분은 ``intro h``를 ``match h ...``와 "합칠" 수 있고 이전 예제를 다음과 같이 쓸 수 있습니다.

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

전략 증명 구조화하기
-------------------------

전략들은 종종 증명을 세우는 효율적인 방식을 제공합니다. 그러나 
지시사항들의 긴 나열은 인수(argument)의 구조를 모호하게 할 수 있습니다. 이 섹션은 더욱 가독성있고 강건한 전략 스타일의 증명을 구조화하여
만드는 데 도움을 주는 몇 가지 방식을 설명할 것 입니다.

린의 증명 작성 문법에 대해 좋은 점은 항 스타일과 전략 스타일의 증명을 혼합할 수 있고, 
이들 사이를 자유로이 왕래할 수 있다는 것입니다. 예를 들어 ``apply``와``exact`` 전략은 
``have``, ``show`` 등등을 사용해 만든 임의의 항을 기대합니다. 반대로 임의의 린 항을 작성했다면 ``by`` 블럭을 삽입하여 
전략모드를 불러올 수 있습니다. 다음은 좀 간단한 예제입니다.

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

다음은 좀 더 자연스러운 예제입니다.

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

사실 증명 항에서 ``show`` 표현식과 비슷한 ``show`` 전략이 있습니다. 전략모드에 남아있는 동안 이것는 단순히 막 풀려고 하는 목표의 유형을 선언합니다.

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

``show`` 전략은 사실 정의상으로 동등한 무언가로 목표를 다시 쓰는데 사용될 수 있습니다.

```lean
example (n : Nat) : n + 1 = Nat.succ n := by
  show Nat.succ n = Nat.succ n
  rfl
```

증명 항을 작성할 때처럼 ``have`` 전략은 새로운 하위목표를 도입합니다.

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

증명 항과 마찬가지로 여러분은  ``have`` 전략에서 레이블을 생략할 수 있습니다. 그 경우 
기본 레이블로 ``this``가 사용됩니다.

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

``have`` 전략에서 유형은 생략될 수 있습니다. 그래서 여러분은  ``have
hp := h.left``과 ``have hqr := h.right``을 쓸 수 있습니다.  사실 이 기호와 관련해서 유형과 레이블 모두를 생략할 수 있습니다. 
그 경우 이 새로운 사실은 ``this`` 레이블로 도입됩니다.

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

린은 또 ``have``전략과 유사한 ``let`` 전략을 갖고 있습니다. 
그러나 이것은 부가적인 사실 보다는 지역 정의를 도입하는데 사용됩니다. 이것은 증명 항에서 ``let``과 유사한 전략입니다.

```lean
example : ∃ x, x + 2 = 8 := by
  let a : Nat := 3 * 2
  exists a
  rfl
```

``have``처럼 여러분은  ``let a:= 3 * 2``와 같이 작성하여 유형을 암시적으로 둘 수 있습니다.  ``let``과 ``have`` 사이의 차이는 ``let``은 맥락 속에 지역 정의를 도입하여 
지역 선언의 정의가 증명 속에 펼쳐져 있게 합니다.

우리는 중첩된 전략 블럭을 만드는데 ``.``를 사용해왔습니다.  중첩된 블럭 속에 린은 첫 번째 목표에 집중하고 블록 끝에서도 완전히 풀리지 않는다면 오류를 발생시킵니다. 이는 전략의 도입으로 생긴 다수의 하위 목표를의 증명의 분할를 가리키는데 유용할 수 있습니다. ``.`` 표기는 공백 문자에 민감하고 전략 블럭의 끝인지 감지하는데 들여쓰기에 의존합니다. 혹은 중괄호와 세미콜론으로 전략 블록을 정의할 수 있습니다.

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

증명을 구조화하는데 들여쓰기를 사용하는 것은 유용합니다. 전략은 매번 한 개 이상의 하위 목표를 남겨두므로 
우리는 블럭과 인덴트 안에 그들을 둘러싸서 남은 하위목표들을 나눕니다.  따라서 ``foo`` 정리를 한 목표에 적용해 네 개의 하위 목표가 만들어 진다면 
증명은 이와 같이 보일 것이라 생각할 수 있습니다.

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

*Tactic combinators*은 이전의 전략으로부터 새 전략을 만드는 연산입니다. 순차 조합자는 이미 ``by`` 블럭 속에 암시적으로 있습니다.

```lean
example (p q : Prop) (hp : p) : p ∨ q :=
  by apply Or.inl; assumption
```

여기 ``apply Or.inl; assumption``는 ``apply Or.inl``을 
적용한 뒤 ``assumption``을 적용한 한 개의 전략과 기능적으로 동등합니다.

``t₁<;>  t₂``에서 ``<;>`` 연산자는 순차 연산의 *병렬적인* 버전을 제공합니다.
``t₁``가 현재 목표에 적용된 후 생기는 하위목표 *모두*에 ``t₂``를 적용합니다.

```lean
example (p q : Prop) (hp : p) (hq : q) : p ∧ q :=
  by constructor <;> assumption
```

이는 특히 생기는 목표가 균일한 방식으로 마무리 될 때 아니면 적어도 
그들 모두가 균일한 방식으로 진전을 만드는게 가능할 때 유용합니다.

 ``first | t₁ | t₂ | ... | tₙ``은 각각의  `tᵢ`에 대해 이 중 하나가 성공하거나 모두 실패할 때까지 적용됩니다.

```lean
example (p q : Prop) (hp : p) : p ∨ q := by
  first | apply Or.inl; assumption | apply Or.inr; assumption
```

첫 예제에서 왼쪽 분기는 성공했습니다. 반면 두 번째에서 성공한 것은 오른쪽의 것입니다.
다음 세 예제에서 동일한 복합 전략은 각 경우에서 성공합니다.

```lean
example (p q r : Prop) (hp : p) : p ∨ q ∨ r :=
  by repeat (first | apply Or.inl; assumption | apply Or.inr | assumption)

example (p q r : Prop) (hq : q) : p ∨ q ∨ r :=
  by repeat (first | apply Or.inl; assumption | apply Or.inr | assumption)

example (p q r : Prop) (hr : r) : p ∨ q ∨ r :=
  by repeat (first | apply Or.inl; assumption | apply Or.inr | assumption)
```

전략은 왼쪽의 논리합를 가정으로 즉시 풀려고 합니다.
만약 그것이 실패하면 이것은 논리합의 오른쪽에 초점을 맞춰 시도합니다. 그래도 
그것 성공하지 못하면, 가정 전략을 불러옵니다.

이제 여러분은 의심의 여지없이 그 전략은 실패함을 눈치챌 것입니다. 당연히, "실패" 상태는 *first* 조합자가 되돌아와 다음 전략을 시도하도록 야기합니다. 대개 자명한 방법일지라도 ``try`` 조합자는  항상 성공하는 전략을 세우고, 
``t``가 실패했음에도 ``try t``는 ``t``를 실행해 성공을 보고합니다. 이는 ``first | t | skip``과 동일합니다. 여기서 ``skip``은 
아무것도 하지 않는(그래서 그것의 실행은 성공하는) 전략입니다. 다음 예제에서 두 번째 ``constructor``는 논리곱 ``q ∧ r``의 오른쪽(논리합과 
논리곱은 오른쪽 결합성을 가짐을 기억하세요.)에서 성공합니다. 그러나 첫 번째에서는 실패합니다. ``try`` 전략은 순차적인 복합이 성공함을 보장합니다.

```lean
example (p q r : Prop) (hp : p) (hq : q) (hr : r) : p ∧ q ∧ r := by
  constructor <;> (try constructor) <;> assumption
```

조심하세요. ``repeat (try t)``의 내부 전략은 절대로 실패하지 않아서 무한루프에 빠질 것입니다.

증명에서는 미해결된 다수의 목표가 있습니다. 병렬 순차는 하나의 전략이 다수의 목표에 적용되게 배열하는 한 방법입니다. 
그러나 이를 다른 방법으로도 할 수 있습니다. 예를 들어 ``all_goals t``는 모든 끝나지 않은 목표에 ``t``를 적용합니다.

```lean
example (p q r : Prop) (hp : p) (hq : q) (hr : r) : p ∧ q ∧ r := by
  constructor
  all_goals (try constructor)
  all_goals assumption
```

이 경우에 ``any_goals`` 전략은 더 강건한 답을 제공합니다.
``any_goals``은 그것의 인수가 어느 한 목표에서도 성공하지 않는 한 
실패하는 경우를 제외하고 ``all_goals``과 유사합니다.

```lean
example (p q r : Prop) (hp : p) (hq : q) (hr : r) : p ∧ q ∧ r := by
  constructor
  any_goals constructor
  any_goals assumption
```

 ``by`` 블럭 아래에 첫 번째 전략은 반복적으로 논리곱을 나눕니다.

```lean
example (p q r : Prop) (hp : p) (hq : q) (hr : r) :
      p ∧ ((p ∧ q) ∧ r) ∧ (q ∧ r ∧ p) := by
  repeat (any_goals constructor)
  all_goals assumption
```

사실, 우리는 모든 전략을 한 줄로 압축시킬 수 있습니다.

```lean
example (p q r : Prop) (hp : p) (hq : q) (hr : r) :
      p ∧ ((p ∧ q) ∧ r) ∧ (q ∧ r ∧ p) := by
  repeat (any_goals (first | constructor | assumption))
```

조합자 ``focus t``은 일시적으로 이 범위로부터 다른 것들을 숨겨 
``t``가 오직 현재 목표에만 영향을 끼침을 보장합니다. 그래서 만약 ``t``가 평소처럼 현재 목표에만 영향을 미친다면 
``focus (all_goals t)``은 ``t``와 같은 효과를 갖습니다.

다시쓰기
---------

 (``rw``로 축약되는)``rewrite`` 전략과 ``simp`` 전략은 
[계산 증명](./quantifiers_and_equality.md#calculational_proofs)에서 간단히 소개했습니다. 이 섹션과 다음 섹션에서 우리는 이들에 대해 더 자세히 논의할 것입니다.

동등과 작업할 때 편리하고 효율적인 방식을 제공하면서 
``rewrite`` 전략은 목표와 가정에 치환을 적용하는 기본적인 작동원리를 제공합니다. 전략의 가장 기본적인 형태는 ``rewrite [t]``입니다. 
여기서 ``t``는 동등을 주장하는 유형의 항입니다. 예를 들어 ``t``는 맥락 속에서 가정 ``h : x = y``이 될 수 있습니다. 
그것은 ``add_comm : ∀ x y, x + y = y + x``같은 일반적인 보조 정리일 수 있고, 
여기서 재작성 전략은 ``x``와 ``y`` 적절한 인스턴스를 찾으려고 노력합니다.
아니면 이것은 구체적이거나 혹은 일반적인 방정식을 주장하는 어떤 복합적인 항이 될 수도 있습니다. 다음 예제에서 우리는 이 기본 형태를 가정을 사용하여 목표를 재작성하는 데 사용합니다.

```lean
example (f : Nat → Nat) (k : Nat) (h₁ : f 0 = 0) (h₂ : k = 0) : f k = 0 := by
  rw [h₂] -- replace k with 0
  rw [h₁] -- replace f 0 with 0
```

다음 예제에서 ``rw``의 첫 번째 사용은 목표 ``f k = 0``에서 
``k``를 ``0``으로 바꿉니다. 그런 뒤 두 번째 것은 ``f 0``을 ``0``으로 대체합니다. 이 전략은 자동적으로 ``t = t``꼴의 임의의 목표를 자동적으로 마무리합니다. 여기서 복합 표현식을 사용하는 재작성에 대한 예제가 있습니다.

```lean
example (x y : Nat) (p : Nat → Prop) (q : Prop) (h : q → x = y)
        (h' : p y) (hq : q) : p x := by
  rw [h hq]; assumption
```

여기서 ``h hq``는 방정식 ``x = y``을 만듭니다. ``h hq`` 주위의 괄호는 필요하지 않습니다만 우리는 명확성을 위해 이들을 추가했습니다.

다수의 재작성은 ``rw [t_1, ..., t_n]`` 표기로 합쳐질 수 있습니다. 
이것은 ``rw t_1; ...; rw t_n``을 간략히 한 것입니다. 이전 예제는 다음과 같이 쓸 수 있습니다.

```lean
example (f : Nat → Nat) (k : Nat) (h₁ : f 0 = 0) (h₂ : k = 0) : f k = 0 := by
  rw [h₂, h₁]
```

기본적으로 ``rw``은 표현식의 좌변과 일치시켜 좌변을 우변으로 대체함으로써 앞방향으로 방정식을 사용합니다. ``←t`` 기호는 반대 방향으로 등식 ``t``을 사용하라고 지시하는데 사용됩니다.

```lean
example (f : Nat → Nat) (a b : Nat) (h₁ : a = b) (h₂ : f a = 0) : f b = 0 := by
  rw [←h₁, h₂]
```

이 예제에서 항 ``←h₁``은 ``b``를 ``a``로 대체하도록 재작성기에게 지시합니다. 편집기에게 여러분은 뒷방향 화살표를 ``\l``로 칠 수 있습니다. 이것과 동일한 아스키 문자 ``<-``로도 쓸 수 있습니다.

때때로 항등식의 좌변은 패턴 속 한 개 이상의 부분항과 일치할 수 있습니다. 
이 때 ``rw`` 전략은 항들을 훑으면서 제일 처음 일치하는 것을 찾고 선택합니다. 만약 이게 여러분이 원한 것이 아니라면 여러분은 추가 인수로 적절한 부분항을 지정할 수 있습니다.

```lean
example (a b c : Nat) : a + b + c = a + c + b := by
  rw [Nat.add_assoc, Nat.add_comm b, ← Nat.add_assoc]

example (a b c : Nat) : a + b + c = a + c + b := by
  rw [Nat.add_assoc, Nat.add_assoc, Nat.add_comm b]

example (a b c : Nat) : a + b + c = a + c + b := by
  rw [Nat.add_assoc, Nat.add_assoc, Nat.add_comm _ b]
```

위의 첫 예제에서 첫 단계는 ``a + b + c``을 ``a + (b + c)``으로 재작성 합니다. 그런 뒤 항 ``b + c``에 교환성을 적용합니다 .
반면 인수의 명시가 없다면 전략은 ``a + (b+ c)``에서 ``(b + c) + a``으로 재작성할 겁니다. 마침내 마지막 단계는 ``a + (c + b)``에서 ``a + c + b``로 역방향으로 결합성을 적용해 재작성 합니다. 다음 두 예제는 앞의 것과 달리 양변의 괄호에 결합성을 적용해 오른쪽으로 옮긴 뒤 
``b``와 ``c``의 자리를 바꿉니다. 마지막 예제는 ``Nat.add_comm``의 
두 번째 인수를 제시하여 우변에서 재작성이 일어나야 함을 보입니다.

기본적으로 ``rewrite`` 전략은 목표에만 영향을 미칩니다. ``rw [t] at h`` 표기는 가정 ``h``에 ``t``로 재작성을 적용합니다.

```lean
example (f : Nat → Nat) (a : Nat) (h : a + 0 = 0) : f a = f 0 := by
  rw [Nat.add_zero] at h
  rw [h]
```

첫 단계 ``rw [Nat.add_zero] at h``는 가정 ``a + 0 = 0``을 ``a = 0``으로 재작성 합니다.
그 뒤 새로운 가정 ``a = 0`` 가 목표를 ``f 0 = f 0``로 재작성하는 데 사용됩니다.

``rewrite`` 전략은 명제에만 국한되지 않습니다.
다음 예제에서 우리는 가정 ``t : Tuple α n``를 ``t : Tuple α 0``으로 재작성하도록 ``rw [h] at t``를 사용합니다.

```lean
def Tuple (α : Type) (n : Nat) :=
  { as : List α // as.length = n }

example (n : Nat) (h : n = 0) (t : Tuple α n) : Tuple α 0 := by
  rw [h] at t
  exact t
```

단순화기 사용하기
--------------------

``rewrite``는 목표를 조작하기 위한 외과 수술 도구로써 고안된 반면
단순화기는 자동화의 더욱 강력한 형태를 제공합니다. 린의 라이브러리 속 여러 항등식들은 ``[simp]`` 속성으로 태그되어 있습니다.
그리고 ``simp`` 전략은 이들을 표현식에서 부분항 재작성에 반복적으로 사용합니다.

```lean
example (x y z : Nat) (p : Nat → Prop) (h : p (x * y))
        : (x + 0) * (0 + y * 1 + z * 0) = x * y := by
  simp

example (x y z : Nat) (p : Nat → Prop) (h : p (x * y))
        : p ((x + 0) * (0 + y * 1 + z * 0)) := by
  simp; assumption
```

첫 예제에서 목표를  ``x * y = x * y``으로 축약하면서 
목표 속 등식의 좌변은 0과 1을 포함한 평범한 항등식을 사용해 단순화됩니다. 여기서 ``simp``는 이 목표를 끝내는데 반사성을 적용합니다. 두 번째 예제에서 ``simp``는 목표를 ``p (x * y)``으로 축약합니다.
이 때, 가정 ``h``가 이 목표를 끝냅니다. 여기에 리스트에 대한 몇 가지 예제가 더 있습니다.

```lean
open List

example (xs : List Nat)
        : reverse (xs ++ [1, 2, 3]) = [3, 2, 1] ++ reverse xs := by
 simp

example (xs ys : List α)
        : length (reverse (xs ++ ys)) = length xs + length ys := by
 simp [Nat.add_comm]
```

``rw``처럼 키워드 ``at``으로 가정을 단순화 하는데 사용할 수 있습니다.

```lean
example (x y z : Nat) (p : Nat → Prop)
        (h : p ((x + 0) * (0 + y * 1 + z * 0))) : p (x * y) := by
  simp at h; assumption
```

게다가 여러분은 "와일드카드" *(asterisk)로 모든 가정과 목표를 간단히 하는데 사용할 수 있습니다.

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

자연수 곱셈 같은 교환성과 결합성이 있는 연산자에 대해 왼쪽 교환성과 
마찬가지로 단순화기는 표현식을 재작성 하는데 이 두 사실을 사용합니다. 곱셈의 경우 후자는 다음과 같이 표현됩니다. ``local`` 수정자는 단순화기에게 현재 파일(경우에 따라 섹션, 이름공간일 수 있음) 
속 이 규칙들을 사용하라고 말합니다. 둘 중 어떤 것의 반복적인 적용이 무한루프를 유발한다는 점에서 
교환성과 왼쪽 교환성은 문제가 있어 보입니다. 그러나 단순화기는 항등식들이 그들의 인자를 교환한다는 것을 감지하고 
*ordered rewriting*으로 알려진 기법을 사용합니다. 이는 린 시스템이 항들의 내부적인 순서를 유지하고 
순위를 감소시키는 방향으로만 항등식을 적용함을 의미합니다. 위에서 언급된 세 항등식들은 표현식 속 모든 괄호가 오른쪽으로 결합되는 
효과를 갖고 표현식들은 표준 방식(약간 임의적일지라도)으로 순서화됩니다. 그럼 결합성과 교환성에 한해 동등한 두 표현식은 동일한 정식 형태로 재작성될 것 입니다.

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

``rewrite``처럼 일반적인 보조정리, 국부적인 가정, 펼친 정의와 복합 표현식을 포함해 
``simp``가 사용할 사실들의 리스트를 보낼 수 있습니다. ``rewrite``가 그런 것처럼 ``simp`` 전략도 ``←t`` 문법을 인식할 수 있습니다.  어떤 경우든지 항을 간단히 하는데 사용되는 항등식의 모임에 추가적인 규칙이 더해질 수 있습니다.

```lean
def f (m n : Nat) : Nat :=
  m + n + m

example {m n : Nat} (h : n = 1) (h' : 0 = m) : (f m n) = n := by
  simp [h, ←h', f]
```

흔한 관용구는 국부적인 가정을 사용해 목표를 단순화하는 것입니다.


```lean
example (f : Nat → Nat) (k : Nat) (h₁ : f 0 = 0) (h₂ : k = 0) : f k = 0 := by
  simp [h₁, h₂]
```

단순화할 때 지역 맥락 속에 있는 모든 가정을 사용하기 위해서
우리는 와일드카드 기호 ``*``를 사용할 수 있습니다.

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

단순화기도 명제 재작성을 할 것입니다. 예를 들어 가정 ``p``를 사용하여 이것은 ``p ∧ q``을 ``q``로 그리고 ``p ∨
q``을 ``true``으로 재작성합니다. 그럼 이것은 자명하게 증명합니다. 이런 재작성을 반복하는 것은 비자명한 명제 논리적 추론을 만듭니다.

```lean
example (p q : Prop) (hp : p) : p ∧ q ↔ q := by
  simp [*]

example (p q : Prop) (hp : p) : p ∨ q := by
  simp [*]

example (p q r : Prop) (hp : p) (hq : q) : p ∧ (q ∨ r) := by
  simp [*]
```

다음 예제는 모든 가정을 단순화한 뒤 이들로 목표를 증명합니다.

```lean
example (u w x x' y y' z : Nat) (p : Nat → Prop)
        (h₁ : x + 0 = x') (h₂ : y + 0 = y')
        : x + y + 0 = x' + y' := by
  simp at *
  simp [*]
```

단순화기를 특히 유용하게 만드는 한 가지는 그것의 능력이 
라이브러리가 개발되어 감에 따라 증가한다는 것입니다. 예를 들어 한 리스트를 뒤집은 것을 그 리스트 뒷편에 연결하여 대칭시키는
리스트 연산을 정의해봅시다.

```lean
def mk_symm (xs : List α) :=
  xs ++ xs.reverse
```

그럼 임의의 리스트  ``xs``에 대해 ``reverse (mk_symm xs)``은 ``mk_symm xs``과 동일합니다. 
그리고 이는 정의를 열어보는 것으로 쉽게 증명할 수 있습니다.

```lean
# def mk_symm (xs : List α) :=
#  xs ++ xs.reverse
theorem reverse_mk_symm (xs : List α)
        : (mk_symm xs).reverse = mk_symm xs := by
  simp [mk_symm]
```

우리는 이 정리로 새로운 결과를 증명하는데 쓸 수 있습니다.

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

하지만 ``reverse_mk_symm``을 사용하는 것은 일반적으로 옳습니다. 그러니 
사용자가 이를 명시적으로 불러올 필요가 없다면 좋을 것입니다. 정리가 정의되었을 때 이 정리를 단순화 규칙으로 
지정하여 이를 성취할 수 있습니다.

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

 ``@[simp]`` 표기는 ``reverse_mk_symm``가 ``[simp]`` 
특성을 갖고 더 명시적으로 쓸 수 있도록 선언합니다.

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

이 특성은 정리가 선언된 이후 언제든지 적용될 수 있습니다.

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

그러나 한 번 이 특성이 적용되면 그 특성이 부여된 정리를 불러온 어떤 파일이든 
지속되므로 영구적으로 이를 제거할 방법이 없습니다. [Attributes](TBD)에서 더 논의할 것이지만 누군가는 ``local`` 수정자를 
사용해 특성의 범위를 현재 파일이나 섹션으로 제한할 수 있습니다.

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

섹션 바깥 쪽에서 단순화기는 기본적으로 ``reverse_mk_symm``를 더 이상 사용할 수 없게 됩니다.

이제까지 논의한 다양한 ``simp`` 옵션은 --규칙들의 명시적인 리스트를 주는 것과 ``at``으로
위치를 나타냄-- 합쳐질 수 있습니다. 그러나 나열된 순서는 변하지 않습니다. 이와 연관된 문서 문자열을 보려면 ``simp`` 식별자에 커서를 놓으면
편집기 속에서 옳바른 순서를 볼 수 있습니다.

유용한 수정자들이 두 개 더 있습니다. 기본적으로 ``simp``은 ``[simp]`` 특성으로 지정한 모든 정리들을 포함합니다. ``simp only``를 쓰는 것은 이런 기본 설정을 배제하여 
더 명시적으로 규칙 리스트를 만들어 쓸 수 있게 합니다. 아래 예제에서 음의 부호와 ``only``는 ``reverse_mk_symm``의 
적용을 막는데 사용됩니다.

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

다음 에제에서 우리는`triv`기호를 `syntax` 명령을 사용해 정의합니다.
그런 뒤 우리는  `triv`가 사용될 때 `macro_rules` 명령으로 
무엇을 해야 하는지 나타내는데 사용할 수 있습니다. 다른 확장을 제공할 수 있습니다. 그리고 전략 
번역기는 어느 하나가 성공할 때까지 그들 모두를 시도할 것입니다..

```lean
-- Define a new tactic notation
syntax "triv" : tactic

macro_rules
  | `(tactic| triv) => `(tactic| assumption)

example (h : p) : p := by
  triv

-- 여러분은 `triv` 사용해 다음 정리를 증명할 수 없습니다.
-- example (x : α) : x = x := by
--  triv

-- 'triv'를 추가해봅시다. 전략 번역기는
-- `triv`에 대한 가능한 모든 매크로 확장들 중 어느 하나라도 성공할 때까지 시도합니다.

macro_rules
  | `(tactic| triv) => `(tactic| rfl)

example (x : α) : x = x := by
  triv

example (x : α) (h : p) : x = x ∧ p := by
  apply And.intro <;> triv

-- 이제 우리는 (재귀적인) 확장을 추가합니다.
macro_rules | `(tactic| triv) => `(tactic| apply And.intro <;> triv)

example (x : α) (h : p) : x = x ∧ p := by
  triv
```

연습문제
---------

1. [명제와 증명](./propositions_and_proofs.md)과 [ 한정기호와 동등성](./quantifiers_and_equality.md)의 연습문제로 돌아가서 
   전략 증명으로 여러분이 할 수 있는 만큼 많이 다시 해보세요. 
   ``rw``와 ``simp``도 적절히 사용하세요.

2. 다음의 한 줄 증명을 얻도록 전략 조합자를 사용하세요.

```lean
 example (p q r : Prop) (hp : p)
         : (p ∨ q ∨ r) ∧ (q ∨ p ∨ r) ∧ (q ∨ r ∨ p) := by
   admit
```
