명제와 증명
=======================

지금까지, 여러분들은 린에서 객체와 함수를 정의하는 몇가지 방법을 배웠습니다. 이 장에서 여러분에게 의존 유형론의 언어로 수학적 주장과 증명을 작성하는 법에 대해 설명하려고 합니다.

유형으로써 명제
---------------------

의존 유형론의 언어로 정의된 대상에 대해서 주장을 증명하는 한 방법은 주장 언어와 증명 언어를 언어 정의의 꼭대기에 두는 것입니다. 그러나 이런 식으로 언어를 늘릴 이유는 없습니다. 의존유형론은 유연하며 표현력 있습니다. 그리고 주장과 증명을 동일한 일반 프레임워크 안에서 표현하지 못 할 이유도 없습니다.

예를 들어, 우리는 명제를 나타내는 새 유형 ``Prop``과 다른 유형으로부터 새로운 명제를 만드는 생성자를 도입할 수 있습니다.

```lean
# def Implies (p q : Prop) : Prop := p → q
#check And     -- Prop → Prop → Prop
#check Or      -- Prop → Prop → Prop
#check Not     -- Prop → Prop
#check Implies -- Prop → Prop → Prop

variable (p q r : Prop)
#check And p q                      -- Prop
#check Or (And p q) r               -- Prop
#check Implies (And p q) (And q p)  -- Prop
```

그뒤 각 원소 ``p : Prop``에 대해 또 다른 유형인 ``Proof p``을 ``p``의 증명 유형으로 도입할 수 있습니다.  "공리"는 그런 유형의 상수일 겁니다.

```lean
# def Implies (p q : Prop) : Prop := p → q
# structure Proof (p : Prop) : Type where
#   proof : p
#check Proof   -- Proof : Prop → Type

axiom and_comm (p q : Prop) : Proof (Implies (And p q) (And q p))

variable (p q : Prop)
#check and_comm p q     -- Proof (Implies (And p q) (And q p))
```

하지만 공리에 더해 우리는 이전 증명으로부터 새로운 증명을 만드는데 사용할 규칙도 필요합니다. 예를 들어, 명제 논리를 위한 다수의 증명보조기는 그 속에 전건긍정(modus ponens) 규칙이 있습니다.

> ``Implies p q``의 증명과 ``p``의 증명으로부터 ``q``의 증명을 얻을 수 있습니다.

이를 다음과 같이 나타낼 수 있습니다.

```lean
# def Implies (p q : Prop) : Prop := p → q
# structure Proof (p : Prop) : Type where
#   proof : p
axiom modus_ponens : (p q : Prop) → Proof (Implies p q) →  Proof p → Proof q
```

명제논리에 대한 자연 영역의 체계은 주로 다음 규칙에 의존합니다.

> 가설로 ``p``를 가정하면 ``q``의 증명을 가질 수 있다는 것입니다. 그러면 우리는 가정을 "상쇄"하여 ``Implies p q``의 증명을 얻을 수 있습니다.

이를 다음과 같이 유도할 수 있습니다.

```lean
# def Implies (p q : Prop) : Prop := p → q
# structure Proof (p : Prop) : Type where
#   proof : p
axiom implies_intro : (p q : Prop) → (Proof p → Proof q) → Proof (Implies p q)
```

이런 접근법은 주장과 증명을 세우는 합리적인 방법을 줍니다.
표현식 ``t``가 주장 ``p``의 올바른 증명임을 결정하는 것은 ``t``가 ``Proof p``형임을 확인하는 문제가 됩니다.

하지만 몇 가지 단순화를 할 수 있습니다. 그러려면 ``p``를 ``Proof p``로 부풀림으로써 항 ``Proof``를 반복해 쓰는 것을 피할 수 있습니다. 다시 말하자면, ``p : Prop``를 갖는 한 우리는``p``를 그것의 증명 유형으로 해석할 수 있습니다. 그러면 ``t : p``를 ``t``는 ``p``의 증명이다라는 주장으로 읽을 수 있습니다.

더욱이 한 번 우리가 이런 식별을 하면 함의 규칙은 ``Implies p q``과 ``p → q``의 앞뒤를 오갈 수 있음을 보여줍니다. 다시 말하면, 명제 ``p``과 ``q``사이의 함의는 어떤 ``p``의 원소를 받아 어떤 ``q``의 원소로 가는 함수를 갖는 것에 대응됩니다. 따라서 결합자 ``Implies``의 도입은 완전히 중복됩니다. 그래서 ``p → q``을 의존유형론에서 함의 개념으로 평소의 함수공간 생성자를 사용할 수 있습니다.

이는 린에서와 마찬가지로 구성주의적 계산법에 따른 접근법입니다. 자연 연역에 대한 증명 보조기에서 함의 규칙이 함수 추상화와 함수 적용을 지배하는 규칙과 정확히 일치한다는 사실은 *커리-하워드 동형론(Curry-Howard isomorphism) *의 한 예이며, 때때로 *유형으로써 명제(propositions-as-types)* 패러다임으로 알려져 있습니다. 사실 ``Prop``형은 지난 장에서 설명한 유형 계층의 최하층인 ``Sort 0``에 대한 문법 설탕입니다. 게다가 ``Type u``도 ``Sort (u+1)``에 대한 문법 설탕입니다. ``Prop``은 특별한 기능이 있습니다. 하지만 다른 유형 세계처럼, 화살표 생성자에 닫혀있습니다. 우리가 ``p q : Prop``갖는다면  ``p → q : Prop``입니다.

유형으로써 명제에 대해 적어도 두 가지 사고 방식이 있습니다. 논리학과 수학에 구성주의적 관점을 갖는 누군가에게 이것은 명제라는 것의 의미를 충실하게 구현한 것입니다. 명제 ``p``은 증명을 생성하는 일종의 데이터를 나타냅니다. 그러면 ``p``의 증명은 단순히 대상 ``t : p``의 오른쪽 유형입니다.

이 이데올로기에 편향되지 않은 사람들은 꽤나 단순한 코딩 트릭으로 볼 것입니다. 각 명제 ``p``에 대해, 우리는 ``p``이 거짓이면 빈 유형, ``p``가 참이면 한 원소(말하자면: ``*``)를 갖는 유형과 연관시킵니다. 후자의 경우 (연관된 유형)``p``은 *머무른다(inhabited)*고 말합시다. 함수 적용 및 추상화 규칙은 ``Prop``의 원소가 머무르는지를 추적하는 걸 돕는데 편리하게 해 줄 수 있습니다. 그러므로 원소 ``t : p``을 생성하는 것은 ``p``가 당연히 사실임을 알립니다. ``p``의 머무름은 "``p``가 참이라는 사실"로 생각할 수 있습니다. ``p → q``의 증명은 "``p``가 참이라는 사실"로  "``q``가 참이라는 사실"을 얻는데 사용합니다.

물론 ``p : Prop``가 어떤 명제라면, 린의 커널은 임의의 두 원소 ``t1 t2 : p ``을 ``(fun x = t) s``와 ``t[/x]``를 다루는 것과 마찬가지로 정의상으로 동등하다 취급합니다. 이것은 *증명 무연관(proof irrelevance)*으로 알려져 있고 이것은 마지막 문단에서 해석과 일치합니다. 이는 증명``t : p``을 의존 유형론 언어에 대해 평범한 대상으로 다룰 수 있음에도 ``p``가 참이라는 사실 외의 정보를 주지 않음을 의미합니다.

앞서 제안한 유형으로써 명제 패러다임에 대한 두 사고 방식은 근본적인 면에서 다릅니다. 구성주의적 관점에서 증명은 의존 유형론의 적절한 표현식으로 *표기된*추상적인 수학적 대상입니다. 대조적으로 위에서 설명한 코딩 트릭으로 생각한다면 표현식 그 자체는 어떤 흥미로운 것도 나타내지 않습니다. 그보다 우리가 표현식을 쓸 수 있고 의문의 명제가 참이라고 보장하는 잘 입력됨을 검증할 수 있다는 것은 사실입니다. 다시 말하면 표현식 *그 자체는* 증명입니다.

아래의 설명에서 우리는 이 두 말하기 방식 사이를 왔다갔다 할 것인데, 어떤 때에는 명제의 증명을 "구성" 또는 "생성", "반환"으로 표현해 말하고 또 다른 때에는 단순히 그런 증명이 "있다"고 말합니다. 이것은 컴퓨터 과학자들이 프로그램이 특정 함수를 "계산"한다고 말함으로써 문법과 의미론 사이의 구분을 때때로 모호하게 하는 방식과 유사합니다. 그리고 또 다른 때에는 프로그램이 문제의 함수인 것처럼 말합니다.

어떤 경우든 가장 중요한 것은 아래의 문장입니다. 의존 유형론의 언어로 수학적 주장을 형식적으로 표현하기 위해 항 ``p : Prop``을 보일 필요가 있습니다. 주장을 *증명*하기 위해 항 ``t : p``을 보일 필요가 있습니다. 증명 보조기로써 린의 일은 그런 항 ``t``를 생성하는 것을 돕는 것과 그것이 올바른 유형을 갖고 잘 형성된 것을 검증하는 것입니다.

유형으로써 명제로 작업하기
----------------------------------

유형으로써 명제 패러다임에서 ``→``만을 포함하는 정리는 람다 추상화와 적용으로 증명될 수 있습니다. 린에서 ``theorem`` 명령은 새로운 정리를 도입합니다.

```lean
variable {p : Prop}
variable {q : Prop}

theorem t1 : p → q → p := fun hp : p => fun hq : q => hp
```

이는 지난 장에서의 상수함수의 정의와 완전히 동일하게 보입니다. 유일한 차이는 인수가 ``Type``보다 ``Prop``의 원소라는 점입니다. 직관적으로  ``p → q → p``의 증명은 ``p``와 ``q``가 참이라고 가정합니다. 그리고 (뻔하게도) 첫 가정을 ``p``가 참이라는 결론을 입증하는데 사용합니다.

``theorem`` 명령은 ``def`` 명령의 변종임을 보세요. 명제와 유형 대응 하에서 정리 ``p → q → p``를 증명하는 것은 연관된 유형의 원소를 정의하는 것과 동일합니다. 커널의 유형 확인기에서 둘 사이의 차이는 없습니다.

하지만 정의와 정리 사이에 약간의 실용적 차이는 있습니다. 평범한 상황에서 증명 무연관에 의해 정리의 "정의"를 펼칠 필요는 절대 없습니다. 그리고 그 정리의 임의의 두 증명도 정의상으로 동등합니다. 한 번 정리의 증명이 끝나면 보통 우리는 증명이 존재한다는 것만 알면 됩니다. 증명이 무엇인지 아는 것은 중요하지 않습니다. 그 사실로부터 린은 증명에 *축약할 수 없는(irreducible)* 태그를 붙여 파서(parser)(더 정확히는  *협력기(elaborator)*)가 파일을 처리할 때 대게 증명을 펼칠 필요가 없다는 힌트를 줍니다. 사실, 어떤 증명의 옳음에 접근하는 것은 다른 증명의 세부사항 알기를 요구하지 않기에 린은 일반적으로 증명의 검증과 처리를 동시에 할 수 있습니다.

정의와 마찬가지로 ``#print``명령은 정리의 증명을 여러분에게 보여줄 것 입니다.

```lean
# variable {p : Prop}
# variable {q : Prop}
theorem t1 : p → q → p := fun hp : p => fun hq : q => hp

#print t1
```

람다 추상화 ``hp : p``과 ``hq : q``는 ``t1``의 증명에서 일시적인 가정이라고 볼 수 있습니다.  여러분은 마지막 항 ``hp``을 ``show`` 문장으로 유형을 명시적으로 나타낼 수 있습니다.

```lean
# variable {p : Prop}
# variable {q : Prop}
theorem t1 : p → q → p :=
  fun hp : p =>
  fun hq : q =>
  show p from hp
```

이런 추가 정보를 더하는 것은 증명의 명확성을 높이고 증명을 작성할 때 오류를 발견하도록 돕습니다. ``show`` 명령은 유형에 주석을 달아줄 뿐 내부적으로 우리가 본 ``t1``의 모든 나타남이 같은 항을 만듭니다.

평범한 정의처럼 우리는 람다 추상화된 변수를 콜론(:)의 왼쪽으로 옮길 수 있습니다.

```lean
# variable {p : Prop}
# variable {q : Prop}
theorem t1 (hp : p) (hq : q) : p := hp

#print t1    -- p → q → p
```

이제 우리는 정리 ``t1``을 함수 활용을 하는 것처럼 사용할 수 있습니다.

```lean
# variable {p : Prop}
# variable {q : Prop}
theorem t1 (hp : p) (hq : q) : p := hp

axiom hp : p

theorem t2 : q → p := t1 hp
```

여기서 ``axiom`` 선언은 주어진 유형의 원소의 존재성을 가정하고 논리적 일관성과 타협합니다. 예를 들어 우리는 이것을 빈 유형 `False`가 원소를 갖는다고 가정하는데 사용할 수 있습니다.

```lean
axiom unsound : False
-- Everything follows from false
theorem ex : 1 = 0 :=
False.elim unsound
```

"공리" ``hp : p``를 선언하는 것은 ``hp``에 의해 목격된 것처럼 ``p``가 참이라고 선언하는 것과 동등합니다. 정리``t1 : p → q → p``에 사실 ``hp : p``을 적용하는 것은 ``p``가 참임은 정리``t1 hp : q → p``을 얻게 합니다.

우리는 정리 ``t1``을 다음과 같이 쓸 수 있음을 기억하세요.

```lean
theorem t1 {p q : Prop} (hp : p) (hq : q) : p := hp

#print t1
```

``t1``의 유형은 이제 ``∀ {p q : Prop}, p → q → p``입니다. 우리는 이를 "모든 명제쌍  ``p q``에 대해 ``p → q → p``이다."라고 주장한다고 읽을 수 있습니다. 예를 들어, 우리는 모든 매개변수들을 콜론의 오른쪽으로 옮길 수 있습니다.

```lean

theorem t1 : ∀ {p q : Prop}, p → q → p :=
  fun {p q : Prop} (hp : p) (hq : q) => hp
```

``p``와 ``q``가 변수로 선언되었다면 린은 이를 자동적으로 일반화시킬 것입니다.

```lean
variable {p q : Prop}

theorem t1 : p → q → p := fun (hp : p) (hq : q) => hp
```

사실 유형으로써 명제 대응에 의해 우리는 ``p``가 성립하는 가정 ``hp``를 또 다른 변수로 선언할 수 있습니다.

```lean
variable {p q : Prop}
variable (hp : p)

theorem t1 : q → p := fun (hq : q) => hp
```

린은 ``hp``를 사용하는 증명을 감지하고 자동적으로 ``hp : p``를 전제로 추가합니다. 모든 경우에 명령 ``#print t1``은 여전히 ``∀ p q : Prop, p → q → p``을 얻습니다. 왜냐하면 화살표는 대상이 구속 변수에 의존하지 않는 화살표 유형만을 나타내기에 이 유형은 ``∀ (p q : Prop) (hp : p) (hq :q), p``로 쓸 수 있습니다.

우리가 ``t1``을 이런 식으로 일반화한다면 우리는 일반적인 정리의 다른 사례를 얻기 위해 다른 명제 쌍을 이에 적용할 수 있습니다.

```lean
theorem t1 (p q : Prop) (hp : p) (hq : q) : p := hp

variable (p q r s : Prop)

#check t1 p q                -- p → q → p
#check t1 r s                -- r → s → r
#check t1 (r → s) (s → r)    -- (r → s) → (s → r) → r → s

variable (h : r → s)
#check t1 (r → s) (s → r) h  -- (s → r) → r → s
```

다시 한 번, 유형으로써 명제 대응을 사용해 ``r → s``형의 변수 ``h``는 ``r → s``을 성립시키는 가정 또는 전제라고 볼 수 있습니다.

또 다른 예로써 지금은 유형 대신 명제로 지난 장에서 논한 합성함수를 고려해봅시다.

```lean
variable (p q r s : Prop)

theorem t2 (h₁ : q → r) (h₂ : p → q) : p → r :=
  fun h₃ : p =>
  show r from h₁ (h₂ h₃)
```
명제 논리의 정리로써 ``t2``가 말하는 것은 무엇인가요?

수치 유니코드 밑첨자를 사용하는 것은 종종 유용합니다. 이 예제에서 그런 것처럼 가정에 대해 ``\0``, ``\1``, ``\2``, ..., 을 쳐서 입력할 수 있습니다.

명제 논리
-------------------

린은 모든 표준 논리 연결사와 표기를 정의합니다. 명제 연결사는 다음 기호와 딸려 나온다.

| 아스키(Ascii) | 유니코드(Unicode) | 편집 단축기(Editor shortcut) | 정의(Definition) |
|-------------------|-----------|------------------------------|--------------|
| True |           |                              | True |
| False |           |                              | False |
| Not | ¬ | ``\not``, ``\neg`` | Not |
| /\\ | ∧ | ``\and`` | 논리곱 |
| \\/ | ∨ | ``\or`` | 논리합 |
| -> | → | ``\to``, ``\r``, ``\imp`` |              |
| <-> | ↔ | ``\iff``, ``\lr`` | Iff |

이들은 ``Prop``형의 모든 값을 받습니다.

```lean
variable (p q : Prop)

#check p → q → p ∧ q
#check ¬p → p ↔ False
#check p ∨ q → q ∨ p
```

연산자의 우선순위는 다음과 같습니다. 일항 부정 ``¬`` 은 가장 강하게 결합하고 그 다음은 ``∧`` 그 다음 ``∨`` 그 다음 ``→`` 그리고 마지막으로 ``↔``입니다. 예를 들어 ``a ∧ b → c ∨ d ∧ e``은 ``(a ∧ b) → (c ∨ (d ∧ e))``을 의미합니다. 다른 이항 결합자들처럼 ``→``은 오른쪽으로 결합한다는 것을 기억하세요.(인수가 ``Type`` 대신 ``Prop``인 것을 제외하고 변한 건 없습니다.) 그래서 만약 ``p q r : Prop``이 있다면 표현식 ``p → q → r``은 "``p``이면 그러면``q``이면``r``이다."로 읽습니다. 이는 ``p ∧ q → r``의 "커리된(curried)" 형태일 뿐입니다.

지난 장에서 람다 추상화가 ``→``에 대한 "도입 규칙"이라고 봤습니다. 현재 상황에서 이는 함의를 어떻게 "도입"하거나 세우는지 보여줍니다. 적용은 어떻게 "제거"하는지 혹은 증명에서 함의를 어떻게사용하는지를 보여주는 "제거 규칙"으로 봅니다. 다른 명제 논리적 연결사들은 린의 라이브러리 속 ``Prelude.core`` 파일에 정의되어 있습니다. (라이브러리 계층에 대한 더 많은 정보는 [파일 불러오기](./interacting_with_lean.md#importing_files)를 참고) 그리고 각 연결사들에 대해 그것의 정식 도입 및 제거 규칙이 딸려 나옵니다.

### 논리곱

표현식 ``And.intro h1 h2``은 ``p ∧ q``의 증명을 ``h1 : p``과 ``h2 : q``의 증명을 사용하여 세웁니다. ``And.intro``를 *and-도입* 규칙이라고 설명하는 것은 흔합니다. 다음 예제에서 우리는 ``And.intro``를 ``p → q → p ∧ q``의 증명을 만들기 위해 사용합니다.

```lean
variable (p q : Prop)

example (hp : p) (hq : q) : p ∧ q := And.intro hp hq

#check fun (hp : p) (hq : q) => And.intro hp hq
```

``example`` 명령은 이름이 없거나 영구적인 맥락 속에 그것을 저장한 정리를 기술합니다. 기본적으로 이는 어떤 항이 지정된 유형을 가짐을 확인할 뿐입니다. 이는 설명에 편리하므로 이를 자주 사용할 것입니다.

표현식 ``And.left h``는 증명 ``h : p ∧ q``으로부터 ``p``의 증명을 생성합니다. 마찬가지로 ``And.right h``는 ``q``의 증명입니다. 이들은 흔히 오른쪽과 왼쪽 *and-제거* 규칙으로 알려져 있습니다.

```lean
variable (p q : Prop)

example (h : p ∧ q) : p := And.left h
example (h : p ∧ q) : q := And.right h
```

이제 ``p ∧ q → q ∧ p``를 다음 증명 항으로 증명할 수 있습니다.

```lean
variable (p q : Prop)

example (h : p ∧ q) : q ∧ p :=
And.intro (And.right h) (And.left h)
```

and-도입과 and-제거는 카테시안 곱 연산에 대해 순서쌍을 구성하는 것과 순서쌍에서 원소를 추출하는 연산과 유사합니다. 차이는 ``hp : p``와 ``hq : q``가 주어졌을 때 ``And.intro hp hq``는 ``p ∧ q : Prop``형을 갖는 한편 ``Prod hp hq``는 ``p × q : Type``형을 갖는다는 것입니다. ``∧``과 ``×`` 사이의 유사성은 커리-하워드 동형론의 또 다른 예입니다. 그러나 함의와 함수 공간 생성자와는 대조적으로  ``∧``과 ``×``은 린에서 별개로 다뤄집니다. 그래도 우리가 방금 구성한 증명은 순서쌍의 원소를 바꾸는 함수와 유사합니다.

[구조체와 레코드 장](./structures_and_records.md)에서 보겠지만 린의 어떤 유형은 *구조체*입니다. 구조체는 그 유형이 적절한 인수의 배열로부터 유형의 원소를 만드는 정식 *생성자* 한 개로 정의된다는 것입니다. 모든 ``p q : Prop``에 대해 ``p ∧ q``는 예제입니다. 원소를 생성하는 정식 방법은 ``And.intro``를 적절한 인수 ``hp : p``과 ``hq : q``에 대해 적용하는 것입니다. 연관된 유형이 귀납형이고 맥락으로부터 추론할 수 있는 상황에서 린은 *익명 생성자* 표기 ``⟨arg1, arg2, ...⟩``를 쓸 수 있게 해줍니다. 특히 ``And.intro hp hq``대신  ``⟨hp, hq⟩``와 같이 쓸 수 있습니다.

```lean
variable (p q : Prop)
variable (hp : p) (hq : q)

#check (⟨hp, hq⟩ : p ∧ q)
```

이 꺽긴 괄호는 각각 ``\<``과 ``\>``으로 입력해 쓸 수 있습니다.

린은 또 다른 유용한 문법 도구를 제공합니다. (아마 몇 인수에 적용한) 귀납형 ``Foo``의 표현식 ``e``에 대해 ``e.bar``과 같은 표기는 ``Foo.bar e``의 약식 표현입니다.
이는 이름공간을 열지 않고 함수에 접근하는 편리한 방법을 줍니다.  예를 들어 다음 두 표현식은 같은 것을 의미합니다.

```lean
variable (xs : List Nat)

#check List.length xs
#check xs.length
```

따라서 ``h : p ∧ q``일 때 ``And.left h``를 ``h.left``로 그리고 ``And.right h``를 ``h.right`` 로 쓸 수 있습니다. 그러므로 다음과 같이 위의 증명 예시를 편리하게 다시 작성할 수 있습니다.

```lean
variable (p q : Prop)
example (h : p ∧ q) : q ∧ p :=
  ⟨h.right, h.left⟩
```

간결함과 난독화 사이에 미세한 선이 있고 이런 식으로 정보를 생략하는 것은 종종 증명을 읽기 더 어렵게 만듭니다. 위처럼 직관적인 구성의 경우 ``h``의 유형과 구성의 목표가 두드러질 때 이 표기법은 깨끗하고 효과적입니다.

"And"같은 반복적 구성은 흔합니다. 두 증명이 동등함을 보이기 위해 린은 여러분이 오른쪽으로 결합한 중첩된 생성자로 꺽인 괄호 하나만 사용하는 것(flatten)을 허용합니다.

```lean
variable (p q : Prop)

example (h : p ∧ q) : q ∧ p ∧ q:=
  ⟨h.right, ⟨h.left, h.right⟩⟩

example (h : p ∧ q) : q ∧ p ∧ q:=
  ⟨h.right, h.left, h.right⟩
```

이 또한 종종 유용합니다.

### 논리합

표현식 ``Or.intro_left q hp``은 ``hp : p``의 증명으로부터 ``p ∨ q``의 증명을 만듭니다.
 비슷하게 ``Or.intro_right p hq``는 ``hq : q``의 증명을 사용해 ``p ∨ q`` 의 증명을 만듭니다. 이들은 왼쪽과 오른쪽 *or-도입* 규칙입니다.

```lean
variable (p q : Prop)
example (hp : p) : p ∨ q := Or.intro_left q hp
example (hq : q) : p ∨ q := Or.intro_right p hq
```

*or-제거* 규칙은 약간 더 복잡합니다. 아이디어는 ``r``이 ``p``로부터 그리고 ``r``이 ``q``로부터 도출됨을 보임으로써 우리가 ``p ∨ q``로부터 ``r``을 증명할 수 있다입니다.  다시 말하자면 경우에 따라 증명한 것입니다. 표현식 ``Or.elim hpq hpr hqr``에서 ``Or.elim``은 세 인수 ``hpq : p ∨ q``와 ``hpr : p → r``, ``hqr : q → r``를 받습니다. 그리고 ``r``의 증명을 만듭니다. 다음 예제에서 ``Or.elim``로 ``p ∨ q → q ∨ p``을 증명합니다.

```lean
variable (p q r : Prop)

example (h : p ∨ q) : q ∨ p :=
  Or.elim h
    (fun hp : p =>
      show q ∨ p from Or.intro_right q hp)
    (fun hq : q =>
     show q ∨ p from Or.intro_left p hq)
```

대부분의 경우 ``Or.intro_right``와 ``Or.intro_left``의 첫 번 째 인수는 린에 의해 자동으로 추론됩니다. 그러므로 린은 ``Or.intro_right _``과 ``Or.intro_left _``의 약식 표현인 ``Or.inr`` 과 ``Or.inl``을 제공합니다. 따라서 위의 증명 항을 더 간결하게 작성할 수 있습니다.

```lean
variable (p q r : Prop)

example (h : p ∨ q) : q ∨ p :=
  Or.elim h (fun hp => Or.inr hp) (fun hq => Or.inl hq)
```

린이 ``hp``와 ``hq``의 유형을 추론하는데 전체 표현식 속에 충분한 정보가 있습니다.  그러나 더 긴 버전의 유형 주석을 사용하면 증명을 더 가독성있게 하고 오류를 잡고 고치는 걸 도와줄 수 있습니다.

``Or``은 두 개의 생성자가 있기 때문에 익명 생성자 표기를 사용할 수 없습니다. 그래도 ``Or.elim h``대신 ``h.elim``와 같이 쓸 수 있습니다.

```lean
variable (p q r : Prop)

example (h : p ∨ q) : q ∨ p :=
  h.elim (fun hp => Or.inr hp) (fun hq => Or.inl hq)
```

한 번 더, 여러분은 그러한 간략화가 가독성을 높이는지 낮추는지 판단을 시험해봐야 합니다.

### 부정과 거짓

부정 ``¬p``은 사실 ``p → False``로 정의 되었습니다. 그래서 ``p``로부터 모순을 유도하여 ``¬p``를 얻습니다. 마찬가지로 표현식 ``hnp hp``은 ``hp : p``과 ``hnp : ¬p``으로부터 ``False``의 증명을 만듭니다. 다음 예제는 ``(p → q) → ¬q → ¬p``의 증명을 만드는 데 두 규칙 모두를 사용합니다. (기호 ``¬``은 ``\not``이나  ``\neg``을 치는 것으로 만들어집니다.)

```lean
variable (p q : Prop)

example (hpq : p → q) (hnq : ¬q) : ¬p :=
  fun hp : p =>
  show False from hnq (hpq hp)
```

연결사 ``False``은 하나의 제거 규칙 ``False.elim``을 갖습니다. 이것은 모순으로부터 어떤 것이든 도출된다는 사실을 표현합니다. 이 규칙은 때때로 *ex falso* (라틴어 *ex falso sequitur quodlibet*을 줄인 것), 또는 *폭발 원리(principle of explosion)*라고 합니다.

```lean
variable (tp q : Prop)

example (hp : p) (hnp : ¬p) : q := False.elim (hnp hp)
```

어떤 사실 ``q``가 어떤 거짓 명제로부터 도출됨은 ``False.elim``의 암시적 인수이며 자동적으로 추론됩니다. 모순적인 가정들로부터 어떤 사실을 유도하는 이런 패턴은 꽤 흔하고 ``absurd``로 표현됩니다.

```lean
variable (p q : Prop)

example (hp : p) (hnp : ¬p) : q := absurd hp hnp
```

여기 ``¬p → q → (q → p) → r``의 증명에 대한 예제가 있습니다.

```lean
variable (p q r : Prop)

example (hnp : ¬p) (hq : q) (hqp : q → p) : r :=
  absurd (hqp hq) hnp
```

참고로 ``False``은 제거 규칙만 있듯이 ``True``는 도입 규칙 ``True.intro : true``만 있습니다.  다시 말하자면 ``True``는 단순히 참이고, 정식 증명 ``True.intro``를 가집니다.

### 논리적 동등

표현식 ``Iff.intro h1 h2``은 ``h1 : p → q``과 ``h2 : q → p``으로부터  ``p ↔ q``의 증명을 생성합니다.  표현식 ``Iff.mp h``는 ``h : p ↔ q``으로부터 ``p → q``의 증명을 생성합니다. 마찬가지로 ``Iff.mpr h``는 ``h : p ↔ q``으로부터 ``q → p``의 증명을 생성합니다. 여기 ``p ∧ q ↔ q ∧ p``의 증명이 있습니다.

```lean
variable (p q : Prop)

theorem and_swap : p ∧ q ↔ q ∧ p :=
  Iff.intro
    (fun h : p ∧ q =>
     show q ∧ p from And.intro (And.right h) (And.left h))
    (fun h : q ∧ p =>
     show p ∧ q from And.intro (And.right h) (And.left h))

#check and_swap p q    -- p ∧ q ↔ q ∧ p

variable (h : p ∧ q)
example : q ∧ p := Iff.mp (and_swap p q) h
```

우리는 앞과 뒷방향 증명으로부터 ``p ↔ q``의 증명을 구성하는 익명 생성자 표기를 사용할 수 있습니다. 그리고 우리는 ``.``와 함께 쓴 ``mp``과 ``mpr``을 사용한 표기를 쓸 수 있습니다. 그러므로 이전 예제는 다음과 같이 간결하게 쓸 수 있습니다.

```lean
variable (p q : Prop)

theorem and_swap : p ∧ q ↔ q ∧ p :=
  ⟨ fun h => ⟨h.right, h.left⟩, fun h => ⟨h.right, h.left⟩ ⟩

example (h : p ∧ q) : q ∧ p := (and_swap p q).mp h
```

보조적인 하위 목표 도입하기
--------

여기는 린이 긴 증명을 구조화하도록 돕는 또 다른 장치를 도입하기에 적절한 곳 입니다. 주로  ``have`` 구성은 증명의 보조적인 세부목표를 도입합니다. 여기 이전 장에서 가져온 작은 예제가 있습니다.

```lean
variable (p q : Prop)

example (h : p ∧ q) : q ∧ p :=
  have hp : p := h.left
  have hq : q := h.right
  show q ∧ p from And.intro hq hp
```

내부적으로 표현식 ``have h : p := s; t``은 항 ``(fun (h : p) => t) s``을 만듭니다. 다시 말하자면 ``s``는 ``p``의 증명입니다. ``t``는 ``h : p``를 가정했을 때 원하는 결론의 증명입니다. 그리고 이 둘은 람다 추상화와 적용으로 결합되어 있습니다. 이 단순한 장치는 긴 증명을 구조화 할 때 엄청나게 유용합니다. 왜냐하면 우리는 간간히 ``have``를 최종 목표로 이끄는 주춧돌로써 쓰기 때문입니다.

게다가 린은 목표로부터 구조화된 후방향 추론 방식을 지원합니다. 이것은 일상 수학 속 "~을 보이기에 충분하다" 구성을 본딴 것입니다. 다음 예제는 이전 증명에서 마지막 두 줄의 순서만 바꾼 것입니다.

```lean
variable (p q : Prop)

example (h : p ∧ q) : q ∧ p :=
  have hp : p := h.left
  suffices hq : q from And.intro hq hp
  show q from And.right h
```

``suffices hq : q``을 쓰는 것은 두 목표를 남깁니다. 우선, 추가적인 가정 ``hq : q``으로 원래 목표``q ∧ p``를 증명함으로써 ``q``임을 보이기에 충분함을 증명해야 합니다. 마지막으로 ``q``임을 보여야 합니다.

고전 논리
---------------

지금까지 본 도입 규칙과 제거 규칙은 모두 구성주의적입니다. 그 말은 즉, 그들은 유형으로써 명제 대응에 기반한 논리적 연결사의 계산적인 이해를 반영한다는 것입니다. 평범한 고전 논리는 여기에 배중률 ``p ∨ ¬p``을 추가합니다. 이 원리를 사용하기 위해서 여러분은 classical 이름공간을 열어야 합니다.

```lean
open Classical

variable (p : Prop)
#check em p
```

직관적으로 구성주의적 "논리합"은 아주 강력합니다. ``p ∨ q``라 주장하는 것은 각 경우를 아는 것과 같습니다. 만약 ``RH``가 리만 가설을 나타낸다면 우리가 아직 어느 논리합도 주장하지 않았더라도 고전 수학자는 ``RH ∨ ¬RH``라고 기꺼이 주장할 겁니다.

배중률의 한 결과는 이중 부정 제거의 원리입니다.

```lean
open Classical

theorem dne {p : Prop} (h : ¬¬p) : p :=
  Or.elim (em p)
    (fun hp : p => hp)
    (fun hnp : ¬p => absurd hnp h)
```

이중 부정 제거는 ``¬¬p``를 증명하는 것과 같기 때문에 여러분이  ``¬p``를 가정하고 ``false``의 유도함으로써 어떤 명제  ``p``의 증명할 수 있게 해줍니다. 다시 말하자면 이중 부정 제거는 직관주의적 논리에서 일반적으로 불가능한 귀류법을 사용한 증명을 허용합니다. 연습으로 여러분은 그 역을 증명해보세요. 즉, ``em``이 ``dne``로부터 증명될 수 있음을 보이세요.

고전적 공리는 추가로 여러분에게 ``em``에 호소하여 정당화할 수 있는 추가적인 증명 패턴 접근권한을 줍니다.  예를 들어 누군가는 경우를 나눠 증명을 수행할 수 있습니다.

```lean
open Classical
variable (p : Prop)

example (h : ¬¬p) : p :=
  byCases
    (fun h1 : p => h1)
    (fun h1 : ¬p => absurd h1 h)
```

한편 여러분은 귀류법으로 증명을 수행할 수 있습니다.

```lean
open Classical
variable (p : Prop)

example (h : ¬¬p) : p :=
  byContradiction
    (fun h1 : ¬p =>
     show False from h h1)
```

여러분이 구성주의적 사고방식에 익숙하지 않다면 고전적 추론이 사용되어야 하는 곳이 어디인지를 아는데 시간이 걸릴지도 모릅니다.  다음 예제에서 이게 필요한데 왜냐하면 구성주의적 관점에서 ``p``와 ``q`` 둘 다 참이 아니라는 것을 아는 것이 반드시 이들 중 하나가 거짓임을 말하지 않기 때문입니다.

```lean
open Classical
variable (p q : Prop)

-- BEGIN
example (h : ¬(p ∧ q)) : ¬p ∨ ¬q :=
  Or.elim (em p)
    (fun hp : p =>
      Or.inr
        (show ¬q from
          fun hq : q =>
          h ⟨hp, hq⟩))
    (fun hp : ¬p =>
      Or.inl hp)
```

우리는 나중에 *배중률과 이중 부정 제거와 같은 원칙이 허용되는 구성주의적 논리 * 상황이 있음을 나중에 보게 될 것입니다. 그리고 린은 그런 맥락에서 배중률에 의존하지 않는 고전적 추론의 사용을 지원합니다.

고전적 추론을 지원하는 린에서 사용된 모든 공리의 리스트는 [공리와 계산](./axioms_and_computations.md)에서 다뤄집니다.

명제적 유효성 예제
------------------------------------

린의 표준 라이브러리는 명제 논리의 유효한 많은 진술들의 증명을 포함합니다. 그 모든 것들은 여러분들의 주장을 증명하는데 자유롭게 사용할 수 있습니다. 다음 리스트는 흔한 동치명제와 항진명제들을 포함합니다.

교환성:

1. ``p ∧ q ↔ q ∧ p``
2. ``p ∨ q ↔ q ∨ p``

결합성:

3. ``(p ∧ q) ∧ r ↔ p ∧ (q ∧ r)``
4. ``(p ∨ q) ∨ r ↔ p ∨ (q ∨ r)``

분배성:

5. ``p ∧ (q ∨ r) ↔ (p ∧ q) ∨ (p ∧ r)``
6. ``p ∨ (q ∧ r) ↔ (p ∨ q) ∧ (p ∨ r)``

기타 성질들:

7. ``(p → (q → r)) ↔ (p ∧ q → r)``
8. ``((p ∨ q) → r) ↔ (p → r) ∧ (q → r)``
9. ``¬(p ∨ q) ↔ ¬p ∧ ¬q``
10. ``¬p ∨ ¬q → ¬(p ∧ q)``
11. ``¬(p ∧ ¬p)``
12. ``p ∧ ¬q → ¬(p → q)``
13. ``¬p → (p → q)``
14. ``(¬p ∨ q) → (p → q)``
15. ``p ∨ False ↔ p``
16. ``p ∧ False ↔ False``
17. ``¬(p ↔ ¬p)``
18. ``(p → q) → (¬q → ¬p)``

이것은 고전적 추론이 필요합니다.

19. ``(p → r ∨ s) → ((p → r) ∨ (p → s))``
20. ``¬(p ∧ q) → ¬p ∨ ¬q``
21. ``¬(p → q) → p ∧ ¬q``
22. ``(p → q) → (¬p ∨ q)``
23. ``(¬q → ¬p) → (p → q)``
24. ``p ∨ ¬p``
25. ``(((p → q) → p) → p)``

``sorry`` 식별자는 어떤 증명이든 마법같이 만듭니다. 혹은 임의 데이터 유형의 대상를 제공합니다. 물론 증명 방법으로 불건전합니다. -- 예를 들어, 여러분은 ``False``을 증명하는데 그것을 사용할 수 있습니다. --그러면 린은 그것에 의존하는 정리를 불러오거나 그런 파일을 사용할 때 심각한 경고를 보냅니다. 하지만 이것은 긴 증명을 점진적으로 만들어 나갈 때 유용합니다. 하향식 증명 작성을 시작하려면 보조 증명에 ``sorry``를 채워 사용하세요. 린이 모든 ``sorry``로 채워진 항을 받아들이게 하세요. 그렇지 않으면 여러분이 고쳐야 하는 에러가 생깁니다. 그런 뒤 다시 돌아가 각각의 ``sorry``가 더 남지 않을 때까지 이를 실제 증명으로 바꾸세요.

여기 또 유용한 기법이 있습니다. ``sorry``를 사용하는 것 대신 밑줄 문자  ``_``를 자리 차지자로 사용할 수 있습니다. 이것이 린에게 인수가 암시적임을 알리고 이를 자동적으로 채우게 함을 의미합니다. 만약 린이 그렇게 하려고 했는데 실패한다면 다음에 오는 항의 유형을 기대했다면서 "어떻게 자리 차지자를 합성해야할 지 모르겠다"는 오류 메시지를 반환합니다. 그리고 모든 대상와 가정들은 맥락에서 이용가능합니다. 다시 말하자면 각 해결되지 않은 자리 차지자에 대해 린은 그 지점에서 채워져야 할 하위 목표를 보고합니다. 그럼 여러분은 이 자리 차지자들을 점차 재우는 것으로 증명을 구성할 수 있습니다.

참고로 위의 리스트에서 가져온 유효성의 증명 예시가 두 개 있습니다.

```lean
open Classical

-- 분배성
example (p q r : Prop) : p ∧ (q ∨ r) ↔ (p ∧ q) ∨ (p ∧ r) :=
  Iff.intro
    (fun h : p ∧ (q ∨ r) =>
      have hp : p := h.left
      Or.elim (h.right)
        (fun hq : q =>
          show (p ∧ q) ∨ (p ∧ r) from Or.inl ⟨hp, hq⟩)
        (fun hr : r =>
          show (p ∧ q) ∨ (p ∧ r) from Or.inr ⟨hp, hr⟩))
    (fun h : (p ∧ q) ∨ (p ∧ r) =>
      Or.elim h
        (fun hpq : p ∧ q =>
          have hp : p := hpq.left
          have hq : q := hpq.right
          show p ∧ (q ∨ r) from ⟨hp, Or.inl hq⟩)
        (fun hpr : p ∧ r =>
          have hp : p := hpr.left
          have hr : r := hpr.right
          show p ∧ (q ∨ r) from ⟨hp, Or.inr hr⟩))

-- 고전적 추론을 필요로 하는 예제
example (p q : Prop) : ¬(p ∧ ¬q) → (p → q) :=
  fun h : ¬(p ∧ ¬q) =>
  fun hp : p =>
  show q from
    Or.elim (em q)
      (fun hq : q => hq)
      (fun hnq : ¬q => absurd (And.intro hp hnq) h)
```

연습문제
---------

 "sorry"를 실제 증명으로 바꿔 다음 항등식을 증명하세요.

```lean
variable (p q r : Prop)

-- ∧과 ∨의 교환성
example : p ∧ q ↔ q ∧ p := sorry
example : p ∨ q ↔ q ∨ p := sorry

-- ∧과 ∨의 결합성
example : (p ∧ q) ∧ r ↔ p ∧ (q ∧ r) := sorry
example : (p ∨ q) ∨ r ↔ p ∨ (q ∨ r) := sorry

-- 분배성
example : p ∧ (q ∨ r) ↔ (p ∧ q) ∨ (p ∧ r) := sorry
example : p ∨ (q ∧ r) ↔ (p ∨ q) ∧ (p ∨ r) := sorry

-- 기타 성질들
example : (p → (q → r)) ↔ (p ∧ q → r) := sorry
example : ((p ∨ q) → r) ↔ (p → r) ∧ (q → r) := sorry
example : ¬(p ∨ q) ↔ ¬p ∧ ¬q := sorry
example : ¬p ∨ ¬q → ¬(p ∧ q) := sorry
example : ¬(p ∧ ¬p) := sorry
example : p ∧ ¬q → ¬(p → q) := sorry
example : ¬p → (p → q) := sorry
example : (¬p ∨ q) → (p → q) := sorry
example : p ∨ False ↔ p := sorry
example : p ∧ False ↔ False := sorry
example : (p → q) → (¬q → ¬p) := sorry
```

다음 항등식을 증명하세요. "sorry"를 실제 증명으로 대체하세요. 이것은 고전적 추론이 필요합니다.

```lean
open Classical

variable (p q r s : Prop)

example : (p → r ∨ s) → ((p → r) ∨ (p → s)) := sorry
example : ¬(p ∧ q) → ¬p ∨ ¬q := sorry
example : ¬(p → q) → p ∧ ¬q := sorry
example : (p → q) → (¬p ∨ q) := sorry
example : (¬q → ¬p) → (p → q) := sorry
example : p ∨ ¬p := sorry
example : (((p → q) → p) → p) := sorry
```

고전 논리를 사용하지 않고 ``¬(p ↔ ¬p)``을 증명하세요.
