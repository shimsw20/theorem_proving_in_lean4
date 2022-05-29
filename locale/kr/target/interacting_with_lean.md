린과 상호작용하기
=====================

정의한 수학적 대상과 증명을 만드는 언어 모두로써 여러분은 이제 기초적인 의존 유형론에 친숙합니다. 한 가지 여러분이 놓친 작동원리는 새로운 데이터 형을 정의하는 것에 대한 것입니다. 우리는 다음 장에서 *inductive data type*의 개념을 도입하여 이 간극을 메울 것입니다. 그러나 우선 이 장에서 우리는 유형론의 원리로부터 떨어져서 린과 상호작용하는 것에 대한 실용적인 면을 탐색해봅시다

여기서 찾은 모든 정보가 여러분에게 바로 유용하지 않을 수 있습니다. 우리는 린의 특징에 대한 감을 얻도록 건너뛰고 읽어보는 것을 추천합니다. 그리고 필요하다면 다시 여기로 돌아오세요.

파일 불러오기
---------------

린의 프론트 엔드의 목표는 사용자의 입력을 해석하고 형식적인 표현을 만들고 그들이 잘 형성되었고 옳바른 유형인지 확인하는 것입니다. 또한 린은 다양한 끊임없는 확인과 피드백을 제공하는 편집기의 사용을 지원합니다. 린에 대한 더 많은 정보는 [documentation pages](http://leanprover.github.io/documentation/)에서 찾을 수 있습니다.

린의 정의와 정리 표준 라이브러리는 다수의 파일에 걸쳐 펴져있습니다. 사용자는 아마 추가적인 라이브러리의 사용 혹은 다수의 파일에 걸쳐 자신만의 프로젝트를 개발하기를 원할지도 모릅니다. 린이 시작될 때, 이는 자동적으로 라이브러리 ``Init`` 폴더의 내용을 불러옵니다.
여기에는 다수의 기초적인 정의와 구성이 포함되어 있습니다. 그 결과 우리가 여기에 소개하는 대부분의 예제는 상식 밖의 것입니다.

그러나 여러분이 추가 파일을 사용하길 원한다면 파일의 시작에서 ``import`` 구문을 통해 수동으로 불러와야 합니다. 명령

```
import Bar.Baz.Blah
```
린의 파일 *search path*에 상대적인 주소로 설명된 곳에서 ``Bar/Baz/Blah.olean``을 불러옵니다. 어떻게 탐색경로가 결정되는지에 대한 정보는 [documentation pages](http://leanprover.github.io/documentation/)에서 찾아볼 수 있습니다.
기본적으로 이는 표준 라이브러리 경로와 (같은 맥락에서) 사용자의 로컬 프로젝트의 루트 경로를 포함합니다. 어떤 이는 현재 경로에 상대적으로 불러오기를 명시할 수 있습니다. 예를 들어 불러오는 것은 전이적입니다. 다시 말하면, 여러분이 ``Foo``를 부르고 ``Foo``는 ``Bar``를 불러온다면
여러분은 ``Bar``의 내용에도 접근할 수 있습니다. 그리고 명시적으로 불러올 필요가 없습니다.

섹션에 대해 더 알아보기
----------------

린은 이론을 구조화하는 것을 돕기 위해 구획을 나누는 다양한 메커니즘을 제공합니다. 여러분은 [Variables and Sections](./dependent_type_theory.md#variables_and_sections)에서 ``section`` 명령으로 필요하다면
함께 할 이론의 요소를 한데 묶을 수 있을 뿐만 아니라 정리와 정의에 인수로 삽입될 변수를 선언할 수도 있습니다. `variable` 명령의 요점은 다음 예제에서 처럼 정리에서 사용하기 위한 변수를 선언하는 것임을 기억하세요.

```lean
section
variable (x y : Nat)

def double := x + x

#check double y
#check double (2 * x)

attribute [local simp] Nat.add_assoc Nat.add_comm Nat.add_left_comm

theorem t1 : double (x + y) = double x + double y := by
  simp [double]

#check t1 y
#check t1 (2 * x)

theorem t2 : double (x * y) = double x * y := by
  simp [double, Nat.add_mul]

end
```

``double``의 정의는 ``x``를 인수로서 정의할 필요가 없습니다.
린은 종속성을 감지하고 그것을 자동적으로 삽입합니다. 마찬가지로 린은 ``t1``와 ``t2``에서 ``x``의 나타남을 감지하고 
거기에도 자동적으로 그것을 삽입합니다.
double은 ``y``를 인수로서 갖지 *않음*을 주목하세요. 변수는 오직 그들이 실제로 사용되는 선언에만 포함됩니다.

이름공간에 대해 더 알아보기
------------------

린에서 식별자는 ``Foo.Bar.baz``처럼 계층적인 *names*으로 제시됩니다. 우리는 [Namespaces](./dependent_type_theory.md#namespaces)에서 린이 계층적인 이름으로 작업하는 메커니즘을 제공하는 것을 보았습니다. ``namespace foo`` 명령은  ``end foo``와 마추치기 전까지 ``foo``가 각 정의와 정리의 이름에 앞에 붙게 합니다. ``open foo`` 명령은 접두사 ``foo``로 시작하는 정의와 정리에 일시적인 *별명*으로 만듭니다.

```lean
namespace Foo
def bar : Nat := 1
end Foo

open Foo

#check bar
#check Foo.bar
```

다음 정의  
```lean
def Foo.bar : Nat := 1
```
은 매크로로 간주되고 
```lean
namespace Foo
def bar : Nat := 1
end Foo
```

로 확장됩니다. 정리와 정의의 이름은 고유하여야 함에도 별명은 그들을 식별하는 별명은 그렇지 않습니다. 우리가 이름공간을 열때, 식별자는 모호하다고 할 지 모릅니다. 린은 맥락에서 의미의 모호함을 해소하려고 유형 정보를 사용하려고 합니다. 
그러나 여러분은 이들의 완전한 이름을 주는 것으로 모호성을 항상 풀 수 있습니다. 이 끝에서 문자열 ``_root_``이 빈 접두사를 나타냅니다.

```lean
def String.add (a b : String) : String :=
  a ++ b

def Bool.add (a b : Bool) : Bool :=
  a != b

def add (α β : Type) : Type := Sum α β

open Bool
open String
-- #check add -- ambiguous
#check String.add           -- String → String → String
#check Bool.add             -- Bool → Bool → Bool
#check _root_.add           -- Type → Type → Type

#check add "hello" "world"  -- String
#check add true false       -- Bool
#check add Nat Nat          -- Type
```

우리느 더 짤은 별명이 생기는 것을 ``protected``  키워드를 사용하여 막을 수 있습니다.

```lean
protected def Foo.bar : Nat := 1

open Foo

-- #check bar -- error
#check Foo.bar
```

흔한 이름들의 과부하를 막기 위해 ``Nat.rec``과 ``Nat.recOn`` 같은 이름들에 종종 사용됩니다.

``open`` 명령은 변형을 허용합니다. The command

```lean
open Nat (succ zero gcd)
#check zero     -- Nat
#eval gcd 15 6  -- 3
```

나열된 식별자들만을 위한 별명을 만드세요. The command

```lean
open Nat hiding succ gcd
#check zero     -- Nat
-- #eval gcd 15 6  -- error
#eval Nat.gcd 15 6  -- 3
```

나열된 식별자를 *제외한* ``Nat`` 이름공간 속 모든 것에 대한 별명을 만듭니다.

```lean
open Nat renaming mul → times, add → plus
#eval plus (times 2 2) 3  -- 7
```

``Nat.mul``을 ``times`` 으로 그리고 ``Nat.add``을 ``plus``로 다시 이름지어 별명을 만드세요.

별명을 한 이름 공간에서 다른 곳 혹은 최상위 단계로 ``내보내기``하는 것은 때때로 유용합니다. The command

```lean
export Nat (succ add sub)
```

이 이름공간이 열리기만 하면 별명을 이용할 수 있도록 현재 이름공간에 ``succ``과 ``add``과 ``sub``에 대한 별명을 만듭니다. 이 명령이 이름공간 밖에서 사용된다면 별명은 최상위 단계로 내보내지게 됩니다.


특성
----------

린의 주요 기능은 사용자의 입력을 커널에 의해 올바름이 검증된 형식 표현식으로 번역하는 것과 나중에 사용할 수 있도록 환경에 저장해두는 것 입니다. 그러나 환경 속 대상에 특성을 할당하는 것이나  기호를 정의하는 것 또는[Chapter Type Classes](./type_classes.md)에서 설명할 유형 클래스의 개체를 선언하는 것으로 몇 가지 명령은 환경에 대해 다른 영향을 받습니다. 대개 이런 명령들은 전역 효과를 갖습니다. 그 말은 즉, 그들이 현재 파일 뿐 아니라 그것을 불러오는 모든 파일에 대해 영향이 남는다는 것입니다. 하지만 이런 명령은 종종 이들이 현재 ``section``이나 ``namespace``이 닫힐 때까지 혹은 현재 파일의 끝까지만 유효하다는 것을 가리키는 ``local`` 수정자를 제공합니다.

[Section Using the Simplifier](./tactics.md#_using_the_simp)에서 우리는 정리들이 단순화기에 의한 사용이 가능하도록 만드는 ``[simp]`` 특성이 붙는 것을 보았습니다.
다음 예제에서는 리스트에 대한 접두사 관계를 정의하고, 이 관계는 반사적임을 증명하고, 그 정리에 ``[simp]`` 특성을 부여합니다.

```lean
def isPrefix (l₁ : List α) (l₂ : List α) : Prop :=
  ∃ t, l₁ ++ t = l₂

@[simp] theorem List.isPrefix_self (as : List α) : isPrefix as as :=
  ⟨[], by simp⟩

example : isPrefix [1, 2, 3] [1, 2, 3] := by
  simp
```

그럼 단순화기는 ``isPrefix [1, 2, 3] [1, 2, 3]``을 그것이 ``True``라고 다시쓰기하여 증명합니다.

어떤 이는 이 정의를 만든 뒤 어느 때든지 특성을 부여할 수 있습니다.

```lean
# def isPrefix (l₁ : List α) (l₂ : List α) : Prop :=
#  ∃ t, l₁ ++ t = l₂
theorem List.isPrefix_self (as : List α) : isPrefix as as :=
  ⟨[], by simp⟩

attribute [simp] List.isPrefix_self
```

모든 경우에 대해서, 특성은 선언이 있는 파일을 불러온 임의의 파일에 대해 영향을 미칩니다. 범위를 제한하기 위해 ``local`` 수정자를 추가하기

```lean
# def isPrefix (l₁ : List α) (l₂ : List α) : Prop :=
#  ∃ t, l₁ ++ t = l₂
section

theorem List.isPrefix_self (as : List α) : isPrefix as as :=
  ⟨[], by simp⟩

attribute [local simp] List.isPrefix_self

example : isPrefix [1, 2, 3] [1, 2, 3] := by
  simp

end

-- Error:
-- example : isPrefix [1, 2, 3] [1, 2, 3] := by
--  simp
```

다른 예제에서 우리는 ``instance`` 명령을 `isPrefix`관계에 ``≤``기호를 부여하는 데 사용할 수 있습니다.  [Chapter Type Classes](./type_classes.md)에서 설명할 그 명령은 연관된 정의에 ``[instance]`` 특성을 배정하는 것으로 동작합니다.

```lean
def isPrefix (l₁ : List α) (l₂ : List α) : Prop :=
  ∃ t, l₁ ++ t = l₂

instance : LE (List α) where
  le := isPrefix

theorem List.isPrefix_self (as : List α) : as ≤ as :=
  ⟨[], by simp⟩
```

그 배정는 지역적으로 만들어 질 수도 있습니다.

```lean
# def isPrefix (l₁ : List α) (l₂ : List α) : Prop :=
#   ∃ t, l₁ ++ t = l₂
def instLe : LE (List α) :=
  { le := isPrefix }

section
attribute [local instance] instLe

example (as : List α) : as ≤ as :=
  ⟨[], by simp⟩

end

-- Error:
-- example (as : List α) : as ≤ as :=
--  ⟨[], by simp⟩
```

아래 [Section Notation](#notation)에서 우리는 린의 기호를 정의하는 메커니즘에 대해 얘기하고 또 이들이 ``local`` 수정자를 지원함을 볼 예정입니다. 하지만 [Section Setting Options](#setting_options)에서 우리는 린의 이 패턴을 따르지 *않는* 옵션 설정에 대한 메커니즘에 대해서 얘기할 것입니다. 옵션은 지역적으로*만* 설정될 수 있습니다. 그 말은 즉, 그들의 범위는 항상 현재 섹션이나 현재 파일로 제한됩니다.

암시적인 인수에 대해 더 알아보기
--------------------------

[Section Implicit Arguments](./dependent_type_theory.md#implicit_arguments)에서 우리는 린은 항 ``t``의 유형을 ``{x : α} → β x``으로 표시하고 나서 중괄호는 ``x``가  *암시적인 인수*로써 ``t``로 표시되었음을 나타냄을 봤습니다. 이는 우리가 ``t``를 쓰는 언제든지 자리차지자 혹은 "구멍"이 삽입되고 ``t``는 ``@t _``로 대체됨을 의미합니다. 여러분이 이것이 일어나기 원하지 않는다면 대신 ``@t``를 써줘야 합니다.

암시적인 인수는 간절히 삽입됨을 주의하세요. 우리가 인수를 제시하여 함수 ``f (x : Nat) {y : Nat} (z : Nat)``을 정의했다고 합시다. 그럼, 우리가 표현식 ``f 7``을 추가 인수없이 슬때, 이는 ``f 7 _``와 같이 구문 분석 될 것입니다. 린은 종종 자리차지자가 이후의 명시적인 인수 *앞에* 추가되어야 함을 나타내는 약한 주석 ``{{y : ℕ}}``을 제공합니다. 이런 주석은 ``⦃y : Nat⦄``으로서 사용해 쓸 수도 있습니다. 여기서 유니코드 괄호는 각각 ``\{{``과 ``\}}``으로 쳐서 입력될 수 있습니다. 이 주석으로 표현식 ``f 7``은 이대로 구문분석 될 수 있습니다. 반면 ``f 7 3``은 강한 주석을 쓸 때처럼 ``f 7 _ 3``으로 구문분석될 것입니다.

차이를 설명하자면 유클리드 관계의 반사성은 모두 대칭적이고 추이적임을 보이는 다음 예제를 생각해보세요.

```lean
def reflexive {α : Type u} (r : α → α → Prop) : Prop :=
  ∀ (a : α), r a a

def symmetric {α : Type u} (r : α → α → Prop) : Prop :=
  ∀ {a b : α}, r a b → r b a

def transitive {α : Type u} (r : α → α → Prop) : Prop :=
  ∀ {a b c : α}, r a b → r b c → r a c

def euclidean {α : Type u} (r : α → α → Prop) : Prop :=
  ∀ {a b c : α}, r a b → r a c → r b c

theorem th1 {α : Type u} {r : α → α → Prop}
            (reflr : reflexive r) (euclr : euclidean r)
            : symmetric r :=
  fun {a b : α} =>
  fun (h : r a b) =>
  show r b a from euclr h (reflr _)

theorem th2 {α : Type u} {r : α → α → Prop}
            (symmr : symmetric r) (euclr : euclidean r)
            : transitive r :=
  fun {a b c : α} =>
  fun (rab : r a b) (rbc : r b c) =>
  euclr (symmr rab) rbc

theorem th3 {α : Type u} {r : α → α → Prop}
            (reflr : reflexive r) (euclr : euclidean r)
            : transitive r :=
 @th2 _ _ (@th1 _ _ reflr @euclr) @euclr

variable (r : α → α → Prop)
variable (euclr : euclidean r)

#check euclr  -- r ?m1 ?m2 → r ?m1 ?m3 → r ?m2 ?m3
```

결과는 작은 단계들로 나눠집니다. ``th1``은 반사적이고 유클리디안은 대칭적이다는 관계를 증명하고 ``th2``은 대칭적이고 유클리디언은 추이적이다는 관계를 증명합니다. 그런 뒤 ``th3``는 이 두 결과를 결합합니다. 하지만 ``th1``과 ``th2``, ``euclr``에서 암시적인 인수를 수동적으로 이 기능을 해제했음을 보세요. 그렇지 않으면 너무 많은 암시적인 인수가 삽입됩니다. 문제는 우리가 약한 암시적인 인수를 사용하면 사라집니다.

```lean
def reflexive {α : Type u} (r : α → α → Prop) : Prop :=
  ∀ (a : α), r a a

def symmetric {α : Type u} (r : α → α → Prop) : Prop :=
  ∀ {{a b : α}}, r a b → r b a

def transitive {α : Type u} (r : α → α → Prop) : Prop :=
  ∀ {{a b c : α}}, r a b → r b c → r a c

def euclidean {α : Type u} (r : α → α → Prop) : Prop :=
  ∀ {{a b c : α}}, r a b → r a c → r b c

theorem th1 {α : Type u} {r : α → α → Prop}
            (reflr : reflexive r) (euclr : euclidean r)
            : symmetric r :=
  fun {a b : α} =>
  fun (h : r a b) =>
  show r b a from euclr h (reflr _)

theorem th2 {α : Type u} {r : α → α → Prop}
            (symmr : symmetric r) (euclr : euclidean r)
            : transitive r :=
  fun {a b c : α} =>
  fun (rab : r a b) (rbc : r b c) =>
  euclr (symmr rab) rbc

theorem th3 {α : Type u} {r : α → α → Prop}
            (reflr : reflexive r) (euclr : euclidean r)
            : transitive r :=
  th2 (th1 reflr euclr) euclr

variable (r : α → α → Prop)
variable (euclr : euclidean r)

#check euclr  -- euclidean r
```

대괄호 ``[``과 ``]``로 표시된 세 번째 종류의 암시적인 매개변수가 있습니다. [Chapter Type Classes](./type_classes.md)에서 설명할 이들은 유형 클래스에 대해서 사용되었습니다.

기호
--------

린의 식별자들은 임의의 그리스 문자를 포함해 (우리가 본 ∀ , Σ , λ 외에도  종속 유형론에서 특별한 의미를 갖습니다.) 알파벳과 수치 문자를 포함할 수 있습니다. 이들은 아래첨자를 넣고자 하는 문자 다음에  ``\_``을 쳐 넣음으로써 아래첨자도 포함할 수 있습니다.

린의 구문분석기는 확장가능성이 있습니다. 그 말은 우리가 새로운 기호를 정의할 수 있다는 뜻입니다.

린의 문법은 모든 수준에서 사용자에 의해 기본적인 "혼합 수정" 기호에서 관습적인 협력기에 이르기까지 확장되거나 사용자가 정의해 쓸 수 있습니다.  사실 모든 내장 문법은 같은 메커니즘과 사용자에게 개방된 API를 사용하여 구문분석되고 처리됩니다.  이 섹션에서 우리는 다양한 확장성에 대해 보여주고 설명할 예정입니다.

새로운 기호를 도입하는 것은 프로그래밍 언어에서 상대적으로 흔치 않은 특징이고 때떄로는 그것이 잠재적으로 코드를 모호하게 하여 종종 난처하게 함에도 이는 세워진 관행들과 각 분야의 기호를 코드에서 간결하게 표현하는 것에 대한 형식화에 있어서 귀중한 도구입니다.  기본 기호를 넘어서 흔한 상용구 코드(잘 동작하는)를 매크로로 묶고 전체 사용자 정의 도메인 특정 언어(domain specific languages, DSLs)를 포함해 하위 문제를 효율적이고 가독성있게 텍스트로 인코딩하는 린의 능력은 프로그래머와 증명 엔지니어 같은 모든 이에게 큰 이득이 될 수 있습니다.

### 기호와 결합순서

가장 기본적인 문법 확장 명령은 새로운 (혹은 이미 있는 것을 오버로딩하는 것) 전위, 중위 그리고 후위 연산자를 도입하는 것을 허용합니다.

```lean
infixl:65   " + " => HAdd.hAdd  -- left-associative
infix:50    " = " => Eq         -- non-associative
infixr:80   " ^ " => HPow.hPow  -- right-associative
prefix:100  "-"   => Neg.neg
# set_option quotPrecheck false
postfix:max "⁻¹"  => Inv.inv
```

연산자 종류를 설명하는 초기 명령 이름 뒤에 (해당 "결합위치"), 콜론 `:`으로 앞서는 연산자의  *구문분석 우선순위*를 줍니다. 그 뒤 새로운 혹은 존재하는 토큰(깔끔한 출력을 위해 공백기호가 사용됨)은 큰 따옴표로 둘러쌓입니다. 그러면 이 연산자의 기능은 뒤따르는 화살표 `=>`로 번역되어야 합니다.

연산의 순서를 부호화하는 우선순위는 연산자가 그것의 인자와 얼마나 "강력하게" 묶여있는지를 설명하는 자연수입니다.  우리는 위의 명령을 다음으로 펼쳐보는 것으로 이를 더 정확하게 만들 수 있습니다.

```lean
notation:65 lhs:65 " + " rhs:66 => HAdd.hAdd lhs rhs
notation:50 lhs:51 " = " rhs:51 => Eq lhs rhs
notation:80 lhs:81 " ^ " rhs:80 => HPow.hPow lhs rhs
notation:100 "-" arg:100 => Neg.neg arg
# set_option quotPrecheck false
notation:1024 arg:1024 "⁻¹" => Inv.inv arg  -- `max` is a shorthand for precedence 1024
```

첫 번째 코드 블럭으로부터 모든 명령은 사실 *macros* 명령이 더 일반적인 `notation`명령으로 번역된 것임이 드러납니다.
우리는 아래에서 그런 매크로를 쓰는 법에 대해 배울 예정입니다.  한 토큰 대신 `notation` 명령은 토큰의 혼합된 열과 이름이 붙고 우선순위가 있는 항 자리차지자를 받아들입니다. 그리고 이는`=>`의 우변을 참조할 수 있고 그 위치에서 구문 분석된 개별적인 항으로 대체될 것입니다.  우선순위가 `p`인 자리차지자는 오직 그 자리에 적어도 `p` 순위인 기호만을 받아들입니다.
따라서 문자열 `a + b + c`는 `a + (b + c)`와 동등한 것으로 분석될 수 없습니다. 왜냐하면 `infixl`표기의 우변의 피연산자가 그 자체의 표기보다 하나 큰 우선순위를 갖기 때문입니다.  반대로, `infixr`은 우변의 피연산자 표기의 우선순위를 재사용합니다. 그래서 `a ^ b ^ c`은 `a ^ (b ^ c)`으로 구문분석 *될* 수 있습니다.  만약 우리가 이처럼 `notation`를 전위 표기를 바로 도입하도록 사용한다면

```lean
# set_option quotPrecheck false
notation:65 lhs:65 " ~ " rhs:65 => wobble lhs rhs
```

여기서 우선순위는 결합성을 결정하기에 충분하지 않아서  린의 구문분석기는 오른쪽 결합성으로 기본설정을 할 것입니다.  더 정확히는 린의 구문분석기는 모호한 문법의 존재에 대해 지역의 *가장 긴 구문분석* 규칙을 따릅니다. `a ~ b ~ c`에서 `a ~`의 우변을 분석할 때 구문분석기는 (현재 우선순위가 허용하는 만큼) 가능한 최대한 분석을 지속할 것입니다. `b` 뒤에서 멈추지 않고  `~ c`에서도 분석을 멈추지 않습니다.
따라서 항은 `a ~ (b ~ c)`과 동등합니다.

위에서 언급한 대로, `notation` 명령은 우리가 임의의 자유롭게 토큰과 자리차지자를 혼합한 *mixfix* 문법을 정의하도록 합니다.

```lean
# set_option quotPrecheck false
notation:max "(" e ")" => e
notation:10 Γ " ⊢ " e " : " τ => Typing Γ e τ
```

우선순위가 없는 자리차지자는 `0`으로 설정됩니다. 예를 들어 이들은 그들의 자리에 임의의 우선순위의 기호든 받습니다.
만약 두 기호가 겹치면, 우리는 다시 가장 긴 구문분석 규칙을 적용합니다.

```lean
notation:65 a " + " b:66 " + " c:66 => a + b - c
#eval 1 + 2 + 3  -- 0
```

새로운 기호는 이항기호로 정의되길 선호합니다. 왜냐면 뒤에 나올 것은 연결되기 전에 `1 + 2` 뒤에 분석을 멈춥니다.  동일한 가장 긴 구문분석을 받아들이는 다수의 기호가 있다면 협력할 때까지 선택은 미뤄집니다. 그리고 이것은 정확히 한 오버로드가 유형이 옳바르지 않는 한 실패할 것 입니다.


강제 형 변환
---------

린에서 자연수 유형 ``Nat``은 정수의 유형 ``Int``과는 다릅니다. 그러나 정수에 자연수가 내장되도록 하는 ``Int.ofNat`` 함수가 있어서 필요할 때 임의의 자연수를 정수로 볼 수 있게 합니다. 린은 이런 종류의 *coercions*의 감지와 삽입하는 메커니즘이 있습니다.

```lean
variable (m n : Nat)
variable (i j : Int)

#check i + m      -- i + Int.ofNat m : Int
#check i + m + j  -- i + Int.ofNat m + j : Int
#check i + m + n  -- i + Int.ofNat m + Int.ofNat n : Int
```

정보 표시하기
----------------------

여러분이 린에게 그것의 현재 상태와 현재 상황에서 사용할 수 있는 대상과 정리에 대한 정보를 요청하는 여러가지 방법이 있습니다. 여러분은 가장 흔한 것 중 두 개인 ``#check``과 ``#eval``를 봤습니다. ``#check``는  ``@`` 연산자와 결합하여 종종 사용됨을 기억하세요. 이는 정리나 정의의 모든 인수를 명시적이게 합니다. 게다가 여러분은 ``#print`` 명령을 사용해서 임의의 식별자에 대한 정보를 얻을 수 있습니다. 만약 식별자가 정의나 정리를 의미한다면 린은 기호의 유형과 그것의 정의를 출력합니다. 만약 그것이 상수나 공리라면 린은 그 사실을 가리키고 유형을 보여줍니다.

```lean
-- examples with equality
#check Eq
#check @Eq
#check Eq.symm
#check @Eq.symm

#print Eq.symm

-- examples with And
#check And
#check And.intro
#check @And.intro

-- a user-defined function
def foo {α : Type u} (x : α) : α := x

#check foo
#check @foo
#print foo
```

옵션 설정하기
---------------

린은 사용자가 설정하여 그 행동을 제어하는 하는 다수의 내부 변수를 관리합니다. 그렇게 하는 문법은 다음과 같습니다.

```
set_option <name> <value>
```

매우 유용한 옵션 모음 중 하나는 린의 *pretty- printer*가 항을 표시하는 방식을 제어합니다. 다음 옵션은 입력으로 참 혹은 거짓을 받습니다.

```
pp.explicit  : display implicit arguments
pp.universes : display hidden universe parameters
pp.notation  : display output using defined notations
```

예제로 다음 설정은 훨씬 더 긴 출력을 만듭니다.

```lean
set_option pp.explicit true
set_option pp.universes true
set_option pp.notation false

#check 2 + 2 = 4
#reduce (fun x => x + 2) = (fun x => x + 3)
#check (fun x => x + 1) 1
```

``set_option pp.all true`` 명령은 이 설정을 한번에 수행합니다. 반면 ``set_option pp.all false``은 이전의 값으로 되돌립니다. 깔끔한 출력하기의 추가 정보는 증명의 버그를 없앨때나 암호같은 오류 메시지를 이해하려고 할 때 아주 유용합니다. 너무 많은 정보에 압도할 수 있지만 린의 기본설정도 평범한 상호작용에 일반적으로 충분합니다.



<!--
Elaboration Hints
-----------------

When you ask Lean to process an expression like ``λ x y z, f (x + y) z``, you are leaving information implicit. For example, the types of ``x``, ``y``, and ``z`` have to be inferred from the context, the notation ``+`` may be overloaded, and there may be implicit arguments to ``f`` that need to be filled in as well. Moreover, we will see in :numref:`Chapter %s <type_classes>` that some implicit arguments are synthesized by a process known as *type class resolution*. And we have also already seen in the last chapter that some parts of an expression can be constructed by the tactic framework.

Inferring some implicit arguments is straightforward. For example, suppose a function ``f`` has type ``Π {α : Type*}, α → α → α`` and Lean is trying to parse the expression ``f n``, where ``n`` can be inferred to have type ``nat``. Then it is clear that the implicit argument ``α`` has to be ``nat``. However, some inference problems are *higher order*. For example, the substitution operation for equality, ``eq.subst``, has the following type:

.. code-block:: text

    eq.subst : ∀ {α : Sort u} {p : α → Prop} {a b : α},
                 a = b → p a → p b

Now suppose we are given ``a b : ℕ`` and ``h₁ : a = b`` and ``h₂ : a * b > a``. Then, in the expression ``eq.subst h₁ h₂``, ``P`` could be any of the following:

-  ``λ x, x * b > x``
-  ``λ x, x * b > a``
-  ``λ x, a * b > x``
-  ``λ x, a * b > a``

In other words, our intent may be to replace either the first or second ``a`` in ``h₂``, or both, or neither. Similar ambiguities arise in inferring induction predicates, or inferring function arguments. Even second-order unification is known to be undecidable. Lean therefore relies on heuristics to fill in such arguments, and when it fails to guess the right ones, they need to be provided explicitly.

To make matters worse, sometimes definitions need to be unfolded, and sometimes expressions need to be reduced according to the computational rules of the underlying logical framework. Once again, Lean has to rely on heuristics to determine what to unfold or reduce, and when.

There are attributes, however, that can be used to provide hints to the elaborator. One class of attributes determines how eagerly definitions are unfolded: constants can be marked with the attribute ``[reducible]``, ``[semireducible]``, or ``[irreducible]``. Definitions are marked ``[semireducible]`` by default. A definition with the ``[reducible]`` attribute is unfolded eagerly; if you think of a definition as serving as an abbreviation, this attribute would be appropriate. The elaborator avoids unfolding definitions with the ``[irreducible]`` attribute. Theorems are marked ``[irreducible]`` by default, because typically proofs are not relevant to the elaboration process.

It is worth emphasizing that these attributes are only hints to the elaborator. When checking an elaborated term for correctness, Lean's kernel will unfold whatever definitions it needs to unfold. As with other attributes, the ones above can be assigned with the ``local`` modifier, so that they are in effect only in the current section or file.

Lean also has a family of attributes that control the elaboration strategy. A definition or theorem can be marked ``[elab_with_expected_type]``, ``[elab_simple]``. or ``[elab_as_eliminator]``. When applied to a definition ``f``, these bear on elaboration of an expression ``f a b c ...`` in which ``f`` is applied to arguments. With the default attribute, ``[elab_with_expected_type]``, the arguments ``a``, ``b``, ``c``, ... are elaborating using information about their expected type, inferred from ``f`` and the previous arguments. In contrast, with ``[elab_simple]``, the arguments are elaborated from left to right without propagating information about their types. The last attribute, ``[elab_as_eliminator]``, is commonly used for eliminators like recursors, induction principles, and ``eq.subst``. It uses a separate heuristic to infer higher-order parameters. We will consider such operations in more detail in the next chapter.

Once again, these attributes can be assigned and reassigned after an object is defined, and you can use the ``local`` modifier to limit their scope. Moreover, using the ``@`` symbol in front of an identifier in an expression instructs the elaborator to use the ``[elab_simple]`` strategy; the idea is that, when you provide the tricky parameters explicitly, you want the elaborator to weigh that information heavily. In fact, Lean offers an alternative annotation, ``@@``, which leaves parameters before the first higher-order parameter implicit. For example, ``@@eq.subst`` leaves the type of the equation implicit, but makes the context of the substitution explicit.

-->

라이브러리 사용하기
-----------------

린을 효과적으로 사용하기 위해서 여러분은 라이브러리의 정의와 정리의 사용이 불가피하게 될 것입니다. 파일의 시작에서  ``import`` 명령은 다른 파일로부터 이전에 컴파일된 결과를 불러오고 그 불러오기는 추이적임을 기억하세요. 만약 여러분이 ``Foo``를 가져오고 ``Foo``가 ``Bar``를 가져오면 ``Bar``에서 이용가능한 정의와 정리도 여러분이 사용할 수 있습니다. 그러나 더 짧은 이름을 제공하는 이름공간을 여는 동작은 앞에서처럼 다른 파일에 영향을 주지 못합니다. 각 파일에서 여러분은 여러분이 사용하려는 이름공간을 열어야 합니다.

일반적으로 여러분이 라이브러리와 그것의 내용물에 친숙해지는 것이 중요합니다. 그래야 여러분이 어떤 정리, 정의, 기호, 자원을 쓸 수 있는지 압니다. 아래에서 우리는 린의 편집기 모드는 여러분이 필요한 것을 찾도록 돕는 것을 봅니다. 그러나 라이브러리의 내용을 공부하는 것은 대게 불가피합니다. 린의 표준 라이브러리는 깃허브에서 찾을 수 있습니다.

- [https://github.com/leanprover/lean4/tree/master/src/Init](https://github.com/leanprover/lean4/tree/master/src/Init)

- [https://github.com/leanprover/lean4/tree/master/src/Std](https://github.com/leanprover/lean4/tree/master/src/Std)

여러분은 깃허브 브라우저 인터페이스로 이 디렉토리와 파일의 내용물을 볼 수 있습니다. 여러분이 여러분 컴퓨터에 린을 설치했다면 여러분은 ``lean`` 폴더에서 라이브러리를 찾을 수 있습니다. 그리고 파일관리자로 그것을 탐색할 수 있습니다. 각 파일의 꼭대기에 도입부 주석은 추가 정보를 제공합니다.

린의 라이브러리 개발자는 여러분이 필요한 정리의 이름을 추측하기 더 쉽게 일반적인 이름짓기 규칙을 따릅니다. 혹은 린 모드인 편집기의 탭 완성 지원 기능으로 그것을 찾도록 돕습니다. 탭 완성은 다음 섹션에서 얘기합니다. 식별자들은 보통 ``camelCase``이고 유형은 `CamelCase`입니다. 정리 이름에 대해, 우리는 다른 부분은 `_`들로 나뉜 설명하는 이름에 의존합니다. 정리의 이름은 종종 결론을 설명합니다.

```lean
#check Nat.succ_ne_zero
#check Nat.zero_add
#check Nat.mul_one
#check Nat.le_of_succ_le_succ
```

린의 식별자들은 계층적인 이름공간 안에 정리될 수 있음을 기억하세요. 예를 들어, 정리는 이름공간 ``Nat`` 에서 ``le_of_succ_le_succ``으로 이름지어진 정리는 ``Nat.le_of_succ_le_succ``을 긴 이름으로 갖습니다. 그러나 더 짧은 이름은 ``open Nat`` 명령으로 사용할 수 있게 됩니다.(`protected`로 표시된 이름을 제외하고) 우리는 [Chapter Inductive Types](./inductive_types.md)와  [Chapter Structures and Records](./structures_and_records.md)에서 린에서 구조체와 유도 데이터 형을 정의하는 것은 연관된 연산을 생성함을 볼 예정입니다. 그리고 이들은 정의에 대해 유형으로써 같은 이름으로 이름공간에 저장됩니다. 예를들어 곱 유형은 다음 연산을 동반합니다.

```lean
#check @Prod.mk
#check @Prod.fst
#check @Prod.snd
#check @Prod.rec
```

첫 째는 쌍을 구성하는데 사용되며 반면 다음 둘은``Prod.fst``과 ``Prod.snd``은 두 원소를 투영(project)합니다. 마지막으로 ``Prod.rec``은 두 원소에 대한 함수에 대한 관점으로 곱에 대한 함수를 정의하는 또다른 방법을 제공합니다. ``Prod.rec``같은 이름은 *protected*입니다. 그말은 누군가가 ``Prod`` 이름공간을 개방했더라도 완전한 이름을 사용해야만 함을 의미합니다.

유형으로써 명제 대응에서 논리 결합자도 유도형의 개체들입니다. 그리고 그들에 대해서도 점 표기를 사용하는 경향이 있습니다.

```lean
#check @And.intro
#check @And.casesOn
#check @And.left
#check @And.right
#check @Or.inl
#check @Or.inr
#check @Or.elim
#check @Exists.intro
#check @Exists.elim
#check @Eq.refl
#check @Eq.subst
```

자동적으로 구속된 암시적인 인자
-----------------

이전 섹션에서 우리는 어떻게 암시적인 인자가 함수를 쓰기 더 편리하게 만드는지 보았습니다.
그러나 `compose`같은 함수들은 여전히 정의하기에 꽤 장황합니다. 심지어 세계 다형적 `compose`는 이전에 정의한 것보다 더 장황합니다.

```lean
universe u v w
def compose {α : Type u} {β : Type v} {γ : Type w}
            (g : β → γ) (f : α → β) (x : α) : γ :=
  g (f x)
```

여러분은 `compose`를 정의할 때 세계 매개변수를 제공하여 `universe` 명령을 피할 수 있습니다.

```lean
def compose.{u, v, w}
            {α : Type u} {β : Type v} {γ : Type w}
            (g : β → γ) (f : α → β) (x : α) : γ :=
  g (f x)
```

린 4는 *auto bound implicit arguments*라 하는 새로운 기능을 지원합니다. 이것은 `compose` 같은 함수를 쓰기에 훨씬 더 편리하게 만듭니다. 린이 선언의 헤더를 처리할 때 만약 이것이 한 글자의 소문자나 그리스 문자이면 임의의 구속되지 않은 식별자가 자동적으로 암시적인 매개변수로 추가됩니다. 이 기능으로 우리는 `compose`를 이와 같이 쓸 수 있습니다.

```lean
def compose (g : β → γ) (f : α → β) (x : α) : γ :=
  g (f x)

#check @compose
-- {β : Sort u_1} → {γ : Sort u_2} → {α : Sort u_3} → (β → γ) → (α → β) → α → γ
```
린은 `Type`대신 `Sort`를 사용하여 더 일반적인 유형을 추론함을 보세요.

우리가 이 기능을 좋아하고 린을 구현할 때 광범위하게 이를 사용했지만 우리는 어떤 사용자들이 이것에 대해 불편하게 느끼는 것을 깨달았습니다. 따라서 여러분은 이것을 `set_option autoImplicit false` 명령을 써서 해제할 수 있습니다.
```lean
set_option autoImplicit false
/- The following definition produces `unknown identifier` errors -/
-- def compose (g : β → γ) (f : α → β) (x : α) : γ :=
--   g (f x)
```

암시적인 람다
---------------

린 3의 표준라이브러리에서 우리는 치명적인 `@`+`_` 구문의 수 많은 [instances](https://github.com/leanprover/lean/blob/master/library/init/category/reader.lean#L39)를 발견했습니다.
이것은 우리가 기대하는 유형이 암시적인 인자를 갖는 함수 유형일 때 종종 사용합니다. 그리고 우리는 암시적인 인수를 받을 수 있는 상수(예제에서 `reader_t.pure`)를 갖습니다. 린 4에서 협력기는 자동적으로 암시적인 인자를 소모하기 위해 람다를 도입합니다. 우리는 여전히 이 기능을 탐색하고 있고, 그것의 영향을 분석합니다. 그러나 지금까지의 경험은 아주 긍정적입니다. 링크 위로부터 린 4의 암시적인 람다를 사용하는 에제가 있습니다.

```lean
# variable (ρ : Type) (m : Type → Type) [Monad m]
instance : Monad (ReaderT ρ m) where
  pure := ReaderT.pure
  bind := ReaderT.bind
```

사용자는 `@`을 사용하거나 `{}` 이나 `[]`의 결합 주석으로 람다 표현식을 쓰는 것으로 암시적인 람다 기능을 해제할 수 있습니다.  여기 몇 가지 예제가 있습니다.

```lean
# namespace ex2
def id1 : {α : Type} → α → α :=
  fun x => x

def listId : List ({α : Type} → α → α) :=
  (fun x => x) :: []

-- 우리는 `fun` 앞에 `@`를 쓰기 때문에 
-- 이 예제에서 암시적인 람다의 도입은 해제되었습니다.
def id2 : {α : Type} → α → α :=
  @fun α (x : α) => id1 x

def id3 : {α : Type} → α → α :=
  @fun α x => id1 x

def id4 : {α : Type} → α → α :=
  fun x => id1 x

-- 이 예제에서 암시적인 람다의 도입은 결합 주석 `{...}`을
-- 사용했기 때문에 해제되었습니다. 
def id5 : {α : Type} → α → α :=
  fun {α} x => id1 x
# end ex2
```

간단한 함수를 위한 설탕
-------------------------

린 3에서는 괄호를 사용해 전위 연산자로부터 간단한 함수를 만들 수 있습니다. 예를 들어 `(+1)`은 `fun x, x + 1`에 대한 설탕입니다. 린 4에서 우리는 `·`를 자리차지자로 사용하여  이 표기를 일반화합니다. 여기 몇 가지 예제가 있습니다.

```lean
# namespace ex3
#check (· + 1)
-- fun a => a + 1
#check (2 - ·)
-- fun a => 2 - a
#eval [1, 2, 3, 4, 5].foldl (·*·) 1
-- 120

def f (x y z : Nat) :=
  x + y + z

#check (f · 1 ·)
-- fun a b => f a 1 b

#eval [(1, 2), (3, 4), (5, 6)].map (·.1)
-- [1, 3, 5]
# end ex3
```

린 3에서처럼 표기는 괄호를 사용해 활성화되고 람다 추상화는 중첩된 `·`의 모음으로 만들어집니다.
모음은 중첩된 괄호에 의해 중단됩니다. 다음 예제에서 다른 두 가지 람다 표현식이 만들어집니다.

```lean
#check (Prod.mk · (· + 1))
-- fun a => (a, fun b => b + 1)
```

이름 인자
---------------

이름 인자는 여러분이 매개변수 리스트에 대한 그것의 위치보다는 그것의 이름으로 매개변수에 대한 인자를 명시하게 해줍니다.  여러분이 매개변수의 순서를 기억하지 못해도 그들의 이름을 알면 여러분은 임의의 순서로든 인자를 보낼 수 있습니다. 여러분은 린이 그것에 대해 추론을 실패했을 때 암시적인 매개변수에 대한 값을 제공할 수도 있습니다. 이름 지어진 인자들은 각 인자가 나타내는 것을 명시함으로써 여러분의 코드의 가독성을 개선합니다.

```lean
def sum (xs : List Nat) :=
  xs.foldl (init := 0) (·+·)

#eval sum [1, 2, 3, 4]
-- 10

example {a b : Nat} {p : Nat → Nat → Nat → Prop} (h₁ : p a b b) (h₂ : b = a)
    : p a a b :=
  Eq.subst (motive := fun x => p a x b) h₂ h₁
```

다음 예제에서 우리는 이름 지어진 것과 기본 인자 사이의 상호작용을 설명합니다.

```lean
def f (x : Nat) (y : Nat := 1) (w : Nat := 2) (z : Nat) :=
  x + y + w - z

example (x z : Nat) : f (z := z) x = x + 1 + 2 - z := rfl

example (x z : Nat) : f x (z := z) = x + 1 + 2 - z := rfl

example (x y : Nat) : f x y = fun z => x + y + 2 - z := rfl

example : f = (fun x z => x + 1 + 2 - z) := rfl

example (x : Nat) : f x = fun z => x + 1 + 2 - z := rfl

example (y : Nat) : f (y := 5) = fun x z => x + 5 + 2 - z := rfl

def g {α} [Add α] (a : α) (b? : Option α := none) (c : α) : α :=
  match b? with
  | none   => a + c
  | some b => a + b + c

variable {α} [Add α]

example : g = fun (a c : α) => a + c := rfl

example (x : α) : g (c := x) = fun (a : α) => a + x := rfl

example (x : α) : g (b? := some x) = fun (a c : α) => a + x + c := rfl

example (x : α) : g x = fun (c : α) => x + c := rfl

example (x y : α) : g x y = fun (c : α) => x + y + c := rfl
```

You can use `..` to provide missing explicit arguments as `_`.
This feature combined with named arguments is useful for writing patterns. 여기 예제가 있습니다.

```lean
inductive Term where
  | var    (name : String)
  | num    (val : Nat)
  | add    (fn : Term) (arg : Term)
  | lambda (name : String) (type : Term) (body : Term)

def getBinderName : Term → Option String
  | Term.lambda (name := n) .. => some n
  | _ => none

def getBinderType : Term → Option Term
  | Term.lambda (type := t) .. => some t
  | _ => none
```

Ellipses도 명시적인 인자가 린으로부터 자동적으로 추론될 수 있을 때와 우리가  `_`들의 나열을 피하고자 할 때 유용합니다.

```lean
example (f : Nat → Nat) (a b c : Nat) : f (a + b + c) = f (a + (b + c)) :=
  congrArg f (Nat.add_assoc ..)
```
