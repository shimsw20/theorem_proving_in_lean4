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

Lean's syntax can be extended and customized by users at every level,
ranging from basic "mixfix" notations to custom elaborators.  In fact,
all builtin syntax is parsed and processed using the same mechanisms
and APIs open to users.  In this section, we will describe and explain
the various extension points.

While introducing new notations is a relatively rare feature in
programming languages and sometimes even frowned upon because of its
potential to obscure code, it is an invaluable tool in formalization
for expressing established conventions and notations of the respective
field succinctly in code.  Going beyond basic notations, Lean's
ability to factor out common boilerplate code into (well-behaved)
macros and to embed entire custom domain specific languages (DSLs) to
textually encode subproblems efficiently and readably can be of great
benefit to both programmers and proof engineers alike.

### Notations and Precedence

The most basic syntax extension commands allow introducing new (or
overloading existing) prefix, infix, and postfix operators.

```lean
infixl:65   " + " => HAdd.hAdd  -- left-associative
infix:50    " = " => Eq         -- non-associative
infixr:80   " ^ " => HPow.hPow  -- right-associative
prefix:100  "-"   => Neg.neg
# set_option quotPrecheck false
postfix:max "⁻¹"  => Inv.inv
```

After the initial command name describing the operator kind (its
"fixity"), we give the *parsing precedence* of the operator preceded
by a colon `:`, then a new or existing token surrounded by double
quotes (the whitespace is used for pretty printing), then the function
this operator should be translated to after the arrow `=>`.

The precedence is a natural number describing how "tightly" an
operator binds to its arguments, encoding the order of operations.  We
can make this more precise by looking at the commands the above unfold to:

```lean
notation:65 lhs:65 " + " rhs:66 => HAdd.hAdd lhs rhs
notation:50 lhs:51 " = " rhs:51 => Eq lhs rhs
notation:80 lhs:81 " ^ " rhs:80 => HPow.hPow lhs rhs
notation:100 "-" arg:100 => Neg.neg arg
# set_option quotPrecheck false
notation:1024 arg:1024 "⁻¹" => Inv.inv arg  -- `max` is a shorthand for precedence 1024
```

It turns out that all commands from the first code block are in fact
command *macros* translating to the more general `notation` command.
We will learn about writing such macros below.  Instead of a single
token, the `notation` command accepts a mixed sequence of tokens and
named term placeholders with precedences, which can be referenced on
the right-hand side of `=>` and will be replaced by the respective
term parsed at that position.  A placeholder with precedence `p`
accepts only notations with precedence at least `p` in that place.
Thus the string `a + b + c` cannot be parsed as the equivalent of
`a + (b + c)` because the right-hand side operand of an `infixl` notation
has precedence one greater than the notation itself.  In contrast,
`infixr` reuses the notation's precedence for the right-hand side
operand, so `a ^ b ^ c` *can* be parsed as `a ^ (b ^ c)`.  Note that
if we used `notation` directly to introduce an infix notation like

```lean
# set_option quotPrecheck false
notation:65 lhs:65 " ~ " rhs:65 => wobble lhs rhs
```

where the precedences do not sufficiently determine associativity,
Lean's parser will default to right associativity.  More precisely,
Lean's parser follows a local *longest parse* rule in the presence of
ambiguous grammars: when parsing the right-hand side of `a ~` in
`a ~ b ~ c`, it will continue parsing as long as possible (as the current
precedence allows), not stopping after `b` but parsing `~ c` as well.
Thus the term is equivalent to `a ~ (b ~ c)`.

As mentioned above, the `notation` command allows us to define
arbitrary *mixfix* syntax freely mixing tokens and placeholders.

```lean
# set_option quotPrecheck false
notation:max "(" e ")" => e
notation:10 Γ " ⊢ " e " : " τ => Typing Γ e τ
```

Placeholders without precedence default to `0`, i.e. they accept notations of any precedence in their place.
If two notations overlap, we again apply the longest parse rule:

```lean
notation:65 a " + " b:66 " + " c:66 => a + b - c
#eval 1 + 2 + 3  -- 0
```

The new notation is preferred to the binary notation since the latter,
before chaining, would stop parsing after `1 + 2`.  If there are
multiple notations accepting the same longest parse, the choice will
be delayed until elaboration, which will fail unless exactly one
overload is type correct.


Coercions
---------

In Lean, the type of natural numbers, ``Nat``, is different from the
type of integers, ``Int``. But there is a function ``Int.ofNat`` that
embeds the natural numbers in the integers, meaning that we can view
any natural number as an integer, when needed. Lean has mechanisms to
detect and insert *coercions* of this sort.

```lean
variable (m n : Nat)
variable (i j : Int)

#check i + m      -- i + Int.ofNat m : Int
#check i + m + j  -- i + Int.ofNat m + j : Int
#check i + m + n  -- i + Int.ofNat m + Int.ofNat n : Int
```

Displaying Information
----------------------

There are a number of ways in which you can query Lean for information
about its current state and the objects and theorems that are
available in the current context. You have already seen two of the
most common ones, ``#check`` and ``#eval``. Remember that ``#check``
is often used in conjunction with the ``@`` operator, which makes all
of the arguments to a theorem or definition explicit. In addition, you
can use the ``#print`` command to get information about any
identifier. If the identifier denotes a definition or theorem, Lean
prints the type of the symbol, and its definition. If it is a constant
or an axiom, Lean indicates that fact, and shows the type.

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

Setting Options
---------------

Lean maintains a number of internal variables that can be set by users
to control its behavior. The syntax for doing so is as follows:

```
set_option <name> <value>
```

One very useful family of options controls the way Lean's *pretty- printer* displays terms. The following options take an input of true or false:

```
pp.explicit  : display implicit arguments
pp.universes : display hidden universe parameters
pp.notation  : display output using defined notations
```

As an example, the following settings yield much longer output:

```lean
set_option pp.explicit true
set_option pp.universes true
set_option pp.notation false

#check 2 + 2 = 4
#reduce (fun x => x + 2) = (fun x => x + 3)
#check (fun x => x + 1) 1
```

The command ``set_option pp.all true`` carries out these settings all
at once, whereas ``set_option pp.all false`` reverts to the previous
values. Pretty printing additional information is often very useful
when you are debugging a proof, or trying to understand a cryptic
error message. Too much information can be overwhelming, though, and
Lean's defaults are generally sufficient for ordinary interactions.



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

Using the Library
-----------------

To use Lean effectively you will inevitably need to make use of
definitions and theorems in the library. Recall that the ``import``
command at the beginning of a file imports previously compiled results
from other files, and that importing is transitive; if you import
``Foo`` and ``Foo`` imports ``Bar``, then the definitions and theorems
from ``Bar`` are available to you as well. But the act of opening a
namespace, which provides shorter names, does not carry over. In each
file, you need to open the namespaces you wish to use.

In general, it is important for you to be familiar with the library
and its contents, so you know what theorems, definitions, notations,
and resources are available to you. Below we will see that Lean's
editor modes can also help you find things you need, but studying the
contents of the library directly is often unavoidable. Lean's standard
library can be found online, on GitHub:

- [https://github.com/leanprover/lean4/tree/master/src/Init](https://github.com/leanprover/lean4/tree/master/src/Init)

- [https://github.com/leanprover/lean4/tree/master/src/Std](https://github.com/leanprover/lean4/tree/master/src/Std)

You can see the contents of these directories and files using GitHub's
browser interface. If you have installed Lean on your own computer,
you can find the library in the ``lean`` folder, and explore it with
your file manager. Comment headers at the top of each file provide
additional information.

Lean's library developers follow general naming guidelines to make it
easier to guess the name of a theorem you need, or to find it using
tab completion in editors with a Lean mode that supports this, which
is discussed in the next section. Identifiers are generally
``camelCase``, and types are `CamelCase`. For theorem names,
we rely on descriptive names where the different components are separated
by `_`s. Often the name of theorem simply describes the conclusion:

```lean
#check Nat.succ_ne_zero
#check Nat.zero_add
#check Nat.mul_one
#check Nat.le_of_succ_le_succ
```

Remember that identifiers in Lean can be organized into hierarchical
namespaces. For example, the theorem named ``le_of_succ_le_succ`` in the
namespace ``Nat`` has full name ``Nat.le_of_succ_le_succ``, but the shorter
name is made available by the command ``open Nat`` (for names not marked as
`protected`). We will see in [Chapter Inductive Types](./inductive_types.md)
and [Chapter Structures and Records](./structures_and_records.md)
that defining structures and inductive data types in Lean generates
associated operations, and these are stored in
a namespace with the same name as the type under definition. For
example, the product type comes with the following operations:

```lean
#check @Prod.mk
#check @Prod.fst
#check @Prod.snd
#check @Prod.rec
```

The first is used to construct a pair, whereas the next two,
``Prod.fst`` and ``Prod.snd``, project the two elements. The last,
``Prod.rec``, provides another mechanism for defining functions on a
product in terms of a function on the two components. Names like
``Prod.rec`` are *protected*, which means that one has to use the full
name even when the ``Prod`` namespace is open.

With the propositions as types correspondence, logical connectives are
also instances of inductive types, and so we tend to use dot notation
for them as well:

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

Auto Bound Implicit Arguments
-----------------

In the previous section, we have shown how implicit arguments make functions more convenient to use.
However, functions such as `compose` are still quite verbose to define. Note that the universe
polymorphic `compose` is even more verbose than the one previously defined.

```lean
universe u v w
def compose {α : Type u} {β : Type v} {γ : Type w}
            (g : β → γ) (f : α → β) (x : α) : γ :=
  g (f x)
```

You can avoid the `universe` command by providing the universe parameters when defining `compose`.

```lean
def compose.{u, v, w}
            {α : Type u} {β : Type v} {γ : Type w}
            (g : β → γ) (f : α → β) (x : α) : γ :=
  g (f x)
```

Lean 4 supports a new feature called *auto bound implicit arguments*. It makes functions such as
`compose` much more convenient to write. When Lean processes the header of a declaration,
any unbound identifier is automatically added as an implicit argument *if* it is a single lower case or
greek letter. With this feature we can write `compose` as

```lean
def compose (g : β → γ) (f : α → β) (x : α) : γ :=
  g (f x)

#check @compose
-- {β : Sort u_1} → {γ : Sort u_2} → {α : Sort u_3} → (β → γ) → (α → β) → α → γ
```
Note that Lean inferred a more general type using `Sort` instead of `Type`.

Although we love this feature and use it extensively when implementing Lean,
we realize some users may feel uncomfortable with it. Thus, you can disable it using
the command `set_option autoImplicit false`.
```lean
set_option autoImplicit false
/- The following definition produces `unknown identifier` errors -/
-- def compose (g : β → γ) (f : α → β) (x : α) : γ :=
--   g (f x)
```

Implicit Lambdas
---------------

In Lean 3 stdlib, we find many
[instances](https://github.com/leanprover/lean/blob/master/library/init/category/reader.lean#L39) of the dreadful `@`+`_` idiom.
It is often used when we the expected type is a function type with implicit arguments,
and we have a constant (`reader_t.pure` in the example) which also takes implicit arguments. In Lean 4, the elaborator automatically introduces lambdas
for consuming implicit arguments. We are still exploring this feature and analyzing its impact, but the experience so far has been very positive. Here is the example from the link above using Lean 4 implicit lambdas.

```lean
# variable (ρ : Type) (m : Type → Type) [Monad m]
instance : Monad (ReaderT ρ m) where
  pure := ReaderT.pure
  bind := ReaderT.bind
```

Users can disable the implicit lambda feature by using `@` or writing
a lambda expression with `{}` or `[]` binder annotations.  Here are
few examples

```lean
# namespace ex2
def id1 : {α : Type} → α → α :=
  fun x => x

def listId : List ({α : Type} → α → α) :=
  (fun x => x) :: []

-- In this example, implicit lambda introduction has been disabled because
-- we use `@` before `fun`
def id2 : {α : Type} → α → α :=
  @fun α (x : α) => id1 x

def id3 : {α : Type} → α → α :=
  @fun α x => id1 x

def id4 : {α : Type} → α → α :=
  fun x => id1 x

-- In this example, implicit lambda introduction has been disabled
-- because we used the binder annotation `{...}`
def id5 : {α : Type} → α → α :=
  fun {α} x => id1 x
# end ex2
```

Sugar for Simple Functions
-------------------------

In Lean 3, we can create simple functions from infix operators by
using parentheses. For example, `(+1)` is sugar for `fun x, x + 1`. In
Lean 4, we generalize this notation using `·` As a placeholder. Here
are a few examples:

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

As in Lean 3, the notation is activated using parentheses, and the lambda abstraction is created by collecting the nested `·`s.
The collection is interrupted by nested parentheses. In the following example, two different lambda expressions are created.

```lean
#check (Prod.mk · (· + 1))
-- fun a => (a, fun b => b + 1)
```

Named Arguments
---------------

Named arguments enable you to specify an argument for a parameter by
matching the argument with its name rather than with its position in
the parameter list.  If you don't remember the order of the parameters
but know their names, you can send the arguments in any order. You may
also provide the value for an implicit parameter when Lean failed to
infer it. Named arguments also improve the readability of your code by
identifying what each argument represents.

```lean
def sum (xs : List Nat) :=
  xs.foldl (init := 0) (·+·)

#eval sum [1, 2, 3, 4]
-- 10

example {a b : Nat} {p : Nat → Nat → Nat → Prop} (h₁ : p a b b) (h₂ : b = a)
    : p a a b :=
  Eq.subst (motive := fun x => p a x b) h₂ h₁
```

In the following examples, we illustrate the interaction between named
and default arguments.

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

Ellipses are also useful when explicit argument can be automatically
inferred by Lean, and we want to avoid a sequence of `_`s.

```lean
example (f : Nat → Nat) (a b c : Nat) : f (a + b + c) = f (a + (b + c)) :=
  congrArg f (Nat.add_assoc ..)
```
