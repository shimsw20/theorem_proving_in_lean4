# 유형 클래스

유형 클래스는 함수형 프로그래밍 언어에서 특수 목적(ad-hoc)의 다형성을 활성화하는 원칙적인 방법으로 도입되었습니다. 우리는 먼저 함수가 단순히 덧셈의 특정 유형에 대한 구현을 덧셈의 인수로 취한 다음 나머지 인수에 대해 그 구현을 호출하면 임시 다형적 함수(덧셈 같은)를 구현하는 것이 쉽다는 것을 관찰했습니다. 예를 들어 덧셈의 구현을 유지하기 위해 린에 구조체를 선언한다고 해봅시다.
```lean
# namespace Ex
structure Add (a : Type) where
  add : a -> a -> a

#check @Add.add
-- Add.add : {a : Type} → Add a → a → a → a
# end Ex
```
위의 린 코드에서 `add`은 `Add.add : {α : Type} → Add α → α → α → α`형 입니다. 여기서 유형 `a` 주위의 중괄호는 이것이 암시적인 인수임을 의미합니다.
우리는 `double`을 아래와 같이 구현할 수 있습니다.
```lean
# namespace Ex
# structure Add (a : Type) where
#  add : a -> a -> a
def double (s : Add a) (x : a) : a :=
  s.add x x

#eval double { add := Nat.add } 10
-- 20

#eval double { add := Nat.mul } 10
-- 100

#eval double { add := Int.add } 10
-- 20

# end Ex
```
여러분은 자연수 `n`을 `double { add := Nat.add } n`으로 두 배로 할 수 있습니다.
당연히 이처럼 구현을 수동적으로 넘겨야 한다면 사용자에게 아주 성가실 것 입니다.
물론 이는 특수 목적 다형성의 잠재적 이점의 대부분을 좌절시킬 것입니다.

유형 클래스 뒤편의 주요 아이디어는 `Add a` 같은 인수를 암시적으로 만드는 것이고 사용자 정의 개체들의 데이터베이스를 사용해 유형 클래스 해결책으로 알려진 과정을 통해 원하는 개체를 자동적으로 합성하는 것입니다. 린에서 위 예제에서`structure`를 `class`로 바꿈으로 `Add.add`형이 됩니다.
```lean
# namespace Ex
class Add (a : Type) where
  add : a -> a -> a

#check @Add.add
-- Add.add : {a : Type} → [self : Add a] → a → a → a
# end Ex
```
여기서 대괄호는 `Add a`의 유형이 *instance implicit*임을 가리킵니다. 즉, 이것은 유형클래스 해결책을 사용해 합성되어야 합니다. `add`의 이 버전은 하스켈 항 `add :: Add a => a -> a -> a`의 린 닮은꼴입니다.
마찬가지로 우리는 개체를 다음과 같이 등록할 수 있습니다.
```lean
# namespace Ex
# class Add (a : Type) where
#  add : a -> a -> a
instance : Add Nat where
  add := Nat.add

# end Ex
```
그런 다음 `n : Nat` 및 `m : Nat`에 대해 항 `Add.add n m`는 `Add Nat`의 목표를 유형 클래스 해결책으로 만듭니다. 그리고 유형 클래스 해결책은 위의 개체를 합성합니다. 일반적으로 개체는 다른 개체에 복잡한 방식으로 종속될 수 있습니다. 예를 들어 여러분이 (익명) 개체를 `a`가 덧셈을 갖는다면 `Array a`도 덧셈을 갖는다고 서술해 선언할 수 있습니다.
```lean
instance [Add a] : Add (Array a) where
  add x y := Array.zipWith x y (. + .)

#eval Add.add #[1, 2] #[3, 4]
-- #[4, 6]

#eval #[1, 2] + #[3, 4]
-- #[4, 6]
```
 `x + y`는 린에서 `Add.add x y`에 대한 기호임을 주의하세요.

위의 예제는 어떻게 유형 클래스가 기호를 중복(overload)시키는데 사용되는지 시연합니다.
여기서 우리는 다른 적용을 탐색합니다. 우린 종종 주어진 유형의 임의의 원소를 필요로 합니다.
유형은 린에서 임의의 원소가 아닐 수 있음을 기억하세요.
우리는 정의가 "막다른 경우"에 대해 임의의 원소를 반환하게 만들고 싶은 상황이 종종 있습니다. 예를 들어 ``xs``가 ``List a``형일 때 표현식 ``head xs``가 ``a``형이 되길 좋아합니다.
마찬가지로 많은 정리는 유형이 비어 있지 않을 때 덧셈 가정에  대해서 성립합니다.
예를 들어 ``a``가 유형이면 ``exists x : a, x = x``은 ``a``가 비어있지 않을 때에만 참입니다.
표준 라이브러리는 유형 클래스 추론이 내재된 유형의 "기본" 원소를 유추할 수 있도록 유형 클래스 ``Inhabited``를 정의합니다.
위 프로그램의 첫 단계인 적절한 클래스를 선언하는 것부터 시작합시다.

```lean
# namespace Ex
class Inhabited (a : Type u) where
  default : a

#check @Inhabited.default
-- Inhabited.default : {a : Type u} → [self : Inhabited a] → a
# end Ex
```
`Inhabited.default`가 어떤 명시적인 인수도 갖지 않음을 주목하세요.

클래스 ``Inhabited a``의 원소는 단순히 어떤 원소 ``x : a``에 대한 ``Inhabited.mk x``꼴의 표현식입니다.
투영 ``Inhabited.default``은 ``Inhabited a``의 원소로부터 ``a``의 원소 같은 것을 "추출"하도록 해줄 것입니다.
이제 몇몇 개체로 클래스를 채우겠습니다.

```lean
# namespace Ex
# class Inhabited (a : Type _) where
#  default : a
instance : Inhabited Bool where
  default := true

instance : Inhabited Nat where
  default := 0

instance : Inhabited Unit where
  default := ()

instance : Inhabited Prop where
  default := True

#eval (Inhabited.default : Nat)
-- 0

#eval (Inhabited.default : Bool)
-- true
# end Ex
```
여러분은 g1>export` 명령으로 `Inhabited.default`에 대한 `기본` 별명을 만들 수 있습니다.
```lean
# namespace Ex
# class Inhabited (a : Type _) where
#  default : a
# instance : Inhabited Bool where
#  default := true
# instance : Inhabited Nat where
#  default := 0
# instance : Inhabited Unit where
#  default := ()
# instance : Inhabited Prop where
#  default := True
export Inhabited (default)

#eval (default : Nat)
-- 0

#eval (default : Bool)
-- true
# end Ex
```

## 연결 개체

그것이 유형 클래스 추론의 확장이라면 그리 인상적이지 않을 것 입니다. 이것은 협력기가 룩업 테이블에서 찾는 데 쓰는 단순히 개체의 리스트를 저장하는 메커니즘일 것입니다.
유형 클래스 추론을 강력하게 만드는 것은 *chain* 개체입니다. 즉, 개체 선언은 유형 클래스의 암시적인 개체에 차례로 의존하게 할 수 있습니다.
Prolog 같은 탐색에서 필요할 때 역추적하는데 개체를 통한 클래스 추론이 재귀적으로 연결되게 합니다.

예를 들어 다음 정의는 만약 두 유형 ``a``와 ``b``가 내재되었다면 그들의 곱도 그렇다는 것을 보여줍니다.
```lean
instance [Inhabited a] [Inhabited b] : Inhabited (a × b) where
  default := (default, default)
```
더 이전에 개체 선언에 이것을 추가하여 유형 클래스 개체는 예를 들어 ``Nat × Bool``의 기본 원소를 추론할 수 있습니다.
```lean
# namespace Ex
# class Inhabited (a : Type u) where
#  default : a
# instance : Inhabited Bool where
#  default := true
# instance : Inhabited Nat where
#  default := 0
# constant default [Inhabited a] : a :=
#  Inhabited.default
instance [Inhabited a] [Inhabited b] : Inhabited (a × b) where
  default := (default, default)

#eval (default : Nat × Bool)
-- (0, true)
# end Ex
```
마찬가지로 우리는 유형 함수를 적절한 상수 함수로 내재시킬 수 있습니다.
```lean
instance [Inhabited b] : Inhabited (a -> b) where
  default := fun _ => default
```
연습으로 `List`형과 `Sum`형 같은 다른 유형에 대한 기본 개체를 정의해보세요.

린 표준 라이브러리는 `inferInstance` 정의를 포함합니다. 이것은 `{α : Sort u} → [i : α] → α`형이고 예상 유형이 개체일 때 유형 클래스 해결 절차를 일으키는데 유용합니다.
```lean
#check (inferInstance : Inhabited Nat) -- Inhabited Nat

def foo : Inhabited (Nat × Nat) :=
  inferInstance

theorem ex : foo.default = (default, default) :=
  rfl
```
여러분은 `#print` 명령으로 `inferInstance`가 얼마나 단순한지 검사할 수 있습니다.
```lean
#print inferInstance
```

## ToString

다형적인 방법 `toString`은 `{α : Type u} → [ToString α] → α → String`형 입니다. 여러분은 여러분의 유형을 위한 개체를 구현하고 문자열로 복잡한 값에서 문자열로 연결하기를 사용합니다. 린은 대다수의 내장된 유형에 대한 `ToString`와 함께 나옵니다.
```lean
structure Person where
  name : String
  age  : Nat

instance : ToString Person where
  toString p := p.name ++ "@" ++ toString p.age

#eval toString { name := "Leo", age := 542 : Person }
#eval toString ({ name := "Daniel", age := 18 : Person }, "hello")
```
## 수치값(Numerals)

수치값들은 린에서 다형적입니다. 여러분은 수치값(예를 들어 `2`)을 유형클래스 `OfNat`을 구현하는 임의의 유형의 원소를 표시하는데 사용할 수 있습니다.
```lean
structure Rational where
  num : Int
  den : Nat
  inv : den ≠ 0

instance : OfNat Rational n where
  ofNat := { num := n, den := 1, inv := by decide }

instance : ToString Rational where
  toString r := s!"{r.num}/{r.den}"

#eval (2 : Rational) -- 2/1

#check (2 : Rational) -- Rational
#check (2 : Nat)      -- Nat
```
린은 항 `(2 : Nat)`과 `(2 : Rational)`을 각각 `OfNat.ofNat Nat 2 (instOfNatNat 2)`과
`OfNat.ofNat Rational 2 (instOfNatRational 2)`으로 만듭니다.
동화된 항에서 나타나는 수치값 `2`가 *생* 자연수라고 말합니다.
여러분은 생 자연수 `2`를 매크로 `nat_lit 2`을 사용해 입력할 수 있습니다.
```lean
#check nat_lit 2  -- Nat
```
생 자연수는 다형적이지 *않습니다.*

`OfNat` 개체는 수치에 대해 매개적입니다. 그래서 여러분은 특정 수치에 대해 개체를 정의할 수 있습니다.
두 번째 인수는 종종 위의 예제의 것처럼 변수이거나 *생(raw)* 자연수입니다.
```lean
class Monoid (α : Type u) where
  unit : α
  op   : α → α → α

instance [s : Monoid α] : OfNat α (nat_lit 1) where
  ofNat := s.unit

def getUnit [Monoid α] : α :=
  1
```

## 출력 매개변수

항 `T`는 알려져 있고 모르는 부분이 없을 때 기본적으로 린은 `Inhabited T` 개체만 합성하려고 합니다. 다음 명령은 "`Inhabited (Nat × ?m.1499)`에 대한 유형 클래스 개체를 생성하는데 실패했다(failed to create type class instance for `Inhabited (Nat × ?m.1499)`)"는 오류를 일으킵니다. 왜냐하면 유형에 모르는 부분(즉, `_`)이 있기 때문입니다.
```lean
#check_failure (inferInstance : Inhabited (Nat × _))
```
여러분은 유형 클래스 합성기에 대한 *입력*값으로써 유형 클래스 `Inhabited`의 매개변수를 볼 수 있습니다.
유형 클래스가 다수의 매개변수를 가질 때, 여러분은 출력 매개변수로 그들 중 몇을 표시할 수 있습니다.
이들의 매개변수에 모르는 부분이 있을 지라도 린은 유형 클래스 합성기를 시작할 것입니다.
다음 예제에서 우리는 출력 매개변수를 *이질적인* 다형적 곱셈을 정의하는데 사용합니다.
```lean
# namespace Ex
class HMul (α : Type u) (β : Type v) (γ : outParam (Type w)) where
  hMul : α → β → γ

export HMul (hMul)

instance : HMul Nat Nat Nat where
  hMul := Nat.mul

instance : HMul Nat (Array Nat) (Array Nat) where
  hMul a bs := bs.map (fun b => hMul a b)

#eval hMul 4 3           -- 12
#eval hMul 4 #[2, 3, 4]  -- #[8, 12, 16]
# end Ex
```
매개변수 `α`와 `β`는 입력 매개변수로 `γ`는 출력 매개변수 입니다.
활용 `hMul a b`에 대해서 `a`와 `b`의 유형이 알려진 뒤에 유형 클래스 합성기가 호출됩니다. 그리고 결과 유형은 출력 매개변수 `γ`로부터 얻어집니다.
위의 예제에서 우리는 두 개체를 정의 했습니다. 처음 것은 자연수에 대한 동형 곱셈입니다. 두 번째 것은 배열에 대한 스칼라 곱셈입니다.
여러분은 개체를 연결하고 두 번째 개체를 일반화함을 주목하세요.
```lean
# namespace Ex
class HMul (α : Type u) (β : Type v) (γ : outParam (Type w)) where
  hMul : α → β → γ

export HMul (hMul)

instance : HMul Nat Nat Nat where
  hMul := Nat.mul

instance : HMul Int Int Int where
  hMul := Int.mul

instance [HMul α β γ] : HMul α (Array β) (Array γ) where
  hMul a bs := bs.map (fun b => hMul a b)

#eval hMul 4 3                    -- 12
#eval hMul 4 #[2, 3, 4]           -- #[8, 12, 16]
#eval hMul (-2) #[3, -1, 4]       -- #[-6, 2, -8]
#eval hMul 2 #[#[2, 3], #[0, 4]]  -- #[#[4, 6], #[0, 8]]
# end Ex
```
여러분은 `HMul α β γ` 개체를 갖는 언제든지 우리의 새 스칼라 배열 곱셈 개체를 유형 `α`의 스칼라와 `Array β`형의 배열에 대해 사용할 수 있습니다.
지난 `#eval`에서 배열의 배열에 대해 개체가 두 번 사용되었음을 주목하세요.

## 기본 개체

클래스 `HMul`에서 매개변수 `α`와 `β`는 입력값으로 취급됩니다.
따라서 유형 클래스 합성은 이 두 유형이 알려진 뒤에야 시작합니다. 이것은 종종 너무 제한적일 수 있습니다.
```lean
# namespace Ex
class HMul (α : Type u) (β : Type v) (γ : outParam (Type w)) where
  hMul : α → β → γ

export HMul (hMul)

instance : HMul Int Int Int where
  hMul := Int.mul

def xs : List Int := [1, 2, 3]

-- Error "failed to create type class instance for HMul Int ?m.1767 (?m.1797 x)"
#check_failure fun y => xs.map (fun x => hMul x y)
# end Ex
```
`y`형으로 제공되지 않았으므로 개체 `HMul`은 린으로부터 생성되지 않습니다.
그러나 이 같은 상황에서 `y`형과 `x`형은 동일하다고 가정하는 것이 자연스럽습니다. 우리는 정확히 이를 *default instances*으로 달성할 수 있습니다.
```lean
# namespace Ex
class HMul (α : Type u) (β : Type v) (γ : outParam (Type w)) where
  hMul : α → β → γ

export HMul (hMul)

@[defaultInstance]
instance : HMul Int Int Int where
  hMul := Int.mul

def xs : List Int := [1, 2, 3]

#check fun y => xs.map (fun x => hMul x y)  -- Int -> List Int
# end Ex
```
`defaultInstance` 속성으로 위의 개체를 표시함으로써 우리는 린에게 유형 클래스 합성 문제로 보류 중인 이 개체를 사용하라고 가르킵니다.
실제 린에서 구현은 산술 연산자에 대한 동형과 이형 클래스를 정의합니다.
게다가 `a+b`, `a*b`, `a-b`, `a/b`과 `a%b`은 이형 버전에 대한 표기입니다.
개체 `OfNat Nat n`은 `OfNat` 클래스에 대한 (우선순위 100의) 기본 개체입니다. 이것이 기대되는 유형을 모를 때 수치값 `2`가 `Nat`형이 되는 이유입니다. 여러분은 내장된 것보다 우세하여 더 높은 우선순위를 갖는 기본 개체를 정의할 수 있습니다.
```lean
structure Rational where
  num : Int
  den : Nat
  inv : den ≠ 0

@[defaultInstance 200]
instance : OfNat Rational n where
  ofNat := { num := n, den := 1, inv := by decide }

instance : ToString Rational where
  toString r := s!"{r.num}/{r.den}"

#check 2 -- Rational
```
우선 순위는 다른 기본 개체들 간의 상호작용을 제어하는 데에도 유용합니다.
예를 들어 `xs.map (fun x => 2 * x)`으로 해석될 때 `xs`가 `α`형이라고 가정합시다. 우리는 `OfNat`에 대한 기본 개체보다 더 높은 우선 순위를 갖는 곱셈에 대한 동형 개체를 원합니다. 이것은 우리가 개체 `HMul α α α`만 구현하고 `HMul Nat α α`을 구현하지 않았을 때 특히 중요합니다.
이제 우리는 린에서 기호 `a*b`이 어떻게 정의되는지 드러냅니다.
```lean
# namespace Ex
class OfNat (α : Type u) (n : Nat) where
  ofNat : α

@[defaultInstance]
instance (n : Nat) : OfNat Nat n where
  ofNat := n

class HMul (α : Type u) (β : Type v) (γ : outParam (Type w)) where
  hMul : α → β → γ

class Mul (α : Type u) where
  mul : α → α → α

@[defaultInstance 10]
instance [Mul α] : HMul α α α where
  hMul a b := Mul.mul a b

infixl:70 " * "  => HMul.hMul
# end Ex
```
`Mul` 클래스는 동형 곱셈만 구현된 유형에 대해 편리합니다.

## 지역 개체

유형 클래스는 린의 속성을 사용해 구현됩니다. 따라서 여러분은 `local` 수정자로 그들이 오직 현재 닫힌``section``이나 ``namespace``까지만 혹은 현재 파일의 끝까지만 유효함을 나타내는데 사용할 수 있습니다.

```lean
structure Point where
  x : Nat
  y : Nat

section

local instance : Add Point where
  add a b := { x := a.x + b.x, y := a.y + b.y }

def double (p : Point) :=
  p + p

end -- instance `Add Point` is not active anymore

-- def triple (p : Point) :=
--  p + p + p  -- Error: failed to synthesize instance
```

여러분은 일시적으로 `attribute` 명령으로 현재 닫힌 ``section``이나 ``namespace``까지 혹은 현재 파일의 끝까지 개체를 사용 해제 할 수 있습니다.

```lean
structure Point where
  x : Nat
  y : Nat

instance addPoint : Add Point where
  add a b := { x := a.x + b.x, y := a.y + b.y }

def double (p : Point) :=
  p + p

attribute [-instance] addPoint

-- def triple (p : Point) :=
--  p + p + p  -- Error: failed to synthesize instance
```

우리는 이 명령을 여러분이 문제를 진단하는 데에만 사용하는 것을 권장합니다.

## 범위가 지정된 개체

여러분은 이름공간에서 범위가 지정된 개체를 선언할 수 있습니다. 이런 종류의 개체는 여러분이 이름공간 안에 있거나 이름공간을 개방했을 때에만 활동적입니다.

```lean
structure Point where
  x : Nat
  y : Nat

namespace Point

scoped instance : Add Point where
  add a b := { x := a.x + b.x, y := a.y + b.y }

def double (p : Point) :=
  p + p

end Point
-- instance `Add Point` is not active anymore

-- #check fun (p : Point) => p + p + p  -- Error

namespace Point
-- instance `Add Point` is active again
#check fun (p : Point) => p + p + p

end Point

open Point -- activates instance `Add Point`
#check fun (p : Point) => p + p + p
```

여러분은 `open scoped <namespace>` 명령으로 범위가 지정된 속정을 활성화할 수 있습니다. 그러나 이름공간으로부터 이름들을 "개방"하지는 않습니다.

```lean
structure Point where
  x : Nat
  y : Nat

namespace Point

scoped instance : Add Point where
  add a b := { x := a.x + b.x, y := a.y + b.y }

def double (p : Point) :=
  p + p

end Point

open scoped Point -- activates instance `Add Point`
#check fun (p : Point) => p + p + p

-- #check fun (p : Point) => double p -- Error: unknown identifier 'double'
```

## 결정 가능한 명제

표준 라이브러리에 정의된 유형 클래스의 다른 예 즉, ``결정 가능한`` 명제 유형 클래스를 고려해 봅시다. 대략적으로 말하면 ``Prop``의 원소는 그것이 참인지 거짓인지 결정할 수 있다면 결정 가능하다고 합니다. 이 구별은 직관주의적 수학에서만 유용합니다. 고전적으로 모든 명제는 결정 가능합니다. 그러나 우리가 고전 원리를 사용해 경우에 따라 함수를 정의하면 그 함수는 계산 불가일 겁니다. 알고리즘적으로 말하자면 ``Decidable`` 유형 클래스는 명제가 참인지 여부를 효과적으로 결정하는 절차를 추론하는데 사용될 수 있습니다. 결과적으로 유형 클래스는 그들이 가능할 때 그런 계산적 정의를 지원하는 동시에 고전적 정의와 고전 추론의 사용으로 원활히 넘어가는 것을 허용합니다.

표준 라이브러리에서 ``Decidable``은 다음과 같이 형식적으로 정의됩니다.

```lean
# namespace Hidden
class inductive Decidable (p : Prop) where
  | isFalse (h : ¬p) : Decidable p
  | isTrue  (h : p)  : Decidable p
# end Hidden
```

논리적으로 말하자면 원소 ``t : Decidable p``를 갖는 것은 원소 ``t : p ∨ ¬p``을 갖는 것보다 강합니다. 이는 우리가 ``p``의 진리값에 의존하는 임의의 유형의 값을 정의할 수 있게 합니다. 예를 들어 표현식 ``if p then a else b``를 이해하려면 우리는 ``p``가 결정 가능인지 알 필요가 있습니다. 그 표현식은 ``ite p a b``에 대한 문법적 설탕입니다. 여기서 ``ite`` 다음과 같이 정의됩니다.

```lean
# namespace Hidden
def ite {α : Sort u} (c : Prop) [h : Decidable c] (t e : α) : α :=
  Decidable.casesOn (motive := fun _ => α) h (fun _ => e) (fun _ => t)
# end Hidden
```

표준 라이브러리는 또 ``dite (the dependent if-then-else expression)``라는 ``ite``의 변종을 갖습니다. 이것은 다음과 같이 정의됩니다.

```lean
# namespace Hidden
def dite {α : Sort u} (c : Prop) [h : Decidable c] (t : c → α) (e : Not c → α) : α :=
  Decidable.casesOn (motive := fun _ => α) h e t
# end Hidden
```

즉, ``dite c t e``에서 우리는 ``hc : c``를 "then" 분기 그리고 "else" 분기에서 ``hnc : ¬ c``라고 가정할 수 있습니다. ``dite``를 사용하기 더 편리하게 만들기 위해 린은 우리가 ``dite c (λ h : c, t) (λ h : ¬ c, e)`` 대신 ``if h : c then t else e``로 쓸 수 있게 해줍니다.

고전 논리가 없으면 우리는 모든 명제가 결정 가능임을 증명할 수 없습니다. 그래도 우리는 *특정* 명제가 결정 가능임을 증명할 수 있습니다. 예를 들어 우리는 자연수와 정수에 대한 등식과 부등식 같은 기본 연산의 결정 가능성을 증명할 수 있습니다. 게다가 결정 가능성은 명제 연결사 하에 보존됩니다.

```lean
#check @instDecidableAnd
  -- {p q : Prop} → [Decidable p] → [Decidable q] → Decidable (And p q)

#check @instDecidableOr
#check @instDecidableNot
```

따라서 우리는 자연수에 대해 결정가능 술어에 대한 각 경우에 대해 정의를 이끌어 냅니다.

```lean
def step (a b x : Nat) : Nat :=
  if x < a ∨ x > b then 0 else 1

set_option pp.explicit true
#print step
```

단순히 적절한 개체를 적용함으로써 암시적인 인수을 여는 것은 협력기가 명제 ``x < a ∨ x > b``의 결정가능성을 추론함을 보일 수 있습니다.

고전적 공리로 우리는 모든 명제가 결정 가능임을 증명할 수 있습니다. `Classical`  이름공간을 여는 것으로 여러분은 고전적 공리를 불러올 수 있고 결정가능성의 일반적 개체를 만들 수 있습니다.

```lean
open Classical
```

그 후에 ``decidable p``는 모든 ``p``에 대해 개체를 갖습니다.
따라서 결정가능성 가정에 의존하는 라이브러리 속 모든 정리는 여러분이 고전적으로 추론하는 것을 원할 때 자유롭게 이용할 수 있습니다. [공리와 계산 장](./axioms_and_computation.md)에서 우리는 배중률을 사용해 함수를 정의하는 것은 그들이 계산적으로 사용되는 것을 막을 수 있음을 볼 것입니다. 따라서 표준 라이브러리는 `propDecidable` 개체에 낮은 우선 순위를 할당합니다.

```lean
# namespace Hidden
open Classical
noncomputable scoped
instance (priority := low) propDecidable (a : Prop) : Decidable a :=
  choice <| match em a with
    | Or.inl h => ⟨isTrue h⟩
    | Or.inr h => ⟨isFalse h⟩
# end Hidden
```

이렇게 하면 린이 다른 개체를 선호하고 결정가능성을 추론하려는 다른 시도가 실패한 후에만 ``propDecidable``으로 후퇴함을 보장합니다.

``Decidable`` 유형 클래스는 정리 증명에 대한 아주 작은 소규모의 자동화도 제공합니다. 표준 라이브러리는 단순한 목표를 풀기 위해 `Decidable` 개체를 사용하는 `decide` 전략을 도입합니다.

```lean
example : 10 < 5 ∨ 1 > 0 := by
  decide

example : ¬ (True ∧ False) := by
  decide

example : 10 * 20 = 200 := by
  decide

theorem ex : True ∧ 2 = 1+1 := by
  decide

#print ex
-- theorem ex : True ∧ 2 = 1 + 1 :=
-- of_decide_eq_true (Eq.refl true)

#check @of_decide_eq_true
-- ∀ {p : Prop} [Decidable p], decide p = true → p

#check @decide
-- (p : Prop) → [Decidable p] → Bool
```

이는 다음과 같이 동작합니다. 표현식 ``decide p``는 ``p``에 대한 결정 절차를 추론하려고 하고, 성공하면 ``true``나 ``false ``로 평가됩니다. 특히, ``p``가 정말로 닫힌 표현식이라면 ``decide p``는 정의로부터 불리언 ``true``로 축소됩니다.
``decide p = true``가 성립한다고 가정하면 ``of_decide_eq_true``는 ``p``의 증명을 생성합니다. ``decide`` 전략은 목표 ``p``를 증명하기 위해 모든 것을 한데 모읍니다. 전의 관찰로부터 ``decide``는 ``c``에 대한 추론된 결정 절차가 ``isTrue`` 사례에 대해 정의로부터 평가하기에 충분한 정보를 가질 때마다 성공할 것입니다.


유형 클래스 추론 관리하기
-----------------------------

린이 유형 클래스 추론으로 유추할 수 있는 표현식을 여러분이 제공해야 하는 상황에 있어 봤다면 여러분은 `inferInstance`를 사용해 린에게 추론을 이끌어내도록 요청할 수 있습니다.

```lean
def foo : Add Nat := inferInstance
def bar : Inhabited (Nat → Nat) := inferInstance

#check @inferInstance
-- {α : Sort u} → [α] → α
```

사실 여러분은 린의 ``(t : T)`` 기호로 여러분이 찾는 개체의 클래스를 엄밀하게 명시할 수 있습니다.

```lean
#check (inferInstance : Add Nat)
```

여러분은 부가 정의 `inferInstanceAs`도 사용할 수 있습니다.

```lean
#check inferInstanceAs (Add Nat)

#check @inferInstanceAs
-- (α : Sort u) → [α] → α
```


때때로 린은 클래스가 정의에 묻혀 있어 개채를 찾지 못할 수 있습니다. 예를 들어 ``Inhabited (Set α)``의 개체를 찾을 수 없습니다. 여러분은 명시적으로 이를 선언할 수 있습니다.

```lean

def Set (α : Type u) := α → Prop

-- fails
-- example : Inhabited (Set α) :=
--  inferInstance

instance : Inhabited (Set α) :=
  inferInstanceAs (Inhabited (α → Prop))
```

때때로 유형 클래스 추론이 예상한 인스턴스를 찾지 못하거나 더 심하게는 무한 루프에 빠져 시간이 초과되는 것을 발견할 수 있습니다. 이러한 상황에서 디버그를 돕기 위해 Lean을 사용하면 검색 추적을 요청할 수 있습니다.

```
set_option trace.Meta.synthInstance true
```

VS Code를 사용하는 경우 관련 정리 또는 정의 위로 마우스를 이동하거나 ``Ctrl-Shift-Enter``로 메시지 창을 열어 결과를 읽을 수 있습니다. Emacs에서 ``C-c C-x``를 사용하여 파일에서 독립적인 린 프로세스를 실행할 수 있으며 출력 버퍼는 유형 클래스 해결 절차가 이후에 사용될 때마다 추적을 표시합니다.

다음 옵션을 사용하여 검색을 제한할 수도 있습니다.
```
set_option synthInstance.maxHeartbeats 10000
set_option synthInstance.maxSize 400
```

`synthInstance.maxHeartbeats` 옵션은 유형 클래스 해결 문제 당 최대 심박수 양을 지정합니다. 심박수는 (작은) 메모리 할당(천 단위)의 수이고, 0은 제한이 없음을 의미합니다.
`synthInstance.maxSize` 옵션은 유형 클래스 개체 합성 절차에서 해을 만드는 데 사용되는 최대 개체수입니다.

또한 VS Code 및 Emacs 편집기 모드에서 탭 완성 기능은 ``set_option``에서 동작하므로 적절한 옵션을 찾는 데 도움이 됨을 기억하세요.

위에서 언급했듯이 주어진 상황의 유형 클래스 개체는 역추적 검색을 발생시키는 Prolog와 유사한 프로그램을 나타냅니다. 프로그램의 효율성과 발견된 해결책은 모두 시스템이 개체를 시도하는 순서에 따라 달라질 수 있습니다. 마지막에 선언된 개체가 가장 먼저 시도됩니다. 또한 개체가 다른 모듈에서 선언된 경우 시도되는 순서는 이름공간이 열린 순서에 의존합니다. 이름공간에 선언된 개체는 나중에 열린 것이 더 일찍 시도됩니다.

유형 클래스 개체에 *우선순위*를 할당하여 그들이 시도되는 순서를 변경할 수 있습니다. 개체가 선언되면 기본 우선 순위 값이 할당됩니다. 개체를 정의할 때 다른 우선 순위를 할당할 수 있습니다. 다음 예제는 이것이 어떻게 이뤄지는지 보여줍니다.

```lean
class Foo where
  a : Nat
  b : Nat

instance (priority := default+1) i1 : Foo where
  a := 1
  b := 1

instance i2 : Foo where
  a := 2
  b := 2

example : Foo.a = 1 :=
  rfl

instance (priority := default+2) i3 : Foo where
  a := 3
  b := 3

example : Foo.a = 3 :=
  rfl
```

<!--
TODO: we may change the coercion mechanism
.. _coercions_using_type_classes:

Coercions using Type Classes
----------------------------

The most basic type of coercion maps elements of one type to another. For example, a coercion from ``nat`` to ``int`` allows us to view any element ``n : nat`` as an element of ``int``. But some coercions depend on parameters; for example, for any type ``α``, we can view any element ``l : list α`` as an element of ``set α``, namely, the set of elements occurring in the list. The corresponding coercion is defined on the "family" of types ``list α``, parameterized by ``α``.

Lean allows us to declare three kinds of coercions:

-  from a family of types to another family of types
-  from a family of types to the class of sorts
-  from a family of types to the class of function types

The first kind of coercion allows us to view any element of a member of the source family as an element of a corresponding member of the target family. The second kind of coercion allows us to view any element of a member of the source family as a type. The third kind of coercion allows us to view any element of the source family as a function. Let us consider each of these in turn.

In Lean, coercions are implemented on top of the type class resolution framework. We define a coercion from ``α`` to ``β`` by declaring an instance of ``has_coe α β``. For example, we can define a coercion from ``bool`` to ``Prop`` as follows:

.. code-block:: lean

    instance bool_to_Prop : has_coe bool Prop :=
    ⟨λ b, b = tt⟩

This enables us to use boolean terms in if-then-else expressions:

.. code-block:: lean

    instance bool_to_Prop : has_coe bool Prop :=
    ⟨λ b, b = tt⟩
    -- BEGIN
    #reduce if tt then 3 else 5
    #reduce if ff then 3 else 5
    -- END

We can define a coercion from ``list α`` to ``set α`` as follows:

.. code-block:: lean

    def list.to_set {α : Type*} : list α → set α
    | []     := ∅
    | (h::t) := {h} ∪ list.to_set t

    instance list_to_set_coe (α : Type*) :
      has_coe (list α) (set α) :=
    ⟨list.to_set⟩

    def s : set nat  := {1, 2}
    def l : list nat := [3, 4]

    #check s ∪ l -- set nat

Coercions are only considered if the given and expected types do not contain metavariables at elaboration time. In the following example, when we elaborate the union operator, the type of ``[3, 2]`` is ``list ?m``, and a coercion will not be considered since it contains metavariables.

.. code-block:: lean

    def list.to_set {α : Type*} : list α → set α
    | []     := ∅
    | (h::t) := {h} ∪ list.to_set t

    instance list_to_set_coe (α : Type*) :
      has_coe (list α) (set α) :=
    ⟨list.to_set⟩

    def s : set nat  := {1, 2}

    -- BEGIN
    /- The following #check command produces an error. -/
    -- #check s ∪ [3, 2]
    -- END

We can work around this issue by using a type ascription.

.. code-block:: lean

    def list.to_set {α : Type*} : list α → set α
    | []     := ∅
    | (h::t) := {h} ∪ list.to_set t

    instance list_to_set_coe (α : Type*) :
      has_coe (list α) (set α) :=
    ⟨list.to_set⟩

    def s : set nat  := {1, 2}

    -- BEGIN
    #check s ∪ [(3:nat), 2]
    -- or
    #check s ∪ ([3, 2] : list nat)
    -- END

In the examples above, you may have noticed the symbol ``↑`` produced by the ``#check`` commands. It is the lift operator, ``↑t`` is notation for ``coe t``. We can use this operator to force a coercion to be introduced in a particular place. It is also helpful to make our intent clear, and work around limitations of the coercion resolution system.

.. code-block:: lean

    def list.to_set {α : Type*} : list α → set α
    | []     := ∅
    | (h::t) := {h} ∪ list.to_set t

    instance list_to_set_coe (α : Type*) :
      has_coe (list α) (set α) :=
    ⟨list.to_set⟩

    def s : set nat  := {1, 2}

    -- BEGIN
    #check s ∪ ↑[3, 2]

    variables n m : nat
    variable i : int
    #check i + ↑n + ↑m
    #check i + ↑(n + m)
    #check ↑n + i
    -- END

In the first two examples, the coercions are not strictly necessary since Lean will insert implicit nat → int coercions. However, ``#check n + i`` would raise an error, because the expected type of ``i`` is nat in order to match the type of n, and no int → nat coercion exists). In the third example, we therefore insert an explicit ``↑`` to coerce ``n`` to ``int``.

The standard library defines a coercion from subtype ``{x : α // p x}`` to ``α`` as follows:

.. code-block:: lean

    namespace hidden
    -- BEGIN
    instance coe_subtype {α : Type*} {p : α → Prop} :
      has_coe {x // p x} α :=
    ⟨λ s, subtype.val s⟩
    -- END
    end hidden

Lean will also chain coercions as necessary. Actually, the type class ``has_coe_t`` is the transitive closure of ``has_coe``. You may have noticed that the type of ``coe`` depends on ``has_lift_t``, the transitive closure of the type class ``has_lift``, instead of ``has_coe_t``. Every instance of ``has_coe_t`` is also an instance of ``has_lift_t``, but the elaborator only introduces automatically instances of ``has_coe_t``. That is, to be able to coerce using an instance of ``has_lift_t``, we must use the operator ``↑``. In the standard library, we have the following instance:

.. code-block:: lean

    namespace hidden
    universes u v

    instance lift_list {a : Type u} {b : Type v} [has_lift_t a b] :
      has_lift (list a) (list b) :=
    ⟨λ l, list.map (@coe a b _) l⟩

    variables s : list nat
    variables r : list int
    #check ↑s ++ r

    end hidden

It is not an instance of ``has_coe`` because lists are frequently used for writing programs, and we do not want a linear-time operation to be silently introduced by Lean, and potentially mask mistakes performed by the user. By forcing the user to write ``↑``, she is making her intent clear to Lean.

Let us now consider the second kind of coercion. By the *class of sorts*, we mean the collection of universes ``Type u``. A coercion of the second kind is of the form

.. code-block:: text

    c : Π x1 : A1, ..., xn : An, F x1 ... xn → Type u

where ``F`` is a family of types as above. This allows us to write ``s : t`` whenever ``t`` is of type ``F a1 ... an``. In other words, the coercion allows us to view the elements of ``F a1 ... an`` as types. This is very useful when defining algebraic structures in which one component, the carrier of the structure, is a ``Type``. For example, we can define a semigroup as follows:

.. code-block:: lean

    universe u

    structure Semigroup : Type (u+1) :=
    (carrier : Type u)
    (mul : carrier → carrier → carrier)
    (mul_assoc : ∀ a b c : carrier,
                   mul (mul a b) c = mul a (mul b c))

    instance Semigroup_has_mul (S : Semigroup) :
      has_mul (S.carrier) :=
    ⟨S.mul⟩

In other words, a semigroup consists of a type, ``carrier``, and a multiplication, ``mul``, with the property that the multiplication is associative. The ``instance`` command allows us to write ``a * b`` instead of ``Semigroup.mul S a b`` whenever we have ``a b : S.carrier``; notice that Lean can infer the argument ``S`` from the types of ``a`` and ``b``. The function ``Semigroup.carrier`` maps the class ``Semigroup`` to the sort ``Type u``:

.. code-block:: lean

    universe u

    structure Semigroup : Type (u+1) :=
    (carrier : Type u)
    (mul : carrier → carrier → carrier)
    (mul_assoc : ∀ a b c : carrier,
                   mul (mul a b) c = mul a (mul b c))

    instance Semigroup_has_mul (S : Semigroup) : has_mul (S.carrier) :=
    ⟨S.mul⟩
    -- BEGIN
    #check Semigroup.carrier
    -- END

If we declare this function to be a coercion, then whenever we have a semigroup ``S : Semigroup``, we can write ``a : S`` instead of ``a : S.carrier``:

.. code-block:: lean

    universe u

    structure Semigroup : Type (u+1) :=
    (carrier : Type u)
    (mul : carrier → carrier → carrier)
    (mul_assoc : ∀ a b c : carrier, mul (mul a b) c = mul a (mul b c))

    instance Semigroup_has_mul (S : Semigroup) : has_mul (S.carrier) :=
    ⟨S.mul⟩

    -- BEGIN
    instance Semigroup_to_sort : has_coe_to_sort Semigroup :=
    {S := Type u, coe := λ S, S.carrier}

    example (S : Semigroup) (a b c : S) :
      (a * b) * c = a * (b * c) :=
    Semigroup.mul_assoc _ a b c
    -- END

It is the coercion that makes it possible to write ``(a b c : S)``. Note that, we define an instance of ``has_coe_to_sort Semigroup`` instead of ``has_coe Semigroup Type``. The reason is that when Lean needs a coercion to sort, it only knows it needs a type, but, in general, the universe is not known. The field ``S`` in the class ``has_coe_to_sort`` is used to specify the universe we are coercing too.

By the *class of function types*, we mean the collection of Pi types ``Π z : B, C``. The third kind of coercion has the form

.. code-block:: text

    c : Π x1 : A1, ..., xn : An, y : F x1 ... xn, Π z : B, C

where ``F`` is again a family of types and ``B`` and ``C`` can depend on ``x1, ..., xn, y``. This makes it possible to write ``t s`` whenever ``t`` is an element of ``F a1 ... an``. In other words, the coercion enables us to view elements of ``F a1 ... an`` as functions. Continuing the example above, we can define the notion of a morphism between semigroups ``S1`` and ``S2``. That is, a function from the carrier of ``S1`` to the carrier of ``S2`` (note the implicit coercion) that respects the multiplication. The projection ``morphism.mor`` takes a morphism to the underlying function:

.. code-block:: lean

    universe u

    structure Semigroup : Type (u+1) :=
    (carrier : Type u)
    (mul : carrier → carrier → carrier)
    (mul_assoc : ∀ a b c : carrier, mul (mul a b) c = mul a (mul b c))

    instance Semigroup_has_mul (S : Semigroup) : has_mul (S.carrier) :=
    ⟨S.mul⟩

    -- BEGIN
    instance Semigroup_to_sort : has_coe_to_sort Semigroup :=
    {S := _, coe := λ S, S.carrier}

    structure morphism (S1 S2 : Semigroup) :=
    (mor : S1 → S2)
    (resp_mul : ∀ a b : S1, mor (a * b) = (mor a) * (mor b))

    #check @morphism.mor
    -- END

As a result, it is a prime candidate for the third type of coercion.

.. code-block:: lean

    universe u

    structure Semigroup : Type (u+1) :=
    (carrier : Type u)
    (mul : carrier → carrier → carrier)
    (mul_assoc : ∀ a b c : carrier, mul (mul a b) c = mul a (mul b c))

    instance Semigroup_has_mul (S : Semigroup) : has_mul (S.carrier) :=
    ⟨S.mul⟩


    instance Semigroup_to_sort : has_coe_to_sort Semigroup :=
    {S := _, coe := λ S, S.carrier}

    structure morphism (S1 S2 : Semigroup) :=
    (mor : S1 → S2)
    (resp_mul : ∀ a b : S1, mor (a * b) = (mor a) * (mor b))

    -- BEGIN
    instance morphism_to_fun (S1 S2 : Semigroup) :
      has_coe_to_fun (morphism S1 S2) :=
    { F   := λ _, S1 → S2,
      coe := λ m, m.mor }

    lemma resp_mul {S1 S2 : Semigroup}
        (f : morphism S1 S2) (a b : S1) :
      f (a * b) = f a * f b :=
    f.resp_mul a b

    example (S1 S2 : Semigroup) (f : morphism S1 S2) (a : S1) :
      f (a * a * a) = f a * f a * f a :=
    calc
      f (a * a * a) = f (a * a) * f a : by rw [resp_mul f]
                ... = f a * f a * f a : by rw [resp_mul f]
    -- END

With the coercion in place, we can write ``f (a * a * a)`` instead of ``morphism.mor f (a * a * a)``. When the ``morphism``, ``f``, is used where a function is expected, Lean inserts the coercion. Similar to ``has_coe_to_sort``, we have yet another class ``has_coe_to_fun`` for this class of coercions. The field ``F`` is used to specify the function type we are coercing to. This type may depend on the type we are coercing from.

Finally, ``⇑f`` and ``↥S`` are notations for ``coe_fn f`` and ``coe_sort S``. They are the coercion operators for the function and sort classes.

We can instruct Lean's pretty-printer to hide the operators ``↑`` and ``⇑`` with ``set_option``.

.. code-block:: lean

    universe u

    structure Semigroup : Type (u+1) :=
    (carrier : Type u)
    (mul : carrier → carrier → carrier)
    (mul_assoc : ∀ a b c : carrier, mul (mul a b) c = mul a (mul b c))

    instance Semigroup_has_mul (S : Semigroup) : has_mul (S.carrier) :=
    ⟨S.mul⟩

    instance Semigroup_to_sort : has_coe_to_sort Semigroup :=
    {S := _, coe := λ S, S.carrier}

    structure morphism (S1 S2 : Semigroup) :=
    (mor : S1 → S2)
    (resp_mul : ∀ a b : S1, mor (a * b) = (mor a) * (mor b))

    instance morphism_to_fun (S1 S2 : Semigroup) : has_coe_to_fun (morphism S1 S2) :=
    { F   := λ _, S1 → S2,
      coe := λ m, m.mor }

    lemma resp_mul {S1 S2 : Semigroup} (f : morphism S1 S2) (a b : S1) : f (a * b) = f a * f b :=
    f.resp_mul a b

    -- BEGIN
    theorem test (S1 S2 : Semigroup)
        (f : morphism S1 S2) (a : S1) :
      f (a * a * a) = f a * f a * f a :=
    calc
      f (a * a * a) = f (a * a) * f a : by rw [resp_mul f]
                ... = f a * f a * f a : by rw [resp_mul f]

    #check @test
    set_option pp.coercions false
    #check @test
    -- END
-->
