구조체와 레코드
======================

우리는 귀납형을 포함해 린의 기초적인 체계를 보았습니다. 게다가 우리는 유형 세계, 의존 화살표 유형, 귀납형과 이들로부터 따라나온 모든 것 외에는 기반하지 않는 수학의 엄청난 구조물을 세울 수 있는 가능성을 발견한 사실은 주목할만 합니다. 린 표준 라이브러리는 귀납형의 만은 개체(예 ``Nat``, ``Prod``, ``List``)들을 담고 있습니다. 그리고 심지어 논리 결합자도 귀납형을 사용해 정의됩니다.

한 생성자만을 포함한 비 재귀적인 귀납형은 *구조체(structure)* 혹은 *레코드(record)*라고 불린다는 것을 떠올려보세요. 곱 형은 의존적 곱 (시그마) 형과 마찬가지로 구조체입니다.
일반적으로 언제든 우리가 구조체 ``S``를 정의하면 우리는 보통 ``S``의 각 개체를 "파괴"할 수 있게 해주고 그 필드에 저장된 값을 인출할 수 있게 해주는 *투영*함수를 정의합니다. 순서쌍의 첫 번째와 두 번째 원소를 반환하는 함수 ``prod.fst``와 ``prod.snd``는 그런 투영의 예입니다.

프로그램을 작성하거나 수학을 공식화할 때 만은 필드를 포함한 구조체를 정의하는 것은 흔합니다.  린에서 사용할 수 있는 ``structure`` 명령은 이 절차를 지원하는 기반구조를 제공합니다. 우리가 이 명령을 사용해 구조체를 정의할 때, 린은 자동적으로 모든 투영함수를 생성합니다. 또 ``structure``  명령은 이전에 정의한 구조체에 기반한 새 구조체를 정의하도록 허용합니다. 게다가 린은 주어진 구조체의 개체를 정의하는데 편리한 기호를 제공합니다.

구조체 선언하기
--------------------

구조체 명령은 본질적은 유도 데이터형을 정의하기 위한 "최전선"입니다. 모든 ``structure`` 선언은 같은 이름을 가진 이름공간을 도입합니다. 일반적인 형태는 다음과 같습니다.

```
    structure <name> <parameters> <parent-structures> where
      <constructor> :: <fields>
```

대부분은 선택적입니다. 여기 예제가 있습니다.

```lean
structure Point (α : Type u) where
  mk :: (x : α) (y : α)
```

``Point``형의 값은``Point.mk a b``를 사용하여 만들어집니다. 그리고 포인트 ``p``의 필드는 ``Point.x p``와
``Point.y p``를 사용해서 접근할 수 있습니다. (그러나 g6>p.x` and `p.y`도 동작함, 아래를 참고)
또 구조체 명령은 유용한 재귀자와 정리들을 생성합니다. 여기 생성자의 몇 가지가 위의 선언에 대해서 생성되었습니다.

```lean
# structure Point (α : Type u) where
#  mk :: (x : α) (y : α)
#check Point       -- a Type
#check @Point.rec  -- the eliminator
#check @Point.mk   -- the constructor
#check @Point.x    -- a projection
#check @Point.y    -- a projection
```

만약 생성자 이름이 없다면 생성자는 기본적으로 ``mk``로 이름 붙습니다.  여러분이 각 필드 사이에 줄 바꿈 문자를 추가하면 여러분은 필드 이름 주위에 괄호를 쓰지 않을 수 있습니다.

```lean
structure Point (α : Type u) where
  x : α
  y : α
```

여기 만들어진 생성자를 사용하는 몇 가지 간단한 정리와 표현식이 있습니다. 평소처럼 여러분은 ``open Point``명령을 사용해 접두사 ``Point``를 생략할 수 있습니다.

```lean
# structure Point (α : Type u) where
#  x : α
#  y : α
#eval Point.x (Point.mk 10 20)
#eval Point.y (Point.mk 10 20)

open Point

example (a b : α) : x (mk a b) = a :=
  rfl

example (a b : α) : y (mk a b) = b :=
  rfl
```

``p : Point Nat``에 대해서 점 기호 ``p.x``은 ``Point.x p``에 대한 축약 표현입니다. 이것은 구조체의 필드에 접근하는 편리한 방법을 제공합니다.

```lean
# structure Point (α : Type u) where
#  x : α
#  y : α
def p := Point.mk 10 20

#check p.x  -- Nat
#eval p.x   -- 10
#eval p.y   -- 20
```

점 기호는 레코드의 투영에 접근하는데에만 편리한 게 아니라 같은 이름인 이름공간에 정의된 함수를 적용하는데에도 편리합니다. [결합 섹션(Conjunction section)](./propositions_and_proofs.md#conjunction)에서 ``foo``에 대한 첫 번째 비암시적인 인수가 ``Point``형을 갖는다고 가정했을 때 만약 ``p``가 ``Point``형이면 표현식 ``p.foo``는 ``Point.foo p``으로 해석됨을 기억하세요. 표현식 ``p.add q``는 그러므로 아래 예제에서 ``Point.add p q``에 대한 축약 표현입니다.

```lean
structure Point (α : Type u) where
  x : α
  y : α
  deriving Repr

def Point.add (p q : Point Nat) :=
  mk (p.x + q.x) (p.y + q.y)

def p : Point Nat := Point.mk 1 2
def q : Point Nat := Point.mk 3 4

#eval p.add q  -- {x := 4, y := 6}
```

다음 장에서 여러분은 ``add``같은 함수를 어떻게 정의하는지 배울 것입니다. 그래서 그저 ``Point Nat``보다는 ``Point α``의 원소에 대해 일반적으로 동작하도록 할 것입니다. 여기서 ``α``는 덧셈 연산과 연관이 있다고 가정합시다.

더 일반적으로 `p : Point`일 때 제시된 표현식 ``p.foo x y z``에 대해, 린은 ``Point``형의 첫 번째 인수로 ``Point.foo``에  ``p``를 삽입할 것입니다. 예를 들어 아래의 스칼라 곱의 정의에서 ``p.smul 3``은 ``Point.smul 3 p``으로 해석됩니다.

```lean
# structure Point (α : Type u) where
#  x : α
#  y : α
#  deriving Repr
def Point.smul (n : Nat) (p : Point Nat) :=
  Point.mk (n * p.x) (n * p.y)

def p : Point Nat := Point.mk 1 2

#eval p.smul 3  -- {x := 3, y := 6}
```

두 번째 비암시적인 인자로써 리스트를 받는 ``List.map`` 함수로 비슷한 트릭을 쓰는 것은 흔합니다.

```lean
#check @List.map

def xs : List Nat := [1, 2, 3]
def f : Nat → Nat := fun x => x * x

#eval xs.map f  -- [1, 4, 9]
```

Here ``xs.map f`` is interpreted as ``List.map f xs``.

대상(개체, 객체)
-------

우리는 구조체 형의 원소를 생성하는데 생성자를 사용했습니다. 많은 필드를 포함한 구조체에 대해 우리는 필드가 정의된 순서를 기억해야만 하기 때문에 이것은 종종 불편합니다. 그래서 린은 구조체의 원소를 정의하는데 다음의 대안 기호를 제공합니다

```
    { (<field-name> := <expr>)* : structure-type }
    or
    { (<field-name> := <expr>)* }
```

접미사 ``: structure-type``은 언제든지 구조체의 이름이 기대되는 유형으로부터 추론될 수 있는 한 생략될 수 있습니다. 예를 들어 우리는 "점"을 정의하기 위해 이 기호를 사용합니다. 필드가 나타난 순서는 중요하지 않습니다. 그래서 아래의 모든 표현식들은 같은 점을 정의합니다.

```lean
structure Point (α : Type u) where
  x : α
  y : α

#check { x := 10, y := 20 : Point Nat }  -- Point ℕ
#check { y := 20, x := 10 : Point _ }
#check ({ x := 10, y := 20 } : Point Nat)

example : Point Nat :=
  { y := 20, x := 10 }
```

만약 필드의 값이 명시되지 않았다면, 린은 그것을 추론하려고 할 것입니다. 만약 명시되지 않은 필드가 추론될 수 없다면 린은 대응하는 자리차지자를 합성할 수 없다고(the corresponding placeholder could not be synthesized) 나타내는 오류를 띄울 것입니다.

```lean
structure MyStruct where
    {α : Type u}
    {β : Type v}
    a : α
    b : β

#check { a := 10, b := true : MyStruct }
```

*레코드 업데이트*는 이전 필드에서 하나 이상의 필드 값을 수정하여 새 레코드 개체를 만드는 것과 같은 또 다른 흔한 연산입니다. 린은 여러분이 레코드의 명세에서 이전에 정의된 구조체 개체로부터 ``s``를 받아  필드 할당 전에 ``s가 있음`` 주석을 추가하여 할당되지 않은 필드를 나타내도록 해줍니다. 하나 이상의 레코드 개체가 제공되었다면 그럼 그들은 린이 명시되지 않은 필드를 포함하는 곳을 찾을 때까지 순서대로 방문될 것입니다. 린은 모든 개체들이 방문된 이후에도 어떤 필드 이름이라도 명시되지 않고 남아있다면 오류를 발생시킵니다.

```lean
structure Point (α : Type u) where
  x : α
  y : α
  deriving Repr

def p : Point Nat :=
  { x := 1, y := 2 }

#eval { p with y := 3 }  -- { x := 1, y := 3 }
#eval { p with x := 4 }  -- { x := 4, y := 2 }

structure Point3 (α : Type u) where
  x : α
  y : α
  z : α

def q : Point3 Nat :=
  { x := 5, y := 5, z := 5 }

def r : Point3 Nat :=
  { p, q with x := 6 }

example : r.x = 6 := rfl
example : r.y = 2 := rfl
example : r.z = 5 := rfl
```

상속(Inheritance)
-----------

우리는 새 필드를 추가하여 존재하는 구조체를*확장*할 수 있습니다. 이 기능은 우리가 *상속(inheritance)*의 형태를 모사하도록 허용합니다.

```lean
structure Point (α : Type u) where
  x : α
  y : α

inductive Color where
  | red | green | blue

structure ColorPoint (α : Type u) extends Point α where
  c : Color
```

다음 예제에서 우리는 다수의 상속을 사용한 구조체를 정의하고 그 후 부모 구조체의 대상을 사용하는 대상을 정의합니다.

```lean
structure Point (α : Type u) where
  x : α
  y : α
  z : α

structure RGBValue where
  red : Nat
  green : Nat
  blue : Nat

structure RedGreenPoint (α : Type u) extends Point α, RGBValue where
  no_blue : blue = 0

def p : Point Nat :=
  { x := 10, y := 10, z := 20 }

def rgp : RedGreenPoint Nat :=
  { p with red := 200, green := 40, blue := 0, no_blue := rfl }

example : rgp.x   = 10 := rfl
example : rgp.red = 200 := rfl
```
