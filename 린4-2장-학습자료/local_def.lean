/-지역정의-/
/-let 키워드를 사용해 지역정의를 만드는 방법-/
/-C언어의 #define 매크로와 매우 비슷한 기능-/

#check let y := 2 + 2; y*y
--여기서 y의 값은 4(Nat)이므로 y*y는 Nat형이다.
--y는 지역적으로 정의된 변수이다.

#eval let y:= 2+2 ; y*y
--y*y의 값은 16으로 평가된다.

def twice_double (x: Nat) : Nat :=
  let y := x + x --twice_double 함수의 정의에서 y를 지역적으로 정의
  y * y

#eval twice_double 2 --(x+x)*(x+x)와 같아 16으로 평가됨

#check let y:= 2+2; let z:=y+y; z*z -- Nat 형
#eval let y:= 2+2; let z:=y+y; z*z -- ((2+2)+(2+2))*((2+2)+(2+2))

def t (x: Nat) : Nat:=
  let y := x + x
  y * y

  /-let y := x + x; y*y-/
-- ';'은 줄을 분리하는데 사용되는 기호

/-foo의 정의
a는 Nat타입을 같은 유형상수로 결정
fun은 Nat->Nat으로 린이 추론하여 정의됨-/
def foo := 
  let a := Nat
  fun x : a => x + 2

/-잘못된 bar의 정의
a를 마찬가지로 Nat으로 여길 것으로 보지만
a는 사전에 유형이 정의되어 있지 않아 
bar의 유형을 린이 결정하지 못해 에러가 발생함
x+2
-/
def bar :=
  (fun a => fun x : a => x + 2 ) Nat

/-변수와 섹션-/
def compose (α β γ : Type) (g: β → γ ) (f: α → β) (x: α) : γ := g (f x)
def doTwice (α : Type) (h: α -> α ) (x: α) : α := h (h x)
def doThrice (α : Type) (h: α -> α) (x: α) : α := h (h (h x))

variable (α β γ : Type)
--variable 키워드를 사용해서 초반부에 (α β γ :Type)와 같은 것을 생략할 수 있게 함

def compose1 (g: β -> γ) (f: α -> β) (x: α) : γ := g(f x)
def doTwice1 (h: α -> α) (x: α ): α := h(h x)
def doThrice1 (h: α -> α) (x: α): α := h (h (h x))

variable (g: β -> γ) (f: α -> β) (h: α -> α)
variable (x: α)
/-이와 같이 복합적인 유형도 variable로 선언할 수 있음-/

def compose2 := g (f x)
def doTwice2 := h (h x)
def doThrice2 := h (h (h x))

/-#print 명령으로 이들의 정의를 출력하여 보면
세 정의 그룹이 모두 동일한 것임을 확인할 수 있습니다.

variable 키워드는 이것으로 선언된 변수를 참조하여 
정의하는 함수에 대해 이들이 구속변수라고 지시하는 기능을 가짐

이와 같이 선언된 변수는 파일 범위를 가짐
-/

/-선언한 변수가 파일 내에서 충돌하는 것을 방지하기 위해 
 section sec_name - end sec_name
과 같이 쓸 수 있음.
이 안에서 선언된 변수나 함수들은 section의 범위를 가짐
섹션은 특별히 이름이 필요하지도 들여쓰기도 할 필요가 없음
그러나 이름을 사용하면 같은 이름으로 닫아주어야 함
섹션안에 섹션을 중첩시킬 수도 있음
-/
section useful
  def compose := g (f x)
  def doTwice := h (h x)
  def doThrice := h (h (h x))
  section 

  end
end useful

/-프로젝트 범위의 작업을 할 때 다른 팀원과의 이름 충돌을 방지
하기 위해 이름공간으로 변수의 범위를 제한할 수 있음-/

/-이름공간에는 이름을 명시적으로 정해주어야함
이름공간 내의 객체에 접근하기 위해서 Foo.의 접두사를 객체 앞에 붙여주어야 함
이름공간 안에서는 접두사를 생략할 수 있지만 밖에서는 사용해야 함
open명령을 통해서 이름공간의 객체에 접근할 수 있음.
이름공간 안에 이름공간을 중첩시킬 수 있음
닫힌 이름공간은 다른 파일에서도 열릴 수 있음
-/
namespace Foo
  def a : Nat := 5
  def f( x: Nat) : Nat := x + 7

  def fa : Nat := f a
  def ffa : Nat := f (f a)

  #check a
  #check f
  #check fa
  #check ffa 
  #check Foo.fa
end Foo

#check Foo.a
#check Foo.f
#check Foo.fa

open Foo --Foo이름공간을 개방함, Foo.접두사를 생략할 수 있음
#check a
#check f
#check fa

-- List는 이름공간의 이름, 리스트와 관련된 정의와 정리가 있음
#check List.nil
#check List.cons
#check List.map

open List
#check nil
#check cons
#check map

namespace Bar
  def a : Nat := 6
  def f (x : Nat) : Nat := x + 7

  def fa : Nat := f a
end Bar

#check Bar.a
#check Bar.f

/-이와같이 닫은 이름공간에 객체를 더 추가할 수도 있음-/
namespace Bar
  def ffa : Nat := f (f a)
end Bar