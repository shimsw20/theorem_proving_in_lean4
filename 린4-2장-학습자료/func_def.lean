/-앞서서 def키워드를 이용해 상수와 유형상수를 정의하는 법을 배웠음-/
/-def를 이용해 이름을 가진 함수, 상수, 유형상수를 정의하는 방법을 배워보겠음-/

/-이러한 형식을 가지고 이름을 가진 함수를 정의할 수 있음-/
def name (Arug1, Arug2,... : Bool) 
(Argu1, ... : Nat) 
: return Type 
:= expressions
/-expressions의 형은 return Type의 형과 일치-/


/-Nat형 인수 x를 받아 2*x를 출력하는 함수 double-/
def double1 (x: Nat) : Nat := x + x

/-double1 3의 식의 값은 6으로 평가된다-/
#eval double1 3 --

/-fun키워드를 이용해서 이런식으로 정의도 가능-/
def double2 : Nat->Nat := 
  fun x => x + x

#eval double2 3 -- 마찬가지로 6으로 평가됩니다.

/-린은 유형을 자동적으로 추론할 수 있습니다.-/
def double3 :=
  fun (x : Nat) => x + x 
--Nat-> Nat으로의 함수로 인식

def pi := 3.141592654 --pi로 이름지은 상수 3.14...
def add1 (x y : Nat) := x + y --Nat형 인수 x y를 받는 함수 add

#eval add1 3 2 -- 표현식의 값은 5로 평가된다.

def add2 (x : Nat) (y : Nat) := x + y --add1과 달리 인수 x, y를 다른 괄호로 나눠씀

#eval add1 (double1 3) (7 + 9) 
-- double 3이 먼저 평가되고, 7+9가 평가된 다음 add가 평가된다.
-- 이때 표현식의 값은 22가 된다.

/-def를 활용한 좀 더 복잡한 식의 정의-/
def greater (x y : Nat) :=
  if x > y then x
  else y

/-
Nat->Nat형 함수와 Nat형 인수를 받는 함수 doTwice
-/
def doTwice (f: Nat → Nat) (x: Nat) : Nat :=
  f (f x)

--double과 2를 doTwice의 인수로 받아 값을 평가한다.
#eval doTwice double 2 -- double (double 2)와 같은 의미가 있다.

def compose (α β γ : Type) (g : β ->γ ) (f: α -> β) (x: α) : γ 
:= g (f x)
--이 식에서 g와 f로 넘겨주는 함수는 β가 동일한 어떤 함수
--이것이 다르다면 합성이 불가능함
--g, f가 동작하는 유형은 임의의 유형이기 때문에 매우 일반적임

def square (x: Nat): Nat := x*x
#eval compose Nat Nat Nat double square 3 --18

def F (x : Nat) :=
 let y:= x^2; y^5
def g (s : Nat) : String := toString s 
def h (m : String) : Nat := m.length
def compose (α β γ ℘ : Type) 
    (g : β → γ ) (f : α → β ) (h : γ →℘) 
       (x : α) : ℘ := h ( g (f x))
def compose1 (α β γ ℘ : Type) 
    (f : α→β ) (g : β → γ ) (h : γ →℘) 
       (x : α)  : ℘ := h ( g (f x))
#check compose Nat String Nat Nat h g F
#eval compose Nat String Nat Nat h g F 10^1

#check compose1 Nat Nat String Nat F g h 
#eval compose1 Nat Nat String Nat F g h 2 