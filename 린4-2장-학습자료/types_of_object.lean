/-유형의 유형은 무엇인가?-/
/-기본형으로부터 만들어진 유형들은 Type형을 갖는 것으로 보임-/
/-이들은 Type형들의 원소라고 생각할 수 있다-/
#check Nat          --Nat의 유형은 Type임
#check Bool         --Bool의 유형도 Type임
#check Nat → Bool   --Nat → Bool형의 유형도 Type임
#check Nat × Bool
#check Nat → Nat
#check Nat × Nat → Nat
#check Nat → Nat → Nat
#check Nat → (Nat → Nat)
#check Nat → Nat → Bool
#check (Nat → Nat) → Nat

/-어떤 유형값을 같는 유형상수를 정의할 수도 있음-/
def α : Type := Nat   --def m : Nat := 2
def β : Type := Bool  --def b1 : Bool := true

def F : Type → Type := List --Type에서 Type으로의 유형을 저장하는 유형상수
def G : Type → Type → Type := Prod --Type에서 Type에서 Type으로의 유형을 저장하는 유형상수
/-이 Type은 위에서 확인한 Nat, Bool, Nat->Bool ... 과 같은
기본형이거나 기본형으로부터 만들어진 Type 유형들이 될 수 있다-/

/-예를 들어 F는 Nat -> Nat이나,
Nat-> Bool이 되도록하거나
Nat×Nat -> Nat이 되거나
(Nat->Nat) -> Nat 등이 되도록 정의할 수 있다.-/

def H : Type → Type := Nat → Nat
#check H

def J : Type -> Type := List Nat Nat
#check J

def K : Type → Type → Type := Prod Nat Nat Bool
#check K

#check α      --Type형인 유형상수, Nat형을 값으로 가짐
#check F α    --Type->Type형인 유형상수 F에 Type형 인수 α를 전달해 Type형 유형상수가 됨.
#check F Nat  -- Type->Type형인 유형상수 F에 Type형 인수 Nat를 전달해 Type형 유형상수가 됨.
#check G α    -- Type -> Type->Type형인 유형상수 G에 Type형 인수 α를 전달해 Type->Type형 유형상수가 됨.
#check G α β  --Type -> Type->Type형인 유형상수 G에 Type형 인수 α, β를 전달해 Type형 유형상수가 됨.
#check G α Nat --Type -> Type->Type형인 유형상수 G에 Type형 인수 α, Nat를 전달해 Type형 유형상수가 됨.

/- 16, 17번 줄이
def α : Type := Nat   --def m : Nat := 2
def β : Type := Bool  --def b1 : Bool := true
임을 기억
-/

#check Prod α β --Prod는 Type -> Type -> Type으로의 함수인데 Type형 인수 α, β를 전달받아 Type형 함수가 됨.
#check α × β    --×는 Type -> Type -> Type으로의 함수인데 Type형 인수 α, β를 전달받아 Type형 함수가 됨.

/-비슷한 방식으로 α β 대신 Type형인 Nat유형으로도 위와 같이 구현 가능-/
#check Prod Nat Nat
#check Nat × Nat

#check List α   -- List는 Type->Type형인데 Type형 인수 α를 전달받아 List α는 Type형이 됨.
#check List Nat -- 마찬가지로 Type형 인수 Nat을 전달해 List Nat은 Type형이 됨.

/-Type의 유형은 무엇인가?-/
#check Type --Type 또는 Type 0은 Type 1이라는 더 넓은 유형세계에 몸을 담고 있는 유형

#check Type 1
#check Type 2
#check Type 3
#check Type 4
/-...-/

/-그리고 Type 1도 Type 2의 일부이고, Type 2도 Type 3의 일부인 방식으로 있음-/

#check List -- Type u_1 → Type u_1
/-u_1은 어떤 Type n(n은 자연수)의 한 유형-/
/-α 가 Type n의 한 유형(Type n 세계의 한 원소)일 때 
List α 는 Type n형 인수 α를 받아 Type n형이 됨-/

#check Prod -- Type u_1 -> Type u_2 -> Type (max u_1 u_2)
/-
u_1과 u_2는 같은 계층의 유형일 필요가 없음.
그러나 출력유형은 u_1과 u_2가 있는 유형세계에서 
더 큰 것을 유형세계로 채택함
가령, u_1이 Type 1의 한 유형이고, u_2가 Type 2의 한 유형이라면
Type (max u_1 u_2)는 Type 2로 해석될 것임.
-/

/-나만의 유형세계를 만들어 보자-/
/-universe 키워드를 사용해서 어떤 계층의 유형세계를 만들 수 있음-/

universe u
def F (α : Type u) : Type u := Prod α α
/-
나만의 유형세계를 만들고 나서 
Type u형 인자 α를 사용하는 함수 Prod α α를 F로 정의함
-/

#check F --Type u -> Type u

/-
universe 키워드를 명시적으로 사용하지 않고 이와 같이 
함수 F를 정의할 수도 있음
-/
def F.{u} (α : Type u) : Type u := Prod α α
#check F -- Type u -> Type u

Type = {Nat, Bool, Nat->Nat , Bool -> Bool ,,}