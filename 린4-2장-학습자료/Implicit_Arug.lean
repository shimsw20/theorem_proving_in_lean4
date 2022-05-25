/-암시적 인자-/
/-설명을 생략한 중괄호와 @기호의 의미 설명-/

/-리스트의 구현 정의를 생각-/
universe u
def Lst (α : Type u) : Type u := List α
def Lst.cons (α : Type u) (a : α) (as : Lst α) : Lst α := List.cons a as
def Lst.nil (α : Type u) : Lst α := List.nil
def Lst.append (α : Type u) (as bs : Lst α) : Lst α := List.append as bs
#check Lst          -- Type u_1 → Type u_1
#check Lst.cons     -- (α : Type u_1) → α → Lst α → Lst α
#check Lst.nil      -- (α : Type u_1) → Lst α
#check Lst.append   -- (α : Type u_1) → Lst α → Lst α → Lst α

/-일반적인 리스트 표현으로부터 자연수를 원소로 하는 리스트 정의 생성-/
#check Lst.cons Nat 0 (Lst.nil Nat)

def as : Lst Nat := Lst.nil Nat
def bs : Lst Nat := Lst.cons Nat 5 (Lst.nil Nat)

#check Lst.append Nat as bs

/-
자연수 리스트의 각각의 원소가 자연수가 되어야 함은 명백하기 때문에 
각각 Nat으로 써준 것을 린이 결정할 수 있도록 _(밑줄문자)로 표시함
-/
#check Lst.cons _ 0 (Lst.nil _)

def as : Lst Nat := Lst.nil _
def bs : Lst Nat := Lst.cons _ 5 (Lst.nil _)

#check Lst.append _ as bs

/-
밑줄문자를 쓰는 것도 번거롭고 여전히 맥락에서 추론될 수 있는 인수인 경우
암시적인 인수라는 것을 중괄호를 사용해 명시할 수 있음.
아래에서 사용자의 리스트 정의에 α 가 암시적인 인수(디폴트 인수)임을 
함수정의 자리에 중괄호로 명시함
빠진 자리에 채워야 할 인수가 Nat이 되게끔 설정하는 역할
-/
def Lst (α : Type u) : Type u := List α

def Lst.cons {α : Type u} (a : α) (as : Lst α) : Lst α := List.cons a as
def Lst.nil {α : Type u} : Lst α := List.nil
def Lst.append {α : Type u} (as bs : Lst α) : Lst α := List.append as bs

#check Lst.cons 0 Lst.nil             --0앞에 Nat이 생략됨

def as : Lst Nat := Lst.nil
def bs : Lst Nat := Lst.cons 5 Lst.nil --Nat을 생략함

#check Lst.append as bs

/-임의 유형을 가질 수 있는 항등함수의 정의-/
universe u
def ident {α : Type u} (x : α) := x

#check ident          -- ?m -> ?m
#check ident 1         -- Nat
#check ident "Hello"  -- String
#check @ident         -- {α : Type u_1} -> α -> α
--@는 이런 암시적인 인자도 드러내게 하는 기능이 있는것으로 보임,
--암시적임을 중괄호로 표시해 출력함

section
  variable {α : Type u}
  variable (x : α)
  def ident := x --{α : Type u}와 (x : α)으로 인해 정의에서 Argument 선언을 생략할 수 있음
end

#check ident          -- {α : Type u} -> α -> α 
#check ident 4        -- Nat
#check ident "Hello"  -- String

#check List.nil
#check id

#check (Lst.nil : List Nat)
#check (id : Nat → Nat)

#check 2          --Nat
#check (2 : Nat)  --Nat
#check (2 : Int)  --Int

#check @id      --{α : Type u_1} → α → α
#check @id Nat  --Nat -> Nat
#check @id Bool --Bool → Bool

#check @id Nat 1      --Nat
#check @id Bool true  --Bool
