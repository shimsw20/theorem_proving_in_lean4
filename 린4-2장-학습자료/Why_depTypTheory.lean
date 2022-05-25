/-무엇이 의존 유형론을 의존적이게 만드는가?-/

/-간단한 함수들은 입력 인자들의 유형이 무엇이고, 
출력 유형이 무엇이라고 결정되어있는게 대부분
그런데 린에서는 유형조차도 Type과 같은 유형세계의 원소로 
바라보기 때문에 유형변수를 생각해 볼 수 있다.

이런 유형변수가 구체적으로 Nat인지 Bool인지에 상관없이 
각각에 대해 동일한 기능을 하는 함수 cons를 생각해 보자.

List.cons는 어떤 유형의 원소와 리스트를 받아서, 
리스트의 머리에 원소를 삽입하는 기능을 갖고 있다.
그런데 원소의 유형이 Nat형이든지 Bool형 원소이든지
이 함수는 리스트의 머리에 원소를 삽입해야 한다.(다형적)
그렇기에 임의의 유형을 원소로 받을 수 있도록 설계하는 것이 타당하다

이 임의의 유형에 따라 함수의 유형이 결정된다.
그래서 이 함수가 의존적 함수 유형이라고 불리게 되는 것
-/

def cons (α : Type) (a : α) (as : List α) : List α := List.cons a as

/-직접 정의한 cons함수의 유형-/
#check cons Nat   --Nat -> List Nat -> List Nat
#check cons Bool  --Bool -> List Bool -> List Bool
#check cons       --(α : Type) -> α -> List α -> List α

/-라이브러리의 List 멤버 함수의 유형-/
#check @List.cons   -- {α : Type u_1} -> α -> List α → List α
#check @List.nil    -- {α : Type u_1} -> List α 
#check @List.length -- {α : Type u_1} → List α → Nat
#check @List.append -- {α : Type u_1} → List α -> List α -> List α

/-의존적 카테시안 곱, 시그마 유형-/
universe u v
def f (α : Type u) (β : α → Type v) (a : α) (b : β a) : (a : α) × β a := ⟨a, b⟩
-- β가 a의 유형에 의존하는 카테시안 곱

def g (α : Type u) (β : α → Type v) (a : α) (b : β a) : Σ a : α , β a :=
  Sigma.mk a b
--37번 정의와 동일한 의미를 가지는 식 , 각괄호를 Sigma.mk로 대치할 수 있는것으로 보임.

def h1 (x: Nat) : Nat := 
  (f Type (fun α => α) Nat x).2
  --37번 줄의 의존적 카테시안 곱 함수 f에서 두번째 원소를 가져오는 함수이다.
  --Type은 α에 대응되고, (fun α => α)는 β에 대응, a는 Nat, b는 Nat->Nat에 Nat을 적용한 x이다.

def h2 (x: Nat) : Nat :=
  (g Type (fun α => α) Nat x).2
  --40번 줄의 의존적 카테시안 곱 함수 g의 순서쌍에서 2번째 원소를 가져오는 함수.
  --47번과 같은 방식으로 동작한다.

#eval h1 5 -- 5
#eval h2 5 -- 5