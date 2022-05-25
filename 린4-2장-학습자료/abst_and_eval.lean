/-함수를 만드는 구문의 구조-/
fun (a : Nat) => a + 9 

/-함수를 만들기 위한 키워드 fun과 λ-/
#check fun (x: Nat) => x + 5 -- Nat -> Nat형의 함수
#check λ (x : Nat) => x + 5
/-인수 x를 나타나내는 괄호를 생략할 수 있음-/
#check fun x: Nat => x +5 
#check λ x:Nat => x + 5

/-#eval 명령과 함수에서 적절한 인수를 넘겨줌으로써 값을 평가할 수 있음 -/
#eval (λ x : Nat => x + 5) 10

/-어떤 표현식 x로부터 다른 표현식 t를 정의하는 함수를 만드는 과정 : 람다 추상화-/
def x : α --표현식 x가 α 형의 식임
def t : β --표현식 t가 β 형의 식임

fun (x : α) => t -- α -> β 로의 함수
λ (x : α) => t

/-함수 fun x : Nat은 fun y: Bool로 정의되어 있음
 fun y : Bool은 if then else의 형태로 정의되어 있음-/
#check fun x : Nat => fun y : Bool => if not y then x +1 else x +2

/-함수 fun (x: Nat) (y:Bool)은 if then else 형태로 정의됨-/
#check fun (x: Nat) (y:Bool) => if not y then x + 1 else x + 2

/-린이 알아서 x와 y의 유형을 추론하게 함
fun x y는 if then else로 정의되어 있음-/
#check fun x y => if not y then x + 1 else x + 2

--위 세 함수 예제는 모두 동일한 표현식으로 해석됨.

/-함수 f는 자연수 n을 받아 n을 문자열로 반환하는 함수-/
def f (n: Nat) : String := toString n

/-함수 g는 문자열 s를 받아 Bool값을 반환하는 함수-/
def g (s : String) : Bool := s.length > 0

/-린이 알아서 반환값의 유형을 결정함-/
#check fun x : Nat => x   -- Nat -> Nat으로의 함수, y = x의 항등함수
#check fun x : Nat => true --Nat -> Bool로의 함수, 항상 true를 반환하는 상수함수
#check fun x: Nat => g (f x) --Nat -> Bool로의 함수, f와 g가 합성된 함수
#check fun x => g (f x) --Nat->Bool로의 함수, 입력유형과 출력유형을 린이 알아서 판단

/-함수유형을 이름을 가진 인수 사용하는 방법-/
/-아래 함수는 String->Bool형 함수, Nat-> String형 함수, Nat을 인수로 받는 함수임-/
/-여기서 인수로 받는 함수의 이름을 g, f와 같이 두었기 때문에 함수의 정의에서
이 이름을 활용할 수 있음-/
#check fun (g: String → Bool) (f : Nat → String) (x :Nat) => g (f x)
--(String -> Bool) -> (Nat->String)-> Nat -> Bool 형의 함수가 됨

/-Type의 유형상수 α β γ를 사용해 함수를 정의할 수도 있음-/
#check fun (α β γ : Type) (g: β → γ) (f: α → β ) (x : α) => g (f x)
--(β -> γ ) -> (α -> β) -> α -> γ 
--구속변수, 함수의 정의에서 사용되는 용어
--함수의 정의에서만 사용할 수 있는 변수를 의미함

--알파 등가
--구속변수의 이름이 바뀌기 까지 같은 표현식을 나타내는 말
fun x : α => t          --변수 x는 표현식 t를 정의할 때만 사용될 수 있고, 이외에서 사용불가
fun (b : β) (x : α) => b --62번과 63번줄의 함수정의는 '알파등가'임
fun (u : β) (z : α) => u --표현이 b가 u로, x가 z로 바뀔 뿐이었기 때문임

def t : α → β --α->β형 함수
def s : α는   --α형 항 
#check t s -- β형으로 평가된다

/-함수 인수 1(Nat형)를 넘겨주면 Nat->Nat형 함수가 Nat형이 된다. -/
#check (fun x : Nat => x) 1   --Nat형으로 인식

/-함수 인수 1(Nat형)을 넘겨주자 Nat-> Bool형 함수가 Bool형이 된다.-/
#check (fun x : Nat => true) 1 -- Bool 형으로 인식

#check (fun (α β γ : Type) (u : β -> γ) (v: α -> β) (x: α) => u (v x)) Nat String Bool g f 0
--이와 같이 함수 정의에 각각의 유형상수와 함수명, 인자값을 넘겨주자 
--(β -> γ) -> (α -> β )->α ->γ 형 함수가 Bool형으로 되었다.

/-정규화의 의미는 무엇일까?-/
#eval (fun x: Nat => x) 1     --1로 표현식의 값을 평가함
#eval (fun x: Nat => true) 1  -- true로 표현식의 값을 평가함

