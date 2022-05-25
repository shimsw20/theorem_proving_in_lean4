/- 몇 가지 상수를 정의합니다. -/
def m : Nat := 1        -- 자연수 m에 1값을 할당하여 정의합니다.
def n : Nat := 0        -- 자연수 n에 0값을 할당하여 정의합니다.
def b1 : Bool := true   -- 불 타입 b1에 true값을 할당함
def b2 : Bool := false  -- 불 타입 b2에 false값을 할당함

/- 정의한 객체의 유형을 확인합니다 -/
#check m            -- Nat 형 상수
#check n            -- Nat 형 상수
#check n + 0        -- Nat 형 식
#check m * (n + 0)  -- 

#check b1         -- Bool
#check b1 && b2   -- Bool 형 식 
#check b1 || b2
#check true

/- 표현식의 값을 계산합니다. -/
#eval 5 * 4
#eval m + 2
#eval b1 && b2

