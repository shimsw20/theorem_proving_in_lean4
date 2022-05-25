--theorem 키워드, 린에서 새로운 정리를 만드는 데 사용됨
--def 키워드의 변종이라고 생각해도 무방

--Prop형 변수 p, q를 암시적으로 사용하도록 선언
variable {p: Prop}
variable {q: Prop}

theorem t1 : p → q → p :=
  fun hp : p => fun hq : q => hp

--def와 theorem의 미묘한 차이
--1. Proof irrelevance에 의해 정리의 두 증명은 정의상 같아서 
--  정리의 "정의(내부적 구현이 어떻게 되었는지)"는 전혀 필요없음 , 

--2. 정리의 증명이 존재한다는 것만 아는 것으로 충분 (헤더 이름)
--린은 증명에 irreducible로 태그를 붙임.

--#print명령은 theorem의 정의(구현)가 어떻게 되었는지 출력해줌

#print t1

--#show명령은 theorem 정의에서 항의 유형을 명시하는데 사용됨.

theorem t2 : p → q → p :=
  fun hp : p =>
  fun hq : q =>
  show p from hp

--def처럼 theorem도 선언 매개변수 목록을 명시적으로 나타낼 수 있음.
--: 람다 추상화된 변수를 콜론 왼쪽에 배치가능
theorem t3 (hp : p) (hq : q) : p :=
  hp

--t3의 유형은 이와 같음, p -> q -> p
#check t3

--함수 활용으로 정리 t1을 적용할 수 있음.
axiom hp : p --증명(명제) 상수 hp의 선언
theorem t4 : q → p := t3 hp 
--p->q->p형 함수 t3에 p형 객체 hp를 대입하여 q->p형 출력

--원소가 없는 유형 세계: False 
axiom unsound : False --거짓으로부터 어떤 것이든 도출 가능
theorem ex : 1 = 0 := False.elim unsound --말도 안되는 정리라고 증명한 셈,,

--암시적인 변수를 사용하여 theorem을 선언할 수 있음
theorem t5 {p q: Prop} (hp : p) (hq : q) : p := hp
#print t5 --t5는 p → q → p형

--모든이라는 키워드를 theorem 안에서 사용하는 법
--의미: 모든 명제 쌍 p, q에 대해 p->q->p이다.
theorem t6 : ∀ {p q : Prop}, p → q → p :=
  fun {p q : Prop} (hp : p) (hq : q) => hp

--또는 미리 암시적인 변수로 선언한다면, 린에서 자동으로 일반화 하여 표현해줄 것
--variable {p q : Prop}
theorem t7 : p → q → p 
  :=fun (hp : p) (hq : q) => hp

--유형으로써 명제(proposition as type) 대응에 의해 p의 증명 hp를 변수로 선언할 수 있음.

variable (hp : p)
theorem t8 : q → p := fun (hq : q) => hp
--증명은 hp를 사용함
--hp : p를 자동적으로 전제로 사용함.

--모든 명제쌍 p, q에 대해서 일반화된 정리를 다양한 명제쌍에 대해서 적용하는 법
theorem t9 (p q: Prop) (hp : p) (hq : q) : p := hp

variable (p q r s : Prop)
-- Prop형 변수 p, q, r, s를 선언

#check t9 p q 
-- t9의 인자들 hp와 hq대신에 p와 q로 대치된 정리가 출력된다.
-- p -> q -> p

#check t9 r s
-- t9의 인자들 hp와 hq대신에 r과 s로 대치된 정리가 출력된다.
-- r -> s -> r

#check t9 (r → s) (s → r)
-- t9의 인자들 hp와 hq대신 (r → s)와 (s->r)로 대치된 정리가 출력된다.
-- (r → s) -> (s → r) -> (r → s)

variable (h : r → s)
-- r -> s 형 변수 h를 선언한다.
-- h는 전제나 가정처럼 사용됨.
#check t9 (r → s) (s → r) h 
--  (r → s) -> (s → r) -> (r → s)형 함수 t8 (r → s) (s → r)에
-- h를 적용한 결과 (s → r) -> (r → s)로 출력됨.
--뭔가 헷갈리게 하는 점,, 열받는다. 
--어디까지가 유형을 결정하는 인자이고, 함수 적용인자인지 한눈에 알기가 힘들다.

--아래 첨자를 사용해서 있어보이게 정리의 선언을 작성하는 법
theorem t10 (h₁ : q → r) (h₂ : p → q) : p -> r :=
  fun h₃ : p =>
  show r from h₁ (h₂ h₃)

-- t9는 p->r형 인자 h₁과 p → q형 인자 h₂를 받아 p→r을 출력하는 함수

-- 그것의 구현은 이와같이 되어있음.
-- p형 객체 h₃를 받는 함수에 대해서 r을 출력하게 만듬
-- h₂에 h₃가 적용되면 h₂ h₃는 q형이 된다.
-- 다시 h₁에 h₂ h₃를 적용하면 r형이 된다.
-- 이것으로부터 p → r형을 출력하는 함수가 된다.

--아래첨자는 \0, \1과 같이 써서 만들 수 있음.
