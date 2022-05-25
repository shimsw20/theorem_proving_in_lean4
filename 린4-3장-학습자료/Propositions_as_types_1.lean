def Implies (p q : Prop) : Prop := p → q

--4가지 논리 결합자
--이항 연산자 And, Or, Implies는 Prop -> Prop -> Prop형을 가짐
--단항 연산자 Not은 Prop → Prop형을 가짐

--And와 Or, Implies는 Prop형 인자 2개를 받아 Prop형을 출력
--Not은 Prop형 인자 1개를 받아 Prop형을 출력
--첫 글자가 대문자와 소문자의 차이
--대문자: Prop형 인자를 받아 Prop형을 출력
--소문자: Bool형 인자를 받아 Bool형을 출력
#check And
#check Or
#check Not
#check Implies

--Prop형 변수 p, q, r선언
variable (p q r: Prop)

--논리 결합자를 이용한 더 복잡한 Prop형 만들기
#check And p q                      -- p ∧ q
#check Or (And p q) r               -- (p ∧ q) ∨ r
#check Implies (And p q) (And q p)  -- (p ∧ q) → (q ∧ p)

--structure가 정확히 어떤 기능을 하는 것인지 모르지만 Proof형을 정의하는 키워드라고 생각됨.
--Proof p는 p의 증명 유형
--p는 Prop형
structure Proof (p: Prop) : Type where
  proof : p

#check Proof --Proof형은 Prop -> Type 꼴

--and_comm은 axiom의 이름이고, Prop형 인수 p, q를 받아들임
--and_comm의 증명은 (p ∧ q) -> (q ∧ p)
axiom and_comm (p q : Prop) : Proof (Implies (And p q) (And q p))

#check and_comm p q     -- Proof (Implies (And p q) (And q p))의 형태

--명제논리의 모더스 포넨스 규칙을 린4의 언어로 작성
--Implies p q와, Proof p로부터 Proof q를 도출할 수 있음.
axiom modus_ponens : (p q:Prop) → Proof (Implies p q) → Proof p → Proof q

--명제논리의 자연 유도(natural deduction)
--p의 증명을 가정으로 갖고 있고, q의 증명을 갖고있다고 할 때,
--Implies p q의 증명을 얻고 가정을 상쇄할 수 있다.
axiom implies_intro : (p q: Prop) → (Proof p → Proof q) → Proof (Implies p q)

--Proof p가 계속 반복적으로 나타남, 여기서 Proof는 증명이라는 걸 명시적으로 
--보여주기 위해서 만든 키워드이지만 실제로 p가 Prop형이라면 
--p은 그 자체로 증명형이라는 의미도 있음.
--Proposition as type 패러다임 또는 curry-Howard isomorphism이라고도 함
--ex) t:p, 여기서 t는 명제 p의 증명

--Prop형은 Sort 0; 타입 계층의 가장 최하층
--Type u형은 Sort (u+1);
--Prop형은 -> (화살표)생성자에 대해서 닫혀있음
--ex) p q가 Prop형이라면, p->q도 Prop형임

--Proposition as type 패러다임에 대해

--1. 직관주의적 논리학자, 수학자들의 관점
--"명제가 의미하는 바를 충실하게 표현한 것이구나" 라고 생각 
--증명을 의존유형론을 바탕으로 적절히 표현된 추상적인 수학 객체로 바라봄, 

--2. 직관주의자가 아닌 사람들의 관점
--Prop as Type을 "그냥 코딩 트릭이구나"라고 받아들임
--표현식 그 자체는 어떤 것도 나타내지 않지만 문제의 명제가 참인지 확인하는 게
--잘 입력되었는지 확인한다는 것 :
--"표현식 자체가 증명이다" 라고 생각

--Proof irrelevance
--(fun x => t) s 와 t[s/x]는 정의상 같다(defintionally equal)

--정말 중요한 것, p:Prop, t:p에서 항 t(증명)가 
--잘 만들어졌는지 확인(check)하고,
--적절한 유형(type)을 갖도록 만드는 것과,
--t를 만드는 것임. 

