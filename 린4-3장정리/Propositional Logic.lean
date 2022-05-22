--명제 논리
--린은 논리 결합자와 기호를 정의함.

--참, 거짓, 부정, 논리곱, 논리합, 이면, 이면이
--True, False, Not, /\, \/, ->, <->
-- ¬, ∧, ∨, → , ↔  

--모두 Prop형 인자를 받는 연산자들임
section
  variable (p q : Prop)
  #check p → q → p ∧ q    --Prop형
  #check ¬p → p ↔ False     --Prop형
  #check p ∨ q → q ∨ p    --Prop형
end

--연산자 우선순위 : 단항부정 -> 논리곱, 논리합 -> 이면 -> 이면이
-- a ∧ b → c ∨ d ∧ e의 의미를 괄호로 명확히 나타내보자

--각각의 연산자들마다 도입과 소거(제거) 규칙이 있음
section
  variable (p q r: Prop)
  #check p → q → r 
  #check p ∧ q → r --curried form
end

-- conjunction : 결합자, And 연산에 대해서 사용되는 용어
-- And 도입 규칙
-- And.intro h1 h2, 증명 h1 : p와 h2: q로부터 p ∧ q의 증명을 생성
-- 어떤 명제 p, q의 증명이 hp, hq라고 할 때 p ∧ q도 참이다.
-- And.intro의 유형 p → q → p ∧ q  
section
  variable (p q : Prop)
  example (hp : p) (hq : q) : p ∧ q 
    := And.intro hp hq
    --인자 hp와 hq를 받아서 p ∧ q를 출력하는 함수
    --증명은 And.intro hp hq를 이용해서 hp ∧ hq의 증명을 만들어 출력

  #check fun (hp : p) (hq : q) => And.intro hp hq -- p → q → p ∧ q를 유형으로 출력함
  --example키워드는 이름이 없는 theorem을 만들 대 사용하는 키워드
  --다른 정리을 만들 때 example로 정의한 것은 다시 재활용할 수 없음
end


-- And 제거 규칙
-- ∧ 결합자로 연결된 표현식에서 왼쪽의 항, 오른쪽의 항의 증명을 만드는 법
-- h : p ∧ q
-- And.left h   ; p의 증명을 가져옴
-- And.right h  ; q의 증명을 가져옴

-- 명제논리적인 해석
-- 어떤 명제 p ∧ q의 증명을 h라고 한다면
-- h가 참이려면 p와 q가 모두 참이어야 하기 때문에 p가 참이라는 결론을 얻을 수 있음
-- h가 참이려면 p와 q가 모두 참이어야 하기 때문에 q가 참이라는 결론을 얻을 수 있음

-- 유형론적인 해석
-- And.left의 유형은 p ∧ q -> p , p ∧ q형인 h를 적용하면 p를 얻음
-- And.right의 유형은 p ∧ q -> q , p ∧ q형인 h를 적용하면 q를 얻음
section
  variable (p q : Prop)
  example (h : p ∧ q) : p 
    := And.left h
  -- p∧q형 인자 h를 받아서 p를 출력하는 함수

  example (h : p ∧ q) : q 
    := And.right h
  --p∧q형 인자 h를 받아서 q를 출력하는 함수
end

--And 도입 규칙, 제거 규칙을 사용해서 복합논리식의 증명 만들기 예
--ex)  p ∧ q -> q ∧ p
section
  --1단계: Prop형 변수 p, q를 선언한다.
  --2단게: 유형으로써 명제로부터 p, q는 증명 유형으로 해석됨을 착안
  --    p ∧ q형을 받아 q ∧ p형을 출력하는 함수를 선언한다.
  --3 단계: And도입규칙과 제거규칙을 사용해 함수를 정의를 구현한다.

  variable (p q :Prop)
  example (h : p ∧ q) : q ∧ p := 
    And.intro (And.right h) (And.left h)
    -- h에서 q를 뽑고, h에서 p를 뽑아서 And로 결합시킴
end

--structure의 단일 정식 생성자 (single canonical constructor)가 있는 경우
--And.intro와 같이 쓰는 대신에 각괄호 ⟨ , ⟩ 을 사용해서 증명을 생성할 수 있음.
section
  variable (p q: Prop)
  variable (hp : p) (hq : q)
  #check (⟨hp, hq⟩ : p ∧ q) --⟨hp, hq⟩은 p ∧ q형 증명
end

--유도형 Foo형의 표현식 e에 대해서 e.bar와 같은 기호 => Foo.bar e와 같이 짧은 표현을 사용가능
--이름공간을 열지 않고서 함수에 접근하는 편리한 방법
section
  variable (xs : List Nat)  -- List Nat형 객체 xs선언
  #check List.length xs     -- xs의 길이를 알고자 List.lenght 함수 풀네임을 사용
  #check xs.length          -- 대신에 xs의 길이 멤버 length에 접근
end

--66~69번 줄의 코드를 아래와 같이 
--각괄호 생성자와 멤버 연산자를 통해서 간략히 쓸 수 있음.
section
  variable (p q : Prop)
  example (h : p ∧ q) : q ∧ p :=
    ⟨h.right, h.left>
end

--비슷한 방식으로 p ∧ q → q ∧ p ∧ q 함수의 정의를 작성해보자.
section 
  variable (p q : Prop)
  example (h : p ∧ q) : q ∧ p ∧ q :=
    ⟨h.right, ⟨ h.left, h.right⟩ ⟩ --명시적으로 And.intro를 사용해 생성

  example (h : p ∧ q) : q ∧ p ∧ q := 
    ⟨h.right, h.left, h.right⟩ -- flatten 기능, 자동적으로 오른쪽 먼저 And.intro로 자동 생성
  
  --100번과 103번은 모두 동일한 코드
end
--각괄호 생성자는 중첩해서 사용할 수도 있고, 
--여러개의 인자를 사용하는 경우 자동적으로 오른쪽 먼저 생성됨 (flatten 기능)
-- => 심성우: 개인적으로 flatten 기능은 비 직관적이고 가독성을 떨어뜨리므로 왠만하면 쓰지 맙시다.



--Disjuction ; 분리자, Or연산에 대해서 사용되는 용어
--Or 연산에서는 왼쪽과 오른쪽 or도입 규칙이 있음

--Or 왼쪽, 오른쪽 도입규칙
section
  variable (p q :Prop)

--Or 왼쪽 도입규칙: 
  example (hp : p) : p ∨ q 
    :=Or.intro_left q hp 
    --명제 p의 증명 hp로부터 p ∨ q의 증명을 생성 
    --Or.intro_left의 첫 인자 q의 외쪽에 hp를 배치하라로 생각

--Or 오른쪽 도입규칙:
  example (hq : q) : p ∨ q
    := Or.intro_right p hq 
  --명제 q의 증명 hq로부터 p ∨ q의 증명을 생성
  --Or.intro_right의 첫 인자 p의 오른쪽에 hq를 배치하라로 생각
end

--Or 제거규칙
-- p ∨ q → r을 증명하는 방법
-- 1. p → r을 증명한다.
-- 2. q → r을 증명한다.
-- Or 제거규칙은 이처럼 경우에 따라 증명하는 방식(Proof by cases)을 사용함.

-- 그래서 Or.elim은 첫 인자로 p ∨ q를 받고
-- 두번째 인자로 p → r
-- 세번째 인자로 q → r
-- 총 3개를 인수로 받아서 r의 증명을 출력한다.

-- ex) p ∨ q → q ∨ p를 의미하는 함수를 정의해보자
section
  variable (p q r : Prop)
  example (h : p ∨ q) : q ∨ p := -- 함수의 유형이 p ∨ q -> q ∨ p가 되게 선언
    Or.elim h -- p ∨ q를 처음 인자로 제공
    (fun hp : p => 
      show q ∨ p from Or.intro_right q hp) --두번째 인자로 p -> q ∨ p 제공
    (fun hq : q => 
      show q ∨ p from Or.intro_left p hq) --세번째 인자로 q -> q ∨ p 제공
    --이것으로부터 p ∨ q → q ∨ p 형의 함수 정의 완료
end

--And.left, And.right을 h :p ∧ q를 이용해서 h.left, h.right로 쓸 수 있던 것처럼
--Or.intro_left, Or.intro_right를 Or.inl, Or.inr로 간략히 쓸 수 있음.
--이것을 이용해서 158~163의 증명을 더욱 간결하게 쓸 수 있음.
section
  variable (p q r: Prop)
  example (h : p ∨ q) : q ∨ p :=
    Or.elim h
    (fun hp => Or.inr hp) 
    (fun hq => Or.inl hq)
  --개인적으로 Or.intro_left와 Or.intro_right가 간결한 버전보다 
  --가독성에서 더 뛰어나다는 생각임.
end

--부정과 거짓
--부정의 정의: ¬p ↔ p → False
--p에서 모순을 유도하여 ¬p를 얻을 수 있음.

-- hp: p
-- hnp: ¬p --
-- hnp hp  
-- 이것은 p형 인자 hp를 hnp에 적용하여 ¬p형이 된다.
-- 
-- 이로부터 False의 증명을 만든다.

-- ex) (p → q) → (¬q → ¬p)를 증명해보자. 
section
  variable (p q : Prop)
  -- p->q와 ¬q를 인자로 받고 ¬p를 출력하는 함수를 선언한다.
  example (hpq : p → q) (hnq : ¬q) : ¬p :=
    fun hp : p =>
    show False from hnq (hpq hp)
    --hpq에 hp를 적용하면 q형을 출력하는 함수가 됨.
    --여기에 다시 hnq를 적용하면 ¬q형을 출력함.
    -- ¬q의 정의에 따라 hp → False가 나오므로 함수가 완성된다!
end

-- False는 한개의 제거규칙만을 가짐: False.elim
-- False.elim은 모순으로부터 어떤 것이든 나올 수 있다는 사실을 표현
-- False.elim은 exfalso(원래 라틴어, 영어로는 폭발의 원리)라고 하기도 함.
section
  variable (tp q : Prop)
  example (hp : p) (hnp :¬p) : q :=
    False.elim (hnp hp)
  --위 함수의 유형은 (p → ¬p) → q
  --hnp에 hp를 적용해서 ¬p유형이 되는데 
  --여기에 False.elim은 ¬p를 p->False로 바꿔준다.

  example (hp: p) (hnp : ¬p) : q :=
    absurd hp hnp
    -- False.elim은 absurd(뜻: 불합리적인) 키워드를 사용해 나타낼 수 있다.
end

--ex) ¬p → q → (q → p) → r 형 함수 만들기.
section
  variable (p q r: Prop)
  example (hnp : ¬p) (hq : q) (hqp : q → p) : r := 
    --이와같이 함수 선언를 해준다.
    absurd (hnp hq) hnp
    --hqp hq : hqp에 hq를 적용한 것 p형 인자를 absurd의 첫 인수로 전달,
    --hnp : ¬p형을 absurd의 두번째 인자로 전달

    --absurd가 False.elim의 다른 이름이므로
end

-- False는 제거 규칙 False.elim만 가진 것처럼
-- True는 도입 규칙 True.intro만 가지고 있음. 
-- True.intro는 true형을 가짐
-- True를 항진명제로 생각해도 괜찮을 것으로 보임. 정식 증명으로 True.intro를 가짐


--논리적 등가 (Logical equivalence)
--Iff의 도입 규칙 : Iff.intro

--Iff.intro h1 h2의 기능
--p q : Prop
--h1 : p → q (왼쪽 부분)
--h2 : q → p (오른쪽 부분)
--에 대해서 p ↔ q의 증명을 만든다

--Iff.intro의 원리
--p q : Prop --명제 p q에 대해서
--p->q이고 q->p이면 p<->q이기 때문에
--p <-> q의 증명을 만들 수 있는 것임


--Iff의 왼쪽 소거 규칙 : Iff.mp h
-- h : p ↔ q
-- Iff.mp h ; p → q의 증명을 생성

--Iff.mp h의 원리
-- p q: Prop
-- p <-> q이면 p->q이기 때문에
-- p -> q의 증명을 만들 수 있음


--Iff의 오른쪽 소거 규칙 : Iff.mpr h
-- h : p ↔ q
-- Iff.mpr h ; q → p의 증명을 생성

--Iff.mpr h의 원리
-- p q: Prop
-- p <-> q이면 q ->p이기 때문에
-- q -> p의 증명을 만들 수 있음

--ex) p ∧ q ↔ q ∧ p 꼴의 정리(함수) 만들기1!
section
  variable (p q r s: Prop)
  theorem and_swap : p ∧ q ↔ q ∧ p :=
    Iff.intro
      (fun h : p ∧ q => 
      show q ∧ p from And.intro (And.right h) (And.left h))
      -- p ∧ q → q ∧ p의 증명을 첫째 인수로 제공
      --And.intro에서 h의 p, q를 q ∧ p로 결합
      (fun h : q ∧ p => 
      show p ∧ q from And.intro (And.right h) (And.left h))
      -- q ∧ p → p ∧ q의 증명을 둘째 인수로 제공
      --And.intro로 h의 p, q를 p ∧ q로 결합

  #check and_swap r s --임의의 명제 r, s를 제공해서 r ∧ s ↔ s ∧ r
  
  variable (h : p ∧ q)
  example : q ∧ p := Iff.mp (and_swap p q) h
  -- and_swap p q : p ∧ q ↔ q ∧ p
  -- h : p ∧ q
  -- Iff.mp (and_swap p q) : p ∧ q → q ∧ p
  -- Iff.mp (and_swap p q) h: Iff.mp (and_swap p q)에 h를 적용한 것, q ∧ p유형이 됨.

end

-- Iff.intro의 각괄호 생성자, Iff의 멤버연산자,
-- And.intro의 각괄호 생성자와 And.left, And.right 멤버연산자를
-- 사용하여 간결하게 정의한 버전
--ex) p ∧ q ↔ q ∧ p 꼴의 정리(함수) 만들기2!
section
  variable (p q : Prop)
  theorem and_swap : p ∧ q ↔ q ∧ p :=
    -- 첫 각괄호는 <->에 대응한 생성자, 
    -- 첫번째 인자는 p ∧ q -> q ∧ p꼴에 대응, 
    --두번째 인자는 q ∧ p -> p ∧ q꼴에 대응
    --fun에 시용된 각괄호는 and에 대응한 생성자, 
    --첫번쨰 fun은 h : p ∧ q형, 두번째 fun은 h: q ∧ p로 자동 추론
    ⟨ fun h => ⟨h.right, h.left⟩ , 
    fun h => ⟨h.right, h.left⟩ ⟩ 

  example (h : p ∧ q) : q ∧ p :=
    (and_swap p q).mp h
    --(and_swap p q)은 p ∧ q ↔ q ∧ p형이기 때문에
    -- .mp, .mpr을 사용할 수 있음

    --(and_swap p q).mp h는 (and_swap p q).mp에 h를 적용한 형태
    --최종 유형은 q ∧ p로 나옴

  end
  