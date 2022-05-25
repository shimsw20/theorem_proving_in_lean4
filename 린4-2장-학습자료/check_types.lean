#check Nat → Nat  --자연수형에서 자연수형으로의 유형입니다.
#check Nat -> Nat --1번 줄의 아스키표현 \to, \r로 표시가능

#check Nat × Nat    -- 자연수형 × 자연수형 유형
#check Prod Nat Nat -- ×와 같은 의미의 Prod 함수

#check Nat → Nat → Nat -- 자연수에서 자연수에서 자연수로의 유형
#check Nat → (Nat → Nat) -- → 는 오른쪽 결합성을 가집니다

#check Nat × Nat → Nat -- 카테시안 곱에서 자연수로의 유형
#check (Nat → Nat) → Nat --하워드-커리 동형 isomorphism, 범함수

/-자연수를 받으면 그 다음 자연수를 출력하는 함수 -/
#check Nat.succ --자연수형의 succ 멤버함수, Nat -> Nat유형

#check (0, 1)   --Nat×Nat형, Nat형 카테시안 곱

/-자연수와 자연수를 받으면 자연수를 출력하는 함수 -/
#check Nat.add  --자연수형의 add 멤버함수, Nat -> Nat -> Nat 유형

/-인수를 전부 받아도 되고, 일부만 받아도 됨-/
#eval Nat.succ 2  --Nat형, 3을 출력함
#eval Nat.add 5 2 --Nat형, 7을 출력함

/-(m, n)꼴은 카테시안 곱임 '.' 멤버연산자를 이용해 순서쌍의 값을 추출(참조)할 수 있음-/
#eval (5, 9).1    --Nat형, 5를 출력함
#eval (5, 9).2    --Nat형, 9를 출력함