--도입규칙과 소거규칙은 모두 직관주의적 논리에서 볼 수 있는 것
--유형으로써 명제 대응에 기반으로하는 논리 연결사의 전산적인 이해를 반영한 것

--고전 논리는 배중률(p ∨ ¬p)을 직관주의적 논리에 추가한 것
--고전 논리를 사용하려면 Classical 이름공간을 개방해야 함

open Classical

section
  variable (p : Prop)
  #check em p 
  --em은 배중률 (the law of the excluded middle)의 약자
  --p ∨ ¬p형이라고 출력함
end

--배중률의 중요한 결론 중 하나 : 이중 부정 제거 원리
--임의의 명제 p에 대해서
--p의 부정 ¬p가 참이라고 가정하여 false을 유도하고
--p가 참임을 밝히는 논리

section 
  dne {p : Prop} (h :¬¬p) : p :=
    Or.elim (em p)        -- p ∨ ¬p를 첫번째 인자로 제공
      (fun hp : p => hp)  -- p -> p
      (fun hnp : ¬p => absurd hnp h) 
      -- ¬p형 인자와 ¬¬p형 인자를 absurd에 제공
      -- ¬p -> 

-- dne로부터 em을 보이는 역과정을 증명해보기!

--고전 공리(classical axiom)은 em에 호소한 증명 패턴을 추가적으로 제공함
--byCases 키워드
--byContradiction 키워드

section
  variable (p : Prop)
  --이중부정
  example (h : ¬¬p) : p :=
    byCases
      (fun h1 : p => h1)
      (fun h1 : ¬p => absurd h1 h)

  --귀류법
  example (h : ¬¬p) : p :=
    byContradiction
      (fun h1 : ¬p =>
      show False from h h1)
end

-- ¬(p ∧ q) -> ¬p ∨ ¬q의 증명 예제
-- p와 q가 모두 참이 아니라는 것
-- 어떤 것이 거짓이라는 것을 말해줄 필요가 없다는 의미
-
section
  variable (p q: Prop)
  example (h : ¬(p ∧ q)) : ¬p ∨ ¬q :=
    Or.elim (em p) -- p ∨ ¬p
    (fun hp : p =>  Or.inr (show ¬q from fun hq : q => h ⟨ hp, hq ⟩) )
    -- p -> ¬q  ∨ (q -> ¬(p ∧ q))
    (fun hp : ¬p => Or.inl hp)
    -- ¬p -> (q ∨ p)
end

