--긴 증명을 나눠서 증명하는 방법

--방법 1. have 생성자를 사용하여 부분 증명을 만들 수 있음
--앞방향으로 증명을 만드는 방법
section
  varialbe (p q: Prop)
  example (h : p ∧ q) : q ∧ p :=
    have hp : p := h.left
    have hq : q := h.right
    show q ∧ p from And.intro hq hp
end

-- have의 기능
-- have h : p := s; t는
-- 항 (fun (h : p) => t) s를 만듬
-- 여기서 s는 명제 p의 증명
-- h:p를 가정으로 할 때 t는 원하는 결론에 해당
-- 혹은 h : p를 입력받을 때 t를 출력하는 함수
-- 또는 람다 추상화 (fun (h : p) => t)에 s를 함수 적용한 것
--으로 해석할 수 있음

--방법 2. suffices 키워드를 사용해서 부분 증명을 만들 수 있음.
-- 뒷방향으로 증명을 만드는 방법
-- "~을 보이기에 충분하다"는 의미를 가진 증명법
section
  variable (p q : Prop)
  example (h : p ∧ q) : q ∧ p :=
    have hp : p : h.left
    suffices hq : q from And.intro hq hp
    -- suffices키워드는 두 가지 목표를 만듬 
    -- hq: q라는 추가적인 가정을 써서 원래 목표 q ∧ p를 보이는 것으로부터 q를 증명하고
    -- 또 이로부터 q를 보일 수 있어야함
end

