-- other properties
example : (p → (q → r)) ↔ (p ∧ q → r) := 
  Iff.intro
  --(p → (q → r)) -> (p ∧ q → r) 
  (fun (h : p → (q → r)) (hpq : p ∧ q) => 
    show r from h hpq.left hpq.right
  )
  --(p ∧ q → r) -> (p → (q → r))
  (fun (h : p ∧ q → r) (hp : p) (hq : q) =>
    show r from h ⟨hp, hq⟩ 
  )

example : ((p ∨ q) → r) ↔ (p → r) ∧ (q → r) :=
  Iff.intro
  -- ((p ∨ q) → r) -> (p → r) ∧ (q → r)
  (
    fun (h : p ∨ q → r) => show (p → r) ∧ (q → r) 
      from ⟨ (fun hp : p => h (Or.inl hp) ), (fun hq : q => h (Or.inr hq) )⟩
  )
  -- (p → r) ∧ (q → r) -> ((p ∨ q) → r)
  (
    fun (h : (p → r) ∧ (q → r)) (hpq : p ∨ q) => 
      show r from Or.elim hpq h.left h.right 
  )

--본질적으로 13-25번 줄의 증명에서 r대신 False로 바뀐 것과 동일
example : ¬(p ∨ q) ↔ ¬p ∧ ¬q := 
  Iff.intro
  -- ¬(p ∨ q) -> ¬p ∧ ¬q => (p∨q->False)->(p->False) ∧ (q->False)
  (
    fun (h : ¬(p ∨ q)) =>
     ⟨ (fun hp : p => h (Or.inl hp) ), 
      (fun hq : q => h (Or.inr hq) ) ⟩ 
  )
  -- ¬p ∧ ¬q -> ¬(p ∨ q) => (p->False) ∧ (q->False) -> (p∨q->False)
  (
    fun (h : ¬p ∧ ¬q) (hpq : p ∨ q) => 
      show False from 
        Or.elim hpq -- p ∨ q -> False
        h.left      -- p -> False
        h.right     -- q -> False
  )

example : ¬p ∨ ¬q → ¬(p ∧ q) :=
  fun (h  :¬p ∨ ¬q) (hpq : p ∧ q) => 
    Or.elim h
    (fun hnp : ¬p => hnp hpq.left)
    (fun hnq : ¬q => hnq hpq.right)

example : ¬(p ∧ ¬p) := 
  fun (h : p ∧ ¬p) => absurd h.left h.right

example : p ∧ ¬q → ¬(p → q) := 
  fun (h : p ∧ ¬q) => 
    fun (hpq : p → q) => absurd (hpq h.left) h.right
  
example : ¬p → (p → q) := 
  fun (hnp : ¬p) (hp : p) => absurd hp hnp

example : (¬p ∨ q) → (p → q) := 
  fun (h : ¬p ∨ q) (hp : p) => 
    Or.elim h -- ¬p ∨ q
    -- ¬p -> (p -> q)
    (fun hnp : ¬p 
      => absurd hp hnp)
    -- q -> (p -> q)
    (fun hq : q => hq)              
  

example : p ∨ False ↔ p := 
  Iff.intro
  (
    fun h : p ∨ False => 
    show p from 
      Or.elim h         --p ∨ False
      (fun hp : p => hp) --p -> p 
      False.elim      -- False -> p
  ) 
  (
    fun hp : p => 
    show p ∨ False from Or.inl hp -- p -> p ∨ False
  ) 

example : p ∧ False ↔ False := 
  Iff.intro
  (fun h : p ∧ False => h.right)
  False.elim

example : (p → q) → (¬q → ¬p) := 
  (
    fun (hpq : p → q) (hnq : ¬q) (hp : p) => 
      show False from hnq (hpq hp)
  )
