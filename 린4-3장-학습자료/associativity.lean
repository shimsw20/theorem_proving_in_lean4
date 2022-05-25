variable (p q r : Prop)

-- associativity of ∧ 
example : (p ∧ q) ∧ r ↔ p ∧ (q ∧ r) :=
  Iff.intro
    --(p ∧ q) ∧ r -> p ∧ (q ∧ r)
    (fun h : (p ∧ q) ∧ r =>
      have hr : r := h.right
      have hpq : p ∧ q := h.left
      show p ∧ (q ∧ r) from ⟨hpq.left, ⟨ hpq.right, hr⟩ ⟩ 
    )
    --p ∧ (q ∧ r) -> (p ∧ q) ∧ r
    (fun h : p ∧ (q ∧ r) =>
      have hp : p := h.left
      have hqr : q ∧ r := h.right
      show (p ∧ q) ∧ r from ⟨ ⟨ hp,  hqr.left ⟩, hqr.right ⟩  
    )

-- associativity of ∨
example : (p ∨ q) ∨ r ↔ p ∨ (q ∨ r) := 
  Iff.intro
    -- (p ∨ q) ∨ r -> p ∨ (q ∨ r)
    (
      fun h : (p ∨ q) ∨ r => 
      Or.elim h
      -- p ∨ q -> p ∨ (q ∨ r)
      (
        fun hpq : p ∨ q =>
        Or.elim hpq
        -- p -> p ∨ (q ∨ r)
        (fun hp : p => Or.inl hp)
        -- q -> p ∨ (q ∨ r)
        (fun hq : q => Or.inr (Or.inl hq) )
      )
      -- r -> p ∨ (q ∨ r)
      (fun hr : r => Or.inr (Or.inr hr) )
    )
    -- p ∨ (q ∨ r) -> (p ∨ q) ∨ r
    (
      fun h : p ∨ (q ∨ r) => 
      Or.elim h
      -- p -> (p ∨ q) ∨ r
      (fun hp : p => Or.inl (Or.inl hp) )
      -- q ∨ r -> (p ∨ q) ∨ r
      (
        fun hqr : q ∨ r => 
        Or.elim hqr
        -- q -> (p ∨ q) ∨ r
        (fun hq : q => Or.inl (Or.inr hq) )
        -- r -> (p ∨ q) ∨ r
        (fun hr : r => Or.inr hr)
      )
    )