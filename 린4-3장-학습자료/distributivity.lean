-- distributivity 1
example : p ∧ (q ∨ r) ↔ (p ∧ q) ∨ (p ∧ r) := 
  Iff.intro
    (-- p ∧ (q ∨ r) -> (p ∧ q) ∨ (p ∧ r)
      fun h : p ∧ (q ∨ r) =>
      have hp : p := h.left
      -- q ∨ r -> (p ∧ q) ∨ (p ∧ r)
      Or.elim 
        h.right
        (fun hq : q => Or.inl ⟨h.left, hq⟩) -- q -> (p ∧ q) ∨ (p ∧ r)
        (fun hr : r => Or.inr ⟨h.left, hr⟩) -- r -> (p ∧ q) ∨ (p ∧ r)
    )
    (-- (p ∧ q) ∨ (p ∧ r) -> p ∧ (q ∨ r)
      fun h : (p ∧ q) ∨ (p ∧ r) =>
      Or.elim
        h
        (fun hpq : p ∧ q => ⟨hpq.left, Or.inl hpq.right⟩) -- (p ∧ q) -> p ∧ (q ∨ r)
        (fun hpr : p ∧ r => ⟨hpr.left, Or.inr hpr.right⟩) -- (p ∧ r) -> p ∧ (q ∨ r)
    )

-- distributivity 2
example : p ∨ (q ∧ r) ↔ (p ∨ q) ∧ (p ∨ r) :=
  Iff.intro
    (-- p ∨ (q ∧ r) -> (p ∨ q) ∧ (p ∨ r)
      fun h : p ∨ (q ∧ r) =>
      Or.elim
        h
        (fun hp : p => ⟨Or.inl hp, Or.inl hp⟩) -- p -> (p ∨ q) ∧ (p ∨ r)
        (fun hqr : q ∧ r => ⟨Or.inr hqr.left, Or.inr hqr.right⟩)-- q ∧ r -> (p ∨ q) ∧ (p ∨ r)
    )
    (-- (p ∨ q) ∧ (p ∨ r) -> p ∨ (q ∧ r) 
      fun h : (p ∨ q) ∧ (p ∨ r) =>
      Or.elim
        h.left                    -- (p ∨ q)
        (fun hp : p => Or.inl hp) -- p -> p ∨ (q ∧ r)
        (
          fun hq : q =>           -- q -> p ∨ (q ∧ r)
          Or.elim 
            h.right                           -- p ∨ r
            (fun hp : p => Or.inl hp)         -- p -> p ∨ (q ∧ r)
            (fun hr : r => Or.inr ⟨hq, hr⟩)   -- r -> p ∨ (q ∧ r)
        )
    )
