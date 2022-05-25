variable (p q r : Prop)

-- commutativity of ∧
example : p ∧ q ↔ q ∧ p := 
  Iff.intro
    --p ∧ q -> q ∧ p
    (fun h : p ∧ q => And.intro (And.right h) (And.left h))
    --q ∧ p -> p ∧ q
    (fun h : q ∧ p => And.intro (And.right h) (And.left h))

-- commutativity of ∨
example : p ∨ q ↔ q ∨ p :=
  Iff.intro
    (fun hpq : p ∨ q => 
      Or.elim (hpq)                                         -- p ∨ q
      (fun hp : p => show q ∨ p from Or.intro_right q hp)  -- p -> q ∨ p
      (fun hq : q => show q ∨ p from Or.intro_left p hq)   -- q -> q ∨ p
    )
    (fun hqp : q ∨ p =>
      Or.elim (hqp)                                         -- q ∨ p
      (fun hq : q => show p ∨ q from Or.intro_right p hq)  -- q -> p ∨ q
      (fun hp : p => show p ∨ q from Or.intro_left q hp)   -- p -> p ∨ q
    )
