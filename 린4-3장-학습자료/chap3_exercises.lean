--exclusive middle이 포함되어 있는 문제
open Classical

variable (p q r s : Prop)

theorem dneg (hnnp : ¬¬p) : p :=
  byContradiction (fun hnp : ¬p => hnnp hnp)

example : (p → r ∨ s) → ((p → r) ∨ (p → s)) := 
  fun h : p → r ∨ s =>
    byCases -- r, ¬r
      (fun hr : r => Or.inl (fun hp : p => hr))
      (fun hnr : ¬r =>
        Or.inr
          (fun hp : p =>
            (h hp).elim
            (fun hr : r => absurd hr hnr)
            (fun hs : s => hs)
          )
      )
  
example : ¬(p ∧ q) → ¬p ∨ ¬q := 
  fun h : ¬(p ∧ q) =>
    byCases -- p, ¬p
      (fun hp : p => Or.inr (fun hq : q => h ⟨hp, hq⟩) )
      (fun hnp : ¬p => Or.inl hnp)

example : ¬(p → q) → p ∧ ¬q :=
  have lem (p q : Prop) (h : ¬(¬p ∨ q)) : p ∧ ¬q :=
    ⟨dneg p (fun hnp : ¬p => h (Or.inl hnp)),
      fun hq : q => h (Or.inr hq)⟩
  fun h : ¬(p → q) =>
    lem p q ((prop11 (¬p ∨ q) (p → q) (prop8 p q)) h)


example : (p → q) → (¬p ∨ q) :=
  have lem (p q : Prop) (h : ¬(¬p ∨ q)) : p ∧ ¬q :=
    ⟨dneg p (fun hnp : ¬p => h (Or.inl hnp)),
      fun hq : q => h (Or.inr hq)⟩
  fun h : ¬(p → q) =>
    lem p q ((prop11 (¬p ∨ q) (p → q) (prop8 p q)) h)

example : (¬q → ¬p) → (p → q) := 
  fun (h : ¬q → ¬p) (hp : p) =>
    byCases
      (fun hq : q => hq)
      (fun hnq : ¬q => absurd hp (h hnq))

example : p ∨ ¬p := em p -- exclusive middle

example : (((p → q) → p) → p) :=
  have lem := clprop4 (p → q) p
  fun h : ((p → q) → p) =>
    (lem h).elim
      (fun hnpq : ¬(p → q) =>
        (clprop3 p q hnpq).left)
      (fun hp : p => hp)