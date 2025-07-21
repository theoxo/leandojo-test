theorem ex1_and_comm (p q : Prop) : p ∧ q → q ∧ p := by
  intro h
  cases h with | intro h1 h2 =>
  constructor
  exact h2
  exact h1


theorem ex2_or_comm (p q : Prop) : p ∨ q → q ∨ p := by
  intro h
  cases h with
  | inl h1 =>
    right
    exact h1
  | inr h2 =>
    left
    exact h2

theorem ex3_imp_trans (p q r : Prop) : (p → q) → (q → r) → (p → r) := by
  intro h1
  intro h2
  intro h3
  apply h2
  apply h1
  exact h3

theorem ex4_and_distrib_or (p q r : Prop) : p ∧ (q ∨ r) → (p ∧ q) ∨ (p ∧ r) := by
  intro h
  cases h with
  | intro h1 h2 =>
    cases h2 with
    | inl h3 =>
      left
      constructor
      exact h1
      exact h3
    | inr h4 =>
      right
      constructor
      exact h1
      exact h4

theorem ex5_de_morgan_and (p q : Prop) : ¬(p ∧ q) → ¬p ∨ ¬q := by
  intro h1
  by_cases h2 : p
  right
  intro h3
  apply h1
  constructor
  exact h2
  exact h3
  left
  exact h2

theorem ex6_de_morgan_or (p q : Prop) : ¬(p ∨ q) → ¬p ∧ ¬q := by
  intro h
  constructor
  intro h1
  apply h
  left
  exact h1
  intro h2
  apply h
  right
  exact h2

theorem ex7_iff_symm (p q : Prop) : (p ↔ q) → (q ↔ p) := by
  intro h
  constructor
  intro h1
  apply h.mpr
  exact h1
  intro h2
  apply h.mp
  exact h2

theorem ex8_contrapositive (p q : Prop) : (p → q) → (¬q → ¬p) := by
  intro h1
  intro h2
  intro h3
  apply h2
  apply h1
  exact h3

theorem ex9_or_distrib_and (p q r : Prop) : p ∨ (q ∧ r) → (p ∨ q) ∧ (p ∨ r) := by
  intro h
  cases h with
  | inl h1 =>
    constructor
    left
    exact h1
    left
    exact h1
  | inr h2 =>
    cases h2 with
    | intro h3 h4 =>
      constructor
      right
      exact h3
      right
      exact h4

theorem ex10_absorbtion (p q : Prop) : p ∧ (p ∨ q) ↔ p := by
  constructor
  intro h
  cases h with
  | intro h1 _ =>
    exact h1
  intro h1
  constructor
  exact h1
  left
  exact h1
