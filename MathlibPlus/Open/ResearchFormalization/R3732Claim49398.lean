import Mathlib

namespace MathlibPlus.Open.ResearchFormalization.R3732Claim49398

open scoped BigOperators

noncomputable section

abbrev Outcome := Fin 3 → Bool

def sign (b : Bool) : ℝ :=
  if b then 1 else -1

def selector (ω : Outcome) : ℝ :=
  if sign (ω 0) = -1 then sign (ω 2) else sign (ω 1)

def agreesOn (A : Finset (Fin 3)) (ω ω' : Outcome) : Prop :=
  Finset.fold (· && ·) true (fun i => ω i == ω' i) A = true

def fiber (A : Finset (Fin 3)) (ω : Outcome) : Finset Outcome :=
  Finset.univ.filter
    (fun ω' => Finset.fold (· && ·) true (fun i => ω i == ω' i) A = true)

def meanOn (A : Finset Outcome) (f : Outcome → ℝ) : ℝ :=
  (∑ ω ∈ A, f ω) / (A.card : ℝ)

def conditionalVariance (A : Finset (Fin 3)) (ω : Outcome) : ℝ :=
  let C := fiber A ω
  let μ := meanOn C selector
  (∑ ω' ∈ C, (selector ω' - μ) ^ 2) / (C.card : ℝ)

def expectedConditionalVariance (A : Finset (Fin 3)) : ℝ :=
  (∑ ω : Outcome, conditionalVariance A ω) /
    (Fintype.card Outcome : ℝ)

def revealed (π : Equiv.Perm (Fin 3)) (m : Fin 4) : Finset (Fin 3) :=
  Finset.univ.filter (fun i => (π i).val < m.val)

def staticOrderArea (π : Equiv.Perm (Fin 3)) : ℝ :=
  ∑ m : Fin 4, expectedConditionalVariance (revealed π m)

def position (π : Equiv.Perm (Fin 3)) (i : Fin 3) : ℝ :=
  ((π i).val + 1 : ℝ)

def formula (π : Equiv.Perm (Fin 3)) : ℝ :=
  (1 / 4 : ℝ) *
    (position π 1 + position π 2 +
      max (position π 0) (position π 1) +
      max (position π 0) (position π 2))

/-- Claim 49398: the depth-two selector's posterior-variance area is the
stated fixed-order formula, with all six deterministic orders classified. -/
def claim49398 : Prop :=
  (∀ π : Equiv.Perm (Fin 3), staticOrderArea π = formula π) ∧
    (∀ π : Equiv.Perm (Fin 3),
      (position π 0 = 1 → staticOrderArea π = 5 / 2) ∧
      ((position π 0 = 2 ∨ position π 0 = 3) →
        staticOrderArea π = 9 / 4)) ∧
    (∀ π : Equiv.Perm (Fin 3), 9 / 4 ≤ staticOrderArea π) ∧
    (∃ π : Equiv.Perm (Fin 3), staticOrderArea π = 9 / 4) ∧
    (Finset.univ.filter
      (fun π : Equiv.Perm (Fin 3) => staticOrderArea π = 9 / 4)).card = 4 ∧
    (Finset.univ.filter
      (fun π : Equiv.Perm (Fin 3) => position π 0 = 1)).card = 2

end

end MathlibPlus.Open.ResearchFormalization.R3732Claim49398
