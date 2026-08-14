import Mathlib

noncomputable section

namespace MathlibPlus.Open.FormalizationBatch.Algebra

/- Claim 53101. -/
def cubicMap {p : ℕ} (z : Fin 3 → ZMod p) : Fin 3 → ZMod p :=
  ![z 0 ^ 2 + z 0 * z 1 * z 2, z 1 ^ 2, z 2 ^ 2]

def cubicDifference {p : ℕ} (z a : Fin 3 → ZMod p) : Fin 3 → ZMod p :=
  cubicMap z + cubicMap a - cubicMap (z + a)

def cubicDifferenceSpan {p : ℕ} (z : Fin 3 → ZMod p) :
    Submodule (ZMod p) (Fin 3 → ZMod p) :=
  Submodule.span (ZMod p) (Set.range (fun a : Fin 3 → ZMod p => cubicDifference z a))

def finiteFieldCubicDifferenceClaim : Prop :=
  ∀ (p : ℕ) (_hp5 : 5 ≤ p) (hprime : Nat.Prime p),
    letI : Fact (Nat.Prime p) := ⟨hprime⟩
    ∀ z : Fin 3 → ZMod p, cubicMap z ∈ cubicDifferenceSpan z

/- Claim 54096. -/
abbrev Sign := {x : ℝ // x = (-1 : ℝ) ∨ x = 1}

def rareExceptionLambdaZero : ℝ := 31 / 32

def rareExceptionLambdaOne : ℝ := 1 / 32

def exactRareExceptionWitness : Prop :=
  ∃ (T₀ T₁ μ : (Fin 3 → Sign) → ℝ),
    (∀ x,
      T₀ x =
        if (x 0 : ℝ) = 1 ∧ (x 1 : ℝ) = 1 ∧ (x 2 : ℝ) = -1 then -1 else 1) ∧
    (∀ x,
      T₁ x =
        if (x 1 : ℝ) = 1 ∧ (x 2 : ℝ) = -1 then -1 else 1) ∧
    (∀ x,
      μ x = rareExceptionLambdaZero * T₀ x + rareExceptionLambdaOne * T₁ x)

/- Claim 54107. -/
def sourceErrorPerturbationEstimate : Prop :=
  ∀ (a e_C e_L : ℝ), 0 ≤ a →
    (|e_C - a * e_L| + |e_L - a * e_C|) / (1 + a) ≤ |e_C| + |e_L|

/- Claim 54885. -/
def uniqueSelectedCarrierCancellation : Prop :=
  ∀ (A A' : ℂ) (u p : ℝ), A ≠ 0 →
    A' / A = (u : ℂ) + Complex.I * (p : ℂ) → 0 < p →
    let α : ℂ := (u : ℂ) + Complex.I * (p : ℂ)
    let cStar : ℂ := -1 / α
    (1 + cStar * α = 0) ∧
      (∀ c : ℂ, 1 + c * α = 0 → c = cStar) ∧
      (1 + cStar * star α = 2 * Complex.I * (p : ℂ) / α) ∧
      2 * Complex.I * (p : ℂ) / α ≠ 0

end MathlibPlus.Open.FormalizationBatch.Algebra
