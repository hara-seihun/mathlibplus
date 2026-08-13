import Mathlib

namespace MathlibPlus.Algebra.Claim29919

noncomputable section

/-!
The source's `F_{p,q,δ}` is represented as a field-valued rational expression
in an explicit coordinate `Z`.  The source's `Z=((f-D)/(f+D))^2` is a caller's
coordinate choice; keeping `Z` as an argument preserves the displayed
identity without adding an unmentioned domain convention.
-/

/-- Numerator in the displayed midpoint completion fraction. -/
def numerator {K : Type*} [Field K] (p q : ℕ) (δ Z : K) : K :=
  (p : K) * q * (Z ^ p - Z ^ q) +
    δ * ((p - q : K) * Z ^ (p + q) - p * Z ^ p + q * Z ^ q)

/-- Denominator in the displayed midpoint completion fraction. -/
def denominator {K : Type*} [Field K] (p q : ℕ) (δ Z : K) : K :=
  (p : K) * q * (Z ^ p - Z ^ q) +
    δ * (p * Z ^ q - p - q * Z ^ p + q)

/-- The rational function displayed in the midpoint-completion claims. -/
def midpointCompletion {K : Type*} [Field K] (p q : ℕ) (δ Z : K) : K :=
  numerator p q δ Z / denominator p q δ Z

/-- Scaling all three exponents and the node parameter scales the numerator. -/
theorem numerator_scale {K : Type*} [Field K]
    (g p q : ℕ) (δ Z : K) :
    numerator (g * p) (g * q) ((g : K) * δ) Z =
      (g : K) ^ 2 * numerator p q δ (Z ^ g) := by
  simp only [numerator, Nat.cast_mul, pow_mul]
  ring

/-- Expanded form of the denominator recorded in the source packet. -/
theorem denominator_expanded {K : Type*} [Field K]
    (p q : ℕ) (δ Z : K) :
    denominator p q δ Z =
      δ * ((q : K) - p) +
        (q : K) * ((p : K) - δ) * Z ^ p +
        (p : K) * (δ - q) * Z ^ q := by
  simp only [denominator]
  ring

/-- Scaling all three exponents and the node parameter scales the denominator. -/
theorem denominator_scale {K : Type*} [Field K]
    (g p q : ℕ) (δ Z : K) :
    denominator (g * p) (g * q) ((g : K) * δ) Z =
      (g : K) ^ 2 * denominator p q δ (Z ^ g) := by
  simp only [denominator, Nat.cast_mul, pow_mul]
  ring

/-- The midpoint completion has the gcd-scaling law, in fact for every
positive scaling factor (the gcd specialization is the source claim). -/
theorem midpointCompletion_gcd_scale {K : Type*} [Field K] [CharZero K]
    (g p q : ℕ) (δ Z : K) (hg : 0 < g) :
    midpointCompletion (g * p) (g * q) ((g : K) * δ) Z =
      midpointCompletion p q δ (Z ^ g) := by
  unfold midpointCompletion
  rw [numerator_scale, denominator_scale]
  have hgK : (g : K) ^ 2 ≠ 0 := by
    exact pow_ne_zero 2 (Nat.cast_ne_zero.mpr (Nat.ne_of_gt hg))
  by_cases hden : denominator p q δ (Z ^ g) = 0
  · simp [hden]
  · field_simp [hgK, hden]
    exact mul_div_cancel_left₀ _ (Nat.cast_ne_zero.mpr (Nat.ne_of_gt hg))

/-- Exact source-variable form: `g` is the gcd and `p,q,δ` are the scaled
variables. -/
theorem gcdScaling_claim29919
    (g p₀ q₀ p q : ℕ) (δ₀ δ Z : ℚ)
    (hg : 0 < g) (hgcd : Nat.gcd p q = g)
    (hp : p = g * p₀) (hq : q = g * q₀)
    (hδ : δ = (g : ℚ) * δ₀) :
    midpointCompletion p q δ Z =
      midpointCompletion p₀ q₀ δ₀ (Z ^ g) := by
  subst p
  subst q
  subst δ
  exact midpointCompletion_gcd_scale g p₀ q₀ δ₀ Z hg

end
end MathlibPlus.Algebra.Claim29919
