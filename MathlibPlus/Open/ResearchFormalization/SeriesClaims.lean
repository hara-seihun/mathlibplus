import Mathlib

namespace MathlibPlus.Open.ResearchFormalization.SeriesClaims
noncomputable section

def entireExpansion (A : ℂ → ℂ) (a : ℕ → ℂ) : Prop :=
  ∀ z : ℂ, HasSum (fun n => a n * z ^ n) (A z)

def endpointCoefficient (a : ℕ → ℂ) (α : ℂ) (n : ℕ) : ℂ :=
  ∑' j : ℕ, a (n + 1 + j) * α ^ j

def bilateralCoefficient (c : ℕ → ℂ) (b α : ℂ) (n : ℤ) : ℂ :=
  if 0 ≤ n then c n.toNat else b * α ^ ((-n).toNat - 1)

def endpointBlock (d : ℤ → ℂ) (k : ℕ) : Matrix (Fin 3) (Fin 2) ℂ :=
  fun i j => d ((k : ℤ) + (j.val : ℤ) - (i.val : ℤ))

def twoByTwoMinor (d : ℤ → ℂ) (k : ℕ) (r₀ r₁ : Fin 3) : ℂ :=
  endpointBlock d k r₀ 0 * endpointBlock d k r₁ 1 -
    endpointBlock d k r₀ 1 * endpointBlock d k r₁ 0

def maximalCofactor (d : ℤ → ℂ) (k : ℕ) (m : Fin 3) : ℂ :=
  match m.val with
  | 0 => twoByTwoMinor d k 1 2
  | 1 => twoByTwoMinor d k 0 2
  | _ => twoByTwoMinor d k 0 1

def claim12077 : Prop :=
  ∀ (A : ℂ → ℂ) (a : ℕ → ℂ) (α b : ℂ),
    entireExpansion A a → A α = b →
      ∃ (C : ℂ → ℂ) (c : ℕ → ℂ),
        (∀ z : ℂ, z ≠ α → C z = (A z - b) / (z - α)) ∧
        (∀ z : ℂ, HasSum (fun n => c n * z ^ n) (C z)) ∧
        (∀ n : ℕ, c n = endpointCoefficient a α n)

def claim12078 : Prop :=
  ∀ (c : ℕ → ℂ) (b α : ℂ),
    ∀ k : ℕ, 1 ≤ k →
      let d := bilateralCoefficient c b α
      (∃ (B : Matrix (Fin 3) (Fin 2) ℂ) (Δ : Fin 3 → ℂ),
        B = endpointBlock d k ∧
          ∀ m : Fin 3, Δ m = maximalCofactor d k m) ∧
      (∀ n : ℕ, d (n : ℤ) = c n) ∧
      (∀ j : ℕ, 1 ≤ j → d (-(j : ℤ)) = b * α ^ (j - 1))

def claim12081 : Prop :=
  ∀ (A : ℂ → ℂ) (a c : ℕ → ℂ) (α b : ℂ),
    entireExpansion A a → A α = b →
      (∀ n : ℕ, c n = endpointCoefficient a α n) →
      let d := bilateralCoefficient c b α
      (∀ k : ℕ, 1 ≤ k →
        maximalCofactor d k 1 - α * maximalCofactor d k 2 =
          c k * a k - c (k + 1) * a (k - 1)) ∧
      (∀ k : ℕ, 2 ≤ k →
        maximalCofactor d k 0 - α * maximalCofactor d k 1 =
          a k * c (k - 1) - a (k + 1) * c (k - 2)) ∧
      (maximalCofactor d 1 0 - α * maximalCofactor d 1 1 =
        a 1 * c 0 - b * a 2)

end
end MathlibPlus.Open.ResearchFormalization.SeriesClaims
