import Mathlib

noncomputable section

namespace MathlibPlus.Open.ResearchFormalizationBatch

/-- The upper-triangular Pascal matrix specified by the admitted claim. -/
def pascalEntry (q : ℝ) (i p : ℕ) : ℝ :=
  if i ≤ p then
    q ^ i * (Nat.choose p i : ℝ) * ((1 - q) / 2) ^ (p - i)
  else 0

def pascalAffine (q x : ℝ) : ℝ := (1 - q) / 2 + q * x

def pascalMinor {n : ℕ} (q : ℝ) (I J : Fin n → ℕ) : ℝ :=
  Matrix.det (fun i j => pascalEntry q (I i) (J j))

def pascalSemigroupAndTotalNonnegativity : Prop :=
  ∀ (q₁ q₂ : ℝ),
    0 < q₁ → q₁ < 1 → 0 < q₂ → q₂ < 1 →
      (pascalAffine q₁ (1 / 2) = 1 / 2 ∧
        pascalAffine q₂ (1 / 2) = 1 / 2 ∧
        (∀ x : ℝ,
          pascalAffine q₁ (pascalAffine q₂ x) = pascalAffine (q₁ * q₂) x) ∧
        (∀ i p : ℕ,
          ∑' k : ℕ, pascalEntry q₁ i k * pascalEntry q₂ k p =
            pascalEntry (q₁ * q₂) i p) ∧
        (∀ (q : ℝ) (n : ℕ) (I J : Fin n → ℕ),
          0 < q → q < 1 → StrictMono I → StrictMono J →
            0 ≤ pascalMinor q I J))

def profileSize {n : ℕ} (P : Fin n → ℕ) : ℕ :=
  ∑ i, P i

def profileVandermonde {n : ℕ} (P : Fin n → ℕ) : ℝ :=
  ∏ i : Fin n, ∏ j : Fin n,
    if i.val < j.val then (P j : ℝ) - (P i : ℝ) else 1

def profileFactorial {n : ℕ} : ℝ :=
  ∏ j : Fin n, (Nat.factorial j.val : ℝ)

def initialPascalMinor {n : ℕ} (q : ℝ) (P : Fin n → ℕ) : ℝ :=
  pascalMinor q (fun i : Fin n => i.val) P

def initialProfilePascalMinorFormula : Prop :=
  ∀ (n : ℕ) (q : ℝ) (P : Fin n → ℕ),
    0 < q → q < 1 → StrictMono P →
      let α : ℝ := (1 - q) / 2
      (initialPascalMinor q P =
        q ^ (n * (n - 1) / 2) *
          α ^ (profileSize P - n * (n - 1) / 2) *
          profileVandermonde P / profileFactorial (n := n) ∧
        0 < initialPascalMinor q P)

end MathlibPlus.Open.ResearchFormalizationBatch
