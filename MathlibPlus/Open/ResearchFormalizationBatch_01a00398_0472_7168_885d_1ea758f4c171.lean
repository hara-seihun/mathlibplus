import Mathlib

namespace MathlibPlus.Open

open scoped BigOperators

noncomputable section

/-- The order-`m`, parameter-`1/2` Laguerre factor in the packet's kernel. -/
def laguerreHalf (m : ℕ) (x : ℝ) : ℝ :=
  Finset.sum (Finset.range (m + 1)) (fun k =>
    ((-1 : ℝ) ^ k * x ^ k *
      Finset.prod (Finset.range (m - k)) (fun j =>
        ((1 / 2 : ℝ) + (m : ℝ) - (j : ℝ)))) /
      ((Nat.factorial k : ℝ) * (Nat.factorial (m - k) : ℝ)))

/-- The packet's logarithmic autocorrelation factor. -/
def homogeneityPhi (m : ℕ) (σ r : ℝ) : ℝ :=
  Real.rpow r (3 - 2 * σ) * Real.exp (-(r ^ 2)) * laguerreHalf m (r ^ 2)

def homogeneityKernel (m : ℕ) (σ d : ℝ) : ℝ :=
  2 * ∫ s : ℝ,
    homogeneityPhi m σ (Real.exp (s + d)) * homogeneityPhi m σ (Real.exp s)

/-- The positive-variable carrier `𝔟` supplied by the logarithmic representation. -/
def homogeneityB (m : ℕ) (σ : ℝ)
    (u v : {x : ℝ // 0 < x}) : ℝ :=
  Real.rpow ((u : ℝ) * (v : ℝ)) (2 * σ - 2) *
    homogeneityKernel m σ (Real.log (u : ℝ) - Real.log (v : ℝ))

def homogeneityScale (c : ℝ) (u : {x : ℝ // 0 < x}) (hc : 0 < c) :
    {x : ℝ // 0 < x} :=
  ⟨c * (u : ℝ), mul_pos hc u.property⟩

/-- Exact homogeneity law from admitted Claim 7821. -/
def claim7821 : Prop :=
  ∀ (m : ℕ) (σ : ℝ),
    ((1 / 2 : ℝ) < σ ∧ σ < (3 / 2 : ℝ)) →
      ∀ (c : ℝ) (hc : 0 < c)
        (u v : {x : ℝ // 0 < x}),
        homogeneityB m σ (homogeneityScale c u hc) (homogeneityScale c v hc) =
          Real.rpow c (4 * σ - 4) * homogeneityB m σ u v

end

end MathlibPlus.Open
