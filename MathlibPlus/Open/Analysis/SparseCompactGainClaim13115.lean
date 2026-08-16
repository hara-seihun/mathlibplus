import Mathlib

open Filter
open scoped BigOperators

namespace MathlibPlus.Open.Analysis.SparseCompactGainClaim13115

noncomputable section

/-- The sparse degree `d_L = floor(L^(1/(2k)))` from the admitted profile. -/
def sparseDegree (k L : ℕ) : ℕ :=
  ⌊Real.rpow (L : ℝ) (1 / (2 * (k : ℝ)))⌋₊

/-- The degree-`d` sparse profile `1 + (Bu)^d`. -/
def sparseProfileOfDegree (B : ℝ) (d : ℕ) (u : ℝ) : ℝ :=
  1 + (B * u) ^ d

/-- The cutoff-dependent sparse profile. -/
def sparseProfile (B : ℝ) (k L : ℕ) (u : ℝ) : ℝ :=
  sparseProfileOfDegree B (sparseDegree k L) u

/-- The compact supremum of the absolute sparse profile at a fixed degree. -/
noncomputable def compactSup (B U : ℝ) (d : ℕ) : ℝ :=
  sSup (Set.range (fun u : {u : ℝ // |u| ≤ U} =>
    |sparseProfileOfDegree B d u.1|))

/-- The compact logarithmic gain `log⁺ sup_(|u|≤U) |P(u)|`. -/
noncomputable def compactLogGain (B U : ℝ) (d : ℕ) : ℝ :=
  max 0 (Real.log (compactSup B U d))

/-- The sparse family's cutoff-dependent logarithmic gain. -/
noncomputable def sparseLogGain (B U : ℝ) (k L : ℕ) : ℝ :=
  compactLogGain B U (sparseDegree k L)

/-- The exact compact gain and its retained little-o and Theta asymptotics. -/
def claim13115 : Prop :=
  ∀ (k : ℕ) (B U : ℝ),
    1 ≤ k → 1 < B → 0 < U → 1 < B * U →
      (∀ d : ℕ,
        compactSup B U d = 1 + (B * U) ^ d) ∧
      (∀ L : ℕ,
        sparseLogGain B U k L =
          Real.log (1 + (B * U) ^ (sparseDegree k L))) ∧
      Asymptotics.IsLittleO atTop
        (fun L : ℕ =>
          sparseLogGain B U k L -
            (sparseDegree k L : ℝ) * Real.log (B * U))
        (fun _ : ℕ => (1 : ℝ)) ∧
      Asymptotics.IsTheta atTop
        (fun L : ℕ => sparseLogGain B U k L)
        (fun L : ℕ =>
          Real.rpow (L : ℝ) (1 / (2 * (k : ℝ))))

end
end MathlibPlus.Open.Analysis.SparseCompactGainClaim13115
