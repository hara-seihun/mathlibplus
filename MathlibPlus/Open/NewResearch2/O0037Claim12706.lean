import Mathlib

namespace MathlibPlus.Open.NewResearch2.O0037

noncomputable section

/-- Claim 12706 uses the positive-integer logarithmic spectrum and the
finite-module support obtained by applying one nonconstant affine rescaling to
finitely many ordinary arithmetic progressions. -/
def claim12706 : Prop :=
  let PositiveNat := {n : ℕ // 0 < n}
  let arithmeticSpectrum : Set ℝ :=
    Set.range (fun n : PositiveNat => Real.log (n.1 : ℝ))
  let affineProgression : ℝ → ℝ → ℝ → Set ℝ := fun h a b =>
    Set.range (fun k : ℕ => a * (h + (k : ℝ)) + b)
  ∀ (m : ℕ) (h : Fin m → ℝ) (a b : ℝ),
    a ≠ 0 →
      arithmeticSpectrum ≠
        ⋃ i : Fin m, affineProgression (h i) a b

end

end MathlibPlus.Open.NewResearch2.O0037
