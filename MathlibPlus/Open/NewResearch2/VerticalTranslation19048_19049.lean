import Mathlib

namespace MathlibPlus.Open.NewResearch2.VerticalTranslation

noncomputable section

/-- Claim 19048: vertical translation preserves the derivative, so a
non-real-rooted derivative obstructs real-rootedness of every translate. -/
def claim19048_derivativeObstructionToRealRooting
    (p : Polynomial ℝ) : Prop :=
  let realRooted : Polynomial ℝ → Prop := fun f =>
    ∀ z : ℂ,
      (Polynomial.map (algebraMap ℝ ℂ) f).eval z = 0 → z.im = 0
  (∀ c : ℝ, realRooted (p + Polynomial.C c) → realRooted p.derivative) ∧
    (¬ realRooted p.derivative →
      ∀ c : ℝ, ¬ realRooted (p + Polynomial.C c))

/-- Claim 19049: the degree-four boundary family differs only by constants,
and its common derivative has non-real roots. -/
def claim19049_degreeFourTaylorTruncationNoRealTranslate
    (H : ℝ → Polynomial ℝ) (d : Polynomial ℝ) : Prop :=
  let realRooted : Polynomial ℝ → Prop := fun f =>
    ∀ z : ℂ,
      (Polynomial.map (algebraMap ℝ ℂ) f).eval z = 0 → z.im = 0
  (∀ x : ℝ, (H x).natDegree = 4) ∧
    (∀ x y : ℝ, ∃ c : ℝ, H x = H y + Polynomial.C c) ∧
    (∀ x : ℝ, (H x).derivative = d) ∧
    ¬ realRooted d ∧
    (∀ x : ℝ, ¬ realRooted (H x))

end
end MathlibPlus.Open.NewResearch2.VerticalTranslation
