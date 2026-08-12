import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith

namespace MathlibPlus.Analysis.Claim13911

/-- The free Neumann cosine solution and the corresponding energy-dependent
Robin characteristic from claim 13911.

The second-derivative coefficient is written in product-normalized form
`(-z) * (cos (z*x) * z)` so that the derivative proof is direct; it is the
same scalar as `-z^2 * cos (z*x)`. -/
theorem freeNeumann_cosine_solution_characteristic
    (a z lam : ℝ) (τ : ℝ → ℝ) (hz : z ^ 2 = lam) :
    let u : ℝ → ℝ := fun x => Real.cos (z * x)
    let χ : ℝ → ℝ := fun w =>
      w * Real.sin (a * w) - τ (w ^ 2) * Real.cos (a * w)
    u 0 = 1 ∧
      HasDerivAt u 0 0 ∧
      (∀ x,
        HasDerivAt u (-z * Real.sin (z * x)) x ∧
          HasDerivAt (fun y => -z * Real.sin (z * y))
            ((-z) * (Real.cos (z * x) * z)) x ∧
          -((-z) * (Real.cos (z * x) * z)) = lam * u x) ∧
      u a = Real.cos (a * z) ∧
      HasDerivAt u (-z * Real.sin (a * z)) a ∧
      ((-z * Real.sin (a * z) + τ lam * Real.cos (a * z) = 0) ↔ χ z = 0) := by
  dsimp
  have harg (x : ℝ) :
      HasDerivAt (fun y : ℝ => z * y) z x := by
    exact hasDerivAt_const_mul z
  have hcos (x : ℝ) :
      HasDerivAt (fun y : ℝ => Real.cos (z * y))
        (-Real.sin (z * x) * z) x := by
    simpa [Function.comp_def] using
      (Real.hasDerivAt_cos (z * x)).comp x (harg x)
  have hsin (x : ℝ) :
      HasDerivAt (fun y : ℝ => Real.sin (z * y))
        (Real.cos (z * x) * z) x := by
    simpa [Function.comp_def] using
      (Real.hasDerivAt_sin (z * x)).comp x (harg x)
  have hsecond (x : ℝ) :
      HasDerivAt (fun y : ℝ => -z * Real.sin (z * y))
        ((-z) * (Real.cos (z * x) * z)) x := by
    exact (hsin x).const_mul (-z)
  constructor
  · norm_num
  constructor
  · convert hcos 0 using 1 <;> norm_num
  constructor
  · intro x
    refine ⟨?_, ?_, ?_⟩
    · convert hcos x using 1 <;> ring
    · exact hsecond x
    · calc
        -((-z) * (Real.cos (z * x) * z)) = z ^ 2 * Real.cos (z * x) := by ring
        _ = lam * Real.cos (z * x) := by rw [hz]
  constructor
  · congr 1 <;> ring
  constructor
  · convert hcos a using 1 <;> simp [mul_comm]
  · rw [hz]
    constructor <;> intro h <;> linarith

end MathlibPlus.Analysis.Claim13911
