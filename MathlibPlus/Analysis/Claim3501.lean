import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Tactic.FieldSimp

namespace MathlibPlus.Analysis.Claim3501

/-- The quotient derivative in the additive perturbation statement from claim 3501. -/
theorem additiveBoundaryPerturbationDerivative
    {𝕜 : Type*} [NontriviallyNormedField 𝕜]
    (B B₀ E : 𝕜 → 𝕜) (B₀' E' : 𝕜) (x : 𝕜)
    (hB : B = B₀ + E)
    (hB₀ : HasDerivAt B₀ B₀' x) (hE : HasDerivAt E E' x)
    (hB₀_ne : B₀ x ≠ 0) :
    HasDerivAt (fun y => (B y - B₀ y) / B₀ y)
      (E' / B₀ x - E x * B₀' / B₀ x ^ 2) x := by
  have h := hE.div hB₀ hB₀_ne
  have hquot :
      HasDerivAt (fun y => E y / B₀ y)
        (E' / B₀ x - E x * B₀' / B₀ x ^ 2) x := by
    convert h using 1
    · rfl
    · funext y
      rfl
    · field_simp [hB₀_ne]
  rw [hB]
  simpa only [Pi.add_apply, add_sub_cancel_left] using hquot

end MathlibPlus.Analysis.Claim3501
