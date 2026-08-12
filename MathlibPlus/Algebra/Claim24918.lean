import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Tactic

namespace MathlibPlus.Algebra

/-- The exact total-six two-copy pendant-moment kernel relation from packet R-0809. -/
theorem totalSixTwoCopyKernelRelation_claim24918 :
    let t : MvPolynomial (Fin 2) ℚ := MvPolynomial.X 0
    let u : MvPolynomial (Fin 2) ℚ := MvPolynomial.X 1
    let e6t : MvPolynomial (Fin 2) ℚ := 1 + 6 * t
    let e51t : MvPolynomial (Fin 2) ℚ := (1 + 5 * t) * (1 + t)
    let e42t : MvPolynomial (Fin 2) ℚ := (1 + 4 * t) * (1 + 2 * t)
    let e33t : MvPolynomial (Fin 2) ℚ := (1 + 3 * t) * (1 + 3 * t)
    let e6u : MvPolynomial (Fin 2) ℚ := 1 + 6 * u
    let e51u : MvPolynomial (Fin 2) ℚ := (1 + 5 * u) * (1 + u)
    let e42u : MvPolynomial (Fin 2) ℚ := (1 + 4 * u) * (1 + 2 * u)
    let e33u : MvPolynomial (Fin 2) ℚ := (1 + 3 * u) * (1 + 3 * u)
    (-(e6t * e6u) + 6 * (e51t * e51u) - 15 * (e42t * e42u) +
        10 * (e33t * e33u) = 0) := by
  dsimp
  ring

end MathlibPlus.Algebra
