import Mathlib

namespace MathlibPlus.Open

/--
Orbit-product law and ordinary-power defect in the inversion-compression setup.
The two-sided-inverse equations express `DTD = T⁻¹` without an inverse operation
on the endomorphism ring. The local functions are the underlying vectors of the
restrictions to `range P`.
-/
def orbitProductLaw_claim10968
    (V : Type*) [AddCommGroup V] [Module ℚ V]
    (T D : Module.End ℚ V) : Prop :=
  IsUnit T ∧
      D * D = 1 ∧
      (D * T * D) * T = 1 ∧
      T * (D * T * D) = 1 →
    let P : Module.End ℚ V := ((1 : ℚ) / 2) • (1 + D)
    let C : ℕ → P.range → V :=
      fun n x => P ((T ^ n) (P x.1))
    let composite : ℕ → ℕ → P.range → V :=
      fun m n x => P ((T ^ m) (P (P ((T ^ n) (P x.1)))))
    (∀ (m n : ℕ) (x : P.range),
      composite m n x =
          ((1 : ℚ) / 2) • (C (m + n) x + C (Nat.dist m n) x)) ∧
    (∀ (x : P.range),
      C 2 x = (2 : ℚ) • composite 1 1 x - x.1) ∧
    (∀ (x : P.range),
      C 2 x - composite 1 1 x = composite 1 1 x - x.1)

end MathlibPlus.Open
