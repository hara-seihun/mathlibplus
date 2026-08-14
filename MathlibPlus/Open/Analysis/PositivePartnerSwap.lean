import Mathlib

namespace MathlibPlus.Open.Analysis

/--
On the paired off-axis two-state block, the positive partner swap is not
compatible with the prime block away from the unit-modulus locus.
-/
def positivePartnerSwapDestroysPrimeUnitarity : Prop :=
  ∀ (m : ℝ) (p : ℕ) (lam : ℂ),
    0 < m →
    p.Prime →
    ‖Complex.cpow (p : ℂ) lam‖ ≠ 1 →
    let B : Matrix (Fin 2) (Fin 2) ℂ :=
      (m : ℂ) • !![0, 1; 1, 0]
    let Cplus : Matrix (Fin 2) (Fin 2) ℂ :=
      !![0, 1; 1, 0]
    let Up : Matrix (Fin 2) (Fin 2) ℂ :=
      !![Complex.cpow (p : ℂ) lam, 0;
         0, Complex.cpow (p : ℂ) (-star lam)]
    B * Cplus = (m : ℂ) • (1 : Matrix (Fin 2) (Fin 2) ℂ) ∧
    Matrix.PosDef (m • (1 : Matrix (Fin 2) (Fin 2) ℝ)) ∧
    (Cplus * Up - Up * Cplus) ≠ 0 ∧
    Matrix.conjTranspose Up *
          ((m : ℂ) • (1 : Matrix (Fin 2) (Fin 2) ℂ)) * Up ≠
      (m : ℂ) • (1 : Matrix (Fin 2) (Fin 2) ℂ)

end MathlibPlus.Open.Analysis
