import Mathlib
import MathlibPlus.Open.AlgebraicPauli

open scoped Matrix

namespace MathlibPlus.Open.Representation.Claim14798

noncomputable section

/--
Claim 14798.  The Ramanujan-tau coefficient is the coefficient of the
q-expansion of the modular discriminant.  On the mass-whitened coefficient
carrier, the two Hecke variables act by the two ordered matrix multiplications;
the Klingen kernel is the contracted matrix `X + κ P₋`.
-/
def normalizedOrderedLeftRightHeckeDefect_claim14798 : Prop :=
  let EndC := Matrix (Fin 2) (Fin 2) ℂ
  let tau : ℕ → ℂ := fun n =>
    (UpperHalfPlane.qExpansion 1 ModularForm.discriminant).coeff n
  let a : ℕ → ℂ := fun p => 1 + (p : ℂ) ^ 11
  let b : ℕ → ℂ := tau
  let g : ℕ → ℂ := fun p => a p - b p
  let T : ℕ → EndC := fun p => !![a p, 0; 0, b p]
  let iY : EndC := MathlibPlus.Open.AlgebraicPauli.iY
  let Pminus : EndC := MathlibPlus.Open.AlgebraicPauli.Pminus
  ∀ (κ : ℂ) (p : ℕ), Nat.Prime p →
    let Khat_Kl : EndC :=
      MathlibPlus.Open.AlgebraicPauli.X + κ • Pminus
    let Tτ : EndC → EndC := fun B => T p * B
    let Tw : EndC → EndC := fun B => B * T p
    let δ : EndC → EndC := fun B => Tτ B - Tw B
    g p ≠ 0 ∧
      T p * (κ • Pminus) = (κ • Pminus) * T p ∧
      δ Khat_Kl = g p • iY ∧
      (g p)⁻¹ • (Tτ Khat_Kl - Tw Khat_Kl) = iY ∧
      (g p)⁻¹ • (Tw Khat_Kl - Tτ Khat_Kl) = -iY

end

end MathlibPlus.Open.Representation.Claim14798
