import MathlibPlus.Basic

namespace MathlibPlus.Algebra

/-!
Formalization of claim 26480.  The unrooted component symbols are represented
by the variables of `MvPolynomial ℕ R`; the target has variables `z` and `x₁`
(`Fin 2`), and `s=z+x₁`.  `eval₂Hom` supplies the stipulated multiplicative
extension of `x_k ↦ a_k s^k`.
-/

noncomputable def componentOrderSubstitution {R : Type*} [CommSemiring R]
    (a : ℕ → R) :
    MvPolynomial ℕ R →+* MvPolynomial (Fin 2) R :=
  let s : MvPolynomial (Fin 2) R := MvPolynomial.X 0 + MvPolynomial.X 1
  MvPolynomial.eval₂Hom (MvPolynomial.C : R →+* MvPolynomial (Fin 2) R)
    (fun k => MvPolynomial.C (a k) * s ^ k)

end MathlibPlus.Algebra
