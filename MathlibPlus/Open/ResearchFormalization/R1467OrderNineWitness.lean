import MathlibPlus.Open.ResearchFormalization.R1467.CapCompanion

namespace MathlibPlus.Open.ResearchFormalization.R1467OrderNineWitness

noncomputable section

open MathlibPlus.Open.ResearchFormalization.R1467

/-- Claim 37529: the exact primitive order-nine witness has no `x₁` part and
maps to zero under the rank-one component-count toric specialization. -/
def exactOrderNineWitness_claim37529 : Prop :=
  let W : MvPolynomial ℕ ℤ := witnessW
  let e33 : ℕ →₀ ℕ := Finsupp.single 3 3
  let e234 : ℕ →₀ ℕ :=
    Finsupp.single 2 1 + Finsupp.single 3 1 + Finsupp.single 4 1
  let e225 : ℕ →₀ ℕ := Finsupp.single 2 2 + Finsupp.single 5 1
  let e45 : ℕ →₀ ℕ := Finsupp.single 4 1 + Finsupp.single 5 1
  let e36 : ℕ →₀ ℕ := Finsupp.single 3 1 + Finsupp.single 6 1
  let U : MvPolynomial (Fin 2) ℤ := MvPolynomial.X 0
  let V : MvPolynomial (Fin 2) ℤ := MvPolynomial.X 1
  let φ : MvPolynomial ℕ ℤ →+* MvPolynomial (Fin 2) ℤ :=
    MvPolynomial.eval₂Hom (Int.castRingHom _) (fun k => U * V ^ (k + 1))
  MvPolynomial.pderiv 1 W = 0 ∧
    (∀ m ∈ W.support, m.sum (fun i a => i * a) = 9) ∧
    (∀ z : ℤ, (∀ m, z ∣ MvPolynomial.coeff m W) →
      z = 1 ∨ z = -1) ∧
    MvPolynomial.coeff e33 W = 1 ∧
    MvPolynomial.coeff e234 W = -2 ∧
    MvPolynomial.coeff e225 W = 1 ∧
    MvPolynomial.coeff e45 W = -1 ∧
    MvPolynomial.coeff e36 W = 1 ∧
    (1 - 2 + 1 : ℤ) = 0 ∧
    (-1 + 1 : ℤ) = 0 ∧
    φ W = 0

end

end MathlibPlus.Open.ResearchFormalization.R1467OrderNineWitness
