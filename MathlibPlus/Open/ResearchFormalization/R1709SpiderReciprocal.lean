import MathlibPlus.Open.Combinatorics.SpiderProfiles

namespace MathlibPlus.Open.ResearchFormalization.R1709SpiderReciprocal

noncomputable section

open MathlibPlus.Open.Combinatorics.SpiderProfiles

private noncomputable def reciprocalPolynomial
    (B : ℕ) (f : F2Poly) : F2Poly := by
  classical
  exact ∑ d ∈ f.support,
    Polynomial.C (f.coeff d) * Polynomial.X ^ (B - d)

private def singletonShifted (A : Fin 7 → ℕ) : F2Poly :=
  singletonSum ((tupleList A).map (fun a => a + 1))

private def KShifted (A : Fin 7 → ℕ) : F2Poly :=
  kPolynomial ((tupleList A).map (fun a => a + 1))

private def GShifted (A : Fin 7 → ℕ) : F2Poly :=
  KShifted A + 1 + Polynomial.X ^
    (Finset.sum Finset.univ (fun i => A i + 1))

private def foldedSingleton (A : Fin 7 → ℕ) : F2Poly := by
  let B := Finset.sum Finset.univ (fun i => A i + 1)
  exact Polynomial.X ^ 5 * singletonShifted A +
    reciprocalPolynomial B (singletonShifted A)

/-- Claim 33520: the seven-index complement identities, normalized folded
singleton identity, and its consequence for connected-profile collisions are
all stated on the reviewed characteristic-two spider-polynomial carrier. -/
def reciprocalSingletonReduction_claim33520 : Prop :=
  ∀ (A : Fin 7 → ℕ),
    sortedPositiveArms A →
    let bs := (tupleList A).map (fun a => a + 1)
    let B := Finset.sum Finset.univ (fun i => A i + 1)
    let S_A := singletonSum bs
    let K_A := kPolynomial bs
    let G_A := K_A + 1 + Polynomial.X ^ B
    let ρ := reciprocalPolynomial B
    elementarySymmetric 6 bs = ρ S_A ∧
      elementarySymmetric 5 bs = ρ (elementarySymmetric 2 bs) ∧
      elementarySymmetric 4 bs = ρ (elementarySymmetric 3 bs) ∧
      (Polynomial.X ^ 5 * (G_A + ρ G_A)) /
          ((1 + Polynomial.X) ^ 5) =
        Polynomial.X ^ 5 * S_A + ρ S_A
    ∧
    ∀ A' : Fin 7 → ℕ,
      sortedPositiveArms A' →
      connectedSubtreePolynomialModTwo A =
          connectedSubtreePolynomialModTwo A' →
        foldedSingleton A = foldedSingleton A'

end

end MathlibPlus.Open.ResearchFormalization.R1709SpiderReciprocal
