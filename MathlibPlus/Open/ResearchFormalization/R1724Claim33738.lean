import MathlibPlus.Open.ResearchFormalization.R1724TopStratum

open scoped BigOperators

namespace MathlibPlus.Open.ResearchFormalization.R1724Claim33738

attribute [local instance] Classical.decEq Classical.propDecidable

noncomputable section

open MathlibPlus.Open.ResearchFormalizationBatch

abbrev XPoly33738 := MvPolynomial ℕ ℚ

def uPoly33738 {d : ℕ} (T : SimpleGraph (Fin d)) : XPoly33738 :=
  MvPolynomial.map (Int.castRingHom ℚ)
    (forestUPolynomial T)

def xOneFree33738 (P : XPoly33738) : Prop :=
  MvPolynomial.pderiv 1 P = 0

def cutTowerCombination33738 (d : ℕ)
    (ν : SimpleGraph (Fin d) →₀ ℤ) : XPoly33738 :=
  ∑ T ∈ ν.support, (ν T : ℚ) • uPoly33738 T

def blockNumberCoefficientSum33738
    (d ℓ : ℕ) (P : XPoly33738) : ℚ :=
  ∑ m ∈ P.support.filter (fun m =>
    m 1 = 0 ∧
      m.sum (fun i e => i * e) = d ∧
        m.sum (fun _ e => e) = ℓ),
    MvPolynomial.coeff m P

/-- Claim 33738: every integer cut-tower combination supported on unrooted
order-`d` trees whose rational polynomial is `x₁`-free has zero coefficient
sum in every fixed block-number class of `x₁`-free partitions of `d`. -/
def claim33738 : Prop :=
  ∀ (d : ℕ) (ν : SimpleGraph (Fin d) →₀ ℤ),
    (∀ T : SimpleGraph (Fin d), ν T ≠ 0 → T.IsTree) →
    let f := cutTowerCombination33738 d ν
    xOneFree33738 f →
      ∀ ℓ : ℕ, blockNumberCoefficientSum33738 d ℓ f = 0

end
end MathlibPlus.Open.ResearchFormalization.R1724Claim33738
