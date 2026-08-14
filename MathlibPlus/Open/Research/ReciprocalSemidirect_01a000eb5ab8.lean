import Mathlib

namespace MathlibPlus.Open.ResearchFormalizationBatch

/-- Claim 25393, with the displayed common denominator and numerator made
explicit.  The ordinary polynomial lcm is normalized by its constant term,
matching the claim's `Q(0) = 1` convention. -/
def lcmNumeratorReciprocalRelation : Prop := by
  classical
  exact
    ∀ {K : Type*} [Field K] (s : ℕ)
      (Q₀ : Fin s → Polynomial K) (r : Fin s → K),
      (∀ i, Polynomial.eval 0 (Q₀ i) = 1) →
      (∀ ⦃i j⦄, i ≠ j → Q₀ i ≠ Q₀ j) →
      (∀ i, r i ≠ 0) →
      let L := (Finset.univ : Finset (Fin s)).lcm Q₀
      let Q := Polynomial.C ((Polynomial.eval 0 L)⁻¹) * L
      let P := ∑ i, Polynomial.C (r i) * (Q / Q₀ i)
      Polynomial.eval 0 Q = 1 ∧
        (∑ i,
            (algebraMap (Polynomial K) (RatFunc K)) (Polynomial.C (r i)) /
              (algebraMap (Polynomial K) (RatFunc K)) (Q₀ i)).num.trailingDegree =
          P.trailingDegree

/-- Claim 25396: a vanishing cleared numerator forces two maximal
multiplicity denominators for every irreducible common factor. -/
def exactReciprocalRelationsShareMaximalFactors : Prop := by
  classical
  exact
    ∀ {K : Type*} [Field K] (s : ℕ)
      (Q₀ : Fin s → Polynomial K) (r : Fin s → K),
      (∀ i, Polynomial.eval 0 (Q₀ i) = 1) →
      (∀ ⦃i j⦄, i ≠ j → Q₀ i ≠ Q₀ j) →
      (∀ i, r i ≠ 0) →
      let L := (Finset.univ : Finset (Fin s)).lcm Q₀
      let Q := Polynomial.C ((Polynomial.eval 0 L)⁻¹) * L
      let P := ∑ i, Polynomial.C (r i) * (Q / Q₀ i)
      P = 0 →
        ∀ (f : Polynomial K), Irreducible f → f ∣ Q →
          ∀ m : ℕ,
            (∃ i, multiplicity f (Q₀ i) = m) →
            (∀ i, multiplicity f (Q₀ i) ≤ m) →
            ∃ i j, i ≠ j ∧ multiplicity f (Q₀ i) = m ∧
              multiplicity f (Q₀ j) = m

/-- Claim 27427: the stated multiplication on the one-dimensional additive
semidirect product of a finite field by a finite group. -/
def oneDimensionalFiniteFieldSemidirectProduct : Prop :=
  ∀ (F : Type*) [Fintype F] [Field F]
    (H : Type*) [Fintype H] [Group H] (χ : H →* Fˣ),
    ∃ inst : Group (F × H),
      ∀ x y : F × H,
        inst.mul x y =
          (x.1 + (χ x.2 : F) * y.1, x.2 * y.2)

end MathlibPlus.Open.ResearchFormalizationBatch
