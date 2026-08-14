import Mathlib

namespace MathlibPlus.Open.Combinatorics.SpiderProfiles

open scoped BigOperators
open Polynomial

noncomputable section

abbrev F2Poly := Polynomial (ZMod 2)

 def singletonSum (bs : List ℕ) : F2Poly :=
  bs.foldr (fun b p => Polynomial.X ^ b + p) 0

 def productFactors (bs : List ℕ) : F2Poly :=
  bs.foldr (fun b p => (1 + Polynomial.X ^ b) * p) 1

 def kPolynomial (bs : List ℕ) : F2Poly :=
  productFactors bs + (1 + Polynomial.X) ^ 5 * singletonSum bs

 def armPolynomial (a : ℕ) : Polynomial ℕ :=
  Finset.sum (Finset.Icc 1 a) (fun k => Polynomial.C (a - k + 1) * Polynomial.X ^ k)

 def armIntervalPolynomial (a : ℕ) : Polynomial ℕ :=
  Finset.sum (Finset.range (a + 1)) (fun k => Polynomial.X ^ k)

 def spiderFormula (A : Fin 7 → ℕ) : Polynomial ℕ :=
  (∑ i : Fin 7, armPolynomial (A i)) +
    Polynomial.X * ∏ i : Fin 7, armIntervalPolynomial (A i)

 abbrev SpiderVertex (A : Fin 7 → ℕ) :=
  Sum Unit (Sigma (fun i : Fin 7 => Fin (A i)))

 def spiderEdge (A : Fin 7 → ℕ) : SpiderVertex A → SpiderVertex A → Prop
  | Sum.inl _, Sum.inl _ => False
  | Sum.inl _, Sum.inr ⟨_, j⟩ => j.val = 0
  | Sum.inr ⟨_, j⟩, Sum.inl _ => j.val = 0
  | Sum.inr ⟨i, j⟩, Sum.inr ⟨i', j'⟩ =>
      i = i' ∧ (j.val + 1 = j'.val ∨ j'.val + 1 = j.val)

 def connectedSubset (A : Fin 7 → ℕ) (S : Finset (SpiderVertex A)) : Prop :=
  S.Nonempty ∧
    ∀ v, v ∈ S → ∀ w, w ∈ S →
      Relation.ReflTransGen
        (fun x y => x ∈ S ∧ y ∈ S ∧ spiderEdge A x y) v w

 def connectedSubtreePolynomial (A : Fin 7 → ℕ) : Polynomial ℕ := by
  classical
  exact Finset.sum (Finset.univ.powerset.filter (connectedSubset A))
    (fun S => Polynomial.X ^ S.card)

 def connectedSubtreePolynomialModTwo (A : Fin 7 → ℕ) : F2Poly := by
  classical
  exact Finset.sum (Finset.univ.powerset.filter (connectedSubset A))
    (fun S => Polynomial.X ^ S.card)

 def tupleList (A : Fin 7 → ℕ) : List ℕ := Finset.univ.toList.map A

 def commonTerm (m : ℕ) : F2Poly :=
  (1 + Polynomial.X) ^ 5 *
    (Polynomial.C ((m % 2 : ℕ) : ZMod 2) * Polynomial.X +
      Polynomial.C (((m + 1) % 2 : ℕ) : ZMod 2) * Polynomial.X ^ 2)

 def elementarySymmetric : ℕ → List ℕ → F2Poly
  | 0, _ => 1
  | _ + 1, [] => 0
  | j + 1, b :: bs =>
      elementarySymmetric (j + 1) bs +
        Polynomial.X ^ b * elementarySymmetric j bs

 def subsetSums (b : Fin 7 → ℕ) (r : ℕ) : List ℕ :=
  ((Finset.univ.powerset.filter
      (fun s : Finset (Fin 7) => s.card = r)).toList.map
    (fun s => Finset.sum s b))

 def singletonShiftOccurrences (b : Fin 7 → ℕ) : List ℕ :=
  Finset.univ.toList.flatMap (fun i => [b i + 1, b i + 4, b i + 5])

 def varyingSupportOccurrences (b : Fin 7 → ℕ) : List ℕ :=
  (List.range 5).flatMap (fun r => subsetSums b (r + 2)) ++
    singletonShiftOccurrences b

 def evenMultiplicity (xs : List ℕ) : Prop :=
  ∀ n, Even (xs.count n)

 def sortedPositiveArms (A : Fin 7 → ℕ) : Prop :=
  (∀ i, 0 < A i) ∧ ∀ i j, i ≤ j → A i ≤ A j

 def claim33516 : Prop :=
  ∀ A : Fin 7 → ℕ, sortedPositiveArms A →
    connectedSubtreePolynomial A = spiderFormula A

 def claim33518 : Prop :=
  ∀ A : Fin 7 → ℕ, sortedPositiveArms A →
    (1 + Polynomial.X) ^ 7 * connectedSubtreePolynomialModTwo A =
      commonTerm (Finset.sum Finset.univ A) +
        Polynomial.X * kPolynomial ((tupleList A).map (fun a => a + 1))

 def profileFromShifted (b : Fin 7 → ℕ) : F2Poly :=
  connectedSubtreePolynomialModTwo (fun i => b i - 1)

 def claim33519 : Prop :=
  (∀ bs : List ℕ, bs.length = 7 →
    kPolynomial bs =
      1 + (Polynomial.X + Polynomial.X ^ 4 + Polynomial.X ^ 5) * singletonSum bs +
        elementarySymmetric 2 bs + elementarySymmetric 3 bs +
        elementarySymmetric 4 bs + elementarySymmetric 5 bs +
        elementarySymmetric 6 bs + Polynomial.X ^ bs.sum) ∧
  (∀ b : Fin 7 → ℕ, (varyingSupportOccurrences b).length = 140) ∧
  (∀ b b' : Fin 7 → ℕ,
    (∀ i, 1 < b i) → (∀ i, 1 < b' i) →
    Finset.sum Finset.univ b = Finset.sum Finset.univ b' →
      (profileFromShifted b = profileFromShifted b' ↔
        evenMultiplicity (varyingSupportOccurrences b ++
          varyingSupportOccurrences b')) ∧
      (kPolynomial (tupleList b) = kPolynomial (tupleList b') ↔
        evenMultiplicity (varyingSupportOccurrences b ++
          varyingSupportOccurrences b'))) ∧
  (∀ b b' : Fin 7 → ℕ,
    (varyingSupportOccurrences b ++ varyingSupportOccurrences b').length = 280)

 def g₁Left (u v : ℕ) : List ℕ := [2, 2, u, u, u, u, 4 * v - 1]
 def g₁Right (u v : ℕ) : List ℕ := [2, 2, v, v, v, v, 4 * u - 1]
 def g₂Left (c u v : ℕ) : List ℕ := [c, u, u, u, u, 2 * v, 2 * v]
 def g₂Right (c u v : ℕ) : List ℕ := [c, v, v, v, v, 2 * u, 2 * u]
 def g₃Left (u : ℕ) : List ℕ := [4, u, u, u, u, 4 * u, 16 * u - 1]
 def g₃Right (u : ℕ) : List ℕ := [4, 2 * u, 2 * u, 4 * u, 4 * u, 4 * u, 8 * u - 1]

 def sameMultiset (xs ys : List ℕ) : Prop := Multiset.ofList xs = Multiset.ofList ys
 def totalWeight (xs : List ℕ) : ℕ := xs.sum

 def exchangeCollision : Prop :=
  ∀ u v : ℕ, 2 ≤ u → 2 ≤ v → u ≠ v →
    totalWeight (g₁Left u v) = totalWeight (g₁Right u v) ∧
    kPolynomial (g₁Left u v) = kPolynomial (g₁Right u v) ∧
    ¬ sameMultiset (g₁Left u v) (g₁Right u v)

 def commonArmLiftCollision : Prop :=
  ∀ c u v : ℕ, 2 ≤ c → 2 ≤ u → 2 ≤ v → u ≠ v →
    totalWeight (g₂Left c u v) = totalWeight (g₂Right c u v) ∧
    kPolynomial (g₂Left c u v) = kPolynomial (g₂Right c u v) ∧
    ¬ sameMultiset (g₂Left c u v) (g₂Right c u v)

 def frobeniusCollision : Prop :=
  ∀ u : ℕ, 2 ≤ u →
    totalWeight (g₃Left u) = totalWeight (g₃Right u) ∧
    kPolynomial (g₃Left u) = kPolynomial (g₃Right u) ∧
    ¬ sameMultiset (g₃Left u) (g₃Right u)

 def sortedPositiveSeven (xs : List ℕ) : Prop :=
  xs.length = 7 ∧ xs.Pairwise (· ≤ ·) ∧ ∀ x ∈ xs, 0 < x

 def familyG₁Pair (xs ys : List ℕ) : Prop :=
  ∃ u v : ℕ,
    2 ≤ u ∧ 2 ≤ v ∧ u ≠ v ∧
      ((sameMultiset xs (g₁Left u v) ∧ sameMultiset ys (g₁Right u v)) ∨
       (sameMultiset xs (g₁Right u v) ∧ sameMultiset ys (g₁Left u v)))

 def familyG₂Pair (xs ys : List ℕ) : Prop :=
  ∃ c u v : ℕ,
    2 ≤ c ∧ 2 ≤ u ∧ 2 ≤ v ∧ u ≠ v ∧
      ((sameMultiset xs (g₂Left c u v) ∧ sameMultiset ys (g₂Right c u v)) ∨
       (sameMultiset xs (g₂Right c u v) ∧ sameMultiset ys (g₂Left c u v)))

 def familyG₃Pair (xs ys : List ℕ) : Prop :=
  ∃ u : ℕ,
    2 ≤ u ∧
      ((sameMultiset xs (g₃Left u) ∧ sameMultiset ys (g₃Right u)) ∨
       (sameMultiset xs (g₃Right u) ∧ sameMultiset ys (g₃Left u)))

 def exactlyOne (p q r : Prop) : Prop :=
  (p ∧ ¬ q ∧ ¬ r) ∨ (¬ p ∧ q ∧ ¬ r) ∨ (¬ p ∧ ¬ q ∧ r)

 def claim33522 : Prop := exchangeCollision

 def claim33523 : Prop := commonArmLiftCollision

 def claim33524 : Prop := frobeniusCollision

 def claim33525 : Prop :=
  (∀ xs ys : List ℕ,
    sortedPositiveSeven xs → sortedPositiveSeven ys → xs ≠ ys →
    totalWeight xs = totalWeight ys →
    (kPolynomial xs = kPolynomial ys ↔
      exactlyOne (familyG₁Pair xs ys) (familyG₂Pair xs ys) (familyG₃Pair xs ys))) ∧
  exchangeCollision ∧ commonArmLiftCollision ∧ frobeniusCollision

end
end MathlibPlus.Open.Combinatorics.SpiderProfiles
