import Mathlib

namespace MathlibPlus.Open.Combinatorics.R1933Claim36326

open scoped BigOperators

private def memberFamily {α : Type*} {m : ℕ} [DecidableEq α]
    (F : Fin m → Finset α) : Finset (Finset α) :=
  (Finset.univ : Finset (Fin m)).image F

private def uniformDistinct {α : Type*} {m : ℕ} [DecidableEq α]
    (n : ℕ) (F : Fin m → Finset α) : Prop :=
  Function.Injective F ∧ ∀ i, (F i).card = n

private def coordinateSupport {α : Type*} {m : ℕ} [DecidableEq α]
    (F : Fin m → Finset α) (x : α) : Finset (Fin m) :=
  (Finset.univ : Finset (Fin m)).filter (fun i => x ∈ F i)

private noncomputable def groundCarrier {α : Type*} {m : ℕ}
    [Fintype α] [DecidableEq α] (F : Fin m → Finset α) : Finset α :=
  (Finset.univ : Finset (Fin m)).biUnion F

private noncomputable def supportPatterns {α : Type*} {m : ℕ}
    [Fintype α] [DecidableEq α] (F : Fin m → Finset α) :
    Finset (Finset (Fin m)) :=
  ((groundCarrier F).image (coordinateSupport F)).filter Finset.Nonempty

private def laminarPatterns {ι : Type*} [DecidableEq ι]
    (𝒮 : Finset (Finset ι)) : Prop :=
  ∀ S ∈ 𝒮, ∀ T ∈ 𝒮,
    S ⊆ T ∨ T ⊆ S ∨ Disjoint S T

private def strictSubset {ι : Type*} [DecidableEq ι]
    (S T : Finset ι) : Prop := S ⊆ T ∧ S ≠ T

private noncomputable def maximalProperChildren {ι : Type*}
    [DecidableEq ι] (𝒮 : Finset (Finset ι)) (S : Finset ι) :
    Finset (Finset ι) :=
  letI : DecidableEq (Finset ι) := Classical.decEq _
  letI : DecidablePred (fun T : Finset ι =>
    strictSubset T S ∧
      ∀ U ∈ 𝒮, strictSubset U S → T ⊆ U → U = T) := Classical.decPred _
  𝒮.filter (fun T =>
    strictSubset T S ∧
      ∀ U ∈ 𝒮, strictSubset U S → T ⊆ U → U = T)

private noncomputable def unionOfBlocks {ι : Type*} [DecidableEq ι]
    (𝒞 : Finset (Finset ι)) : Finset ι :=
  𝒞.biUnion id

private noncomputable def residualBlock {ι : Type*} [DecidableEq ι]
    (𝒮 : Finset (Finset ι)) (S : Finset ι) : Finset ι :=
  S \ unionOfBlocks (maximalProperChildren 𝒮 S)

private noncomputable def childBlocks {ι : Type*} [DecidableEq ι]
    (𝒮 : Finset (Finset ι)) (S : Finset ι) : Finset (Finset ι) :=
  maximalProperChildren 𝒮 S ∪
    if (residualBlock 𝒮 S).Nonempty then {residualBlock 𝒮 S} else ∅

private def kSunflowerFree {α : Type*} [DecidableEq α]
    (k : ℕ) (F : Finset (Finset α)) : Prop :=
  ∀ K : Finset (Finset α),
    K ⊆ F → K.card = k →
      ¬ ∃ C : Finset α,
        ∀ A ∈ K, ∀ B ∈ K, A ≠ B → A ∩ B = C

/-- Claim 36326: in the literal incidence-support forest of a distinct
n-uniform laminar family, k-sunflower-freeness forces every support node to
have fewer than k nonempty child blocks, equivalently branching at most
q = k - 1. -/
def claim36326 : Prop :=
  ∀ (α : Type*) [Fintype α] [DecidableEq α]
    (m n k : ℕ) (F : Fin m → Finset α),
    uniformDistinct n F →
      3 ≤ k →
        kSunflowerFree k (memberFamily F) →
          laminarPatterns (supportPatterns F) →
            ∀ S ∈ supportPatterns F,
              (childBlocks (supportPatterns F) S).card < k ∧
                (childBlocks (supportPatterns F) S).card ≤ k - 1

end MathlibPlus.Open.Combinatorics.R1933Claim36326
