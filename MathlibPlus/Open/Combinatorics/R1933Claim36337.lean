import Mathlib

namespace MathlibPlus.Open.Combinatorics.R1933Claim36337

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

private def unionClosedPatterns {ι : Type*} [DecidableEq ι]
    (𝒰 : Finset (Finset ι)) : Prop :=
  ∀ ⦃S T : Finset ι⦄, S ∈ 𝒰 → T ∈ 𝒰 → S ∪ T ∈ 𝒰

private noncomputable def layerUnion {ι : Type*} [DecidableEq ι]
    {c : ℕ} (𝒰 : Fin c → Finset (Finset ι)) : Finset (Finset ι) :=
  (Finset.univ : Finset (Fin c)).biUnion 𝒰

private def pairwiseDisjointLayers {ι : Type*} [DecidableEq ι]
    {c : ℕ} (𝒰 : Fin c → Finset (Finset ι)) : Prop :=
  ∀ i j : Fin c, i ≠ j → Disjoint (𝒰 i) (𝒰 j)

private def disjointSupportDecomposition {ι : Type*} [DecidableEq ι]
    {c : ℕ} (𝒮 𝓛 𝓑 𝓔 : Finset (Finset ι))
    (𝒰 : Fin c → Finset (Finset ι)) : Prop :=
  𝓛 ∪ 𝓑 ∪ layerUnion 𝒰 ∪ 𝓔 = 𝒮 ∧
    Disjoint 𝓛 𝓑 ∧
    Disjoint (𝓛 ∪ 𝓑) (layerUnion 𝒰) ∧
    Disjoint (𝓛 ∪ 𝓑 ∪ layerUnion 𝒰) 𝓔 ∧
    pairwiseDisjointLayers 𝒰

private def kSunflowerFree {α : Type*} [DecidableEq α]
    (k : ℕ) (F : Finset (Finset α)) : Prop :=
  ∀ K : Finset (Finset α),
    K ⊆ F → K.card = k →
      ¬ ∃ C : Finset α,
        ∀ A ∈ K, ∀ B ∈ K, A ≠ B → A ∩ B = C

/-- Claim 36337: under the actual laminar, bounded, union-closed, and
exceptional support decomposition, the hypothesis e ≤ beta n substitutes
into the full hybrid bound and raises the entire exponential base to n. -/
def claim36337 : Prop :=
  ∀ (α : Type*) [Fintype α] [DecidableEq α]
    (m n k D c e β : ℕ)
    (F : Fin m → Finset α)
    (𝓛 𝓑 𝓔 : Finset (Finset (Fin m)))
    (𝒰 : Fin c → Finset (Finset (Fin m))),
    uniformDistinct n F →
      3 ≤ k →
        kSunflowerFree k
          ((Finset.univ : Finset (Fin m)).image F) →
          disjointSupportDecomposition
            (supportPatterns F) 𝓛 𝓑 𝓔 𝒰 →
          laminarPatterns 𝓛 →
          (∀ S ∈ 𝓑, S.card ≤ D) →
          (∀ j : Fin c, unionClosedPatterns (𝒰 j)) →
          𝓔.card = e →
          e ≤ β * n →
            let q := k - 1
            (m : ℝ) ≤
              ((D : ℝ) * (q : ℝ) *
                (1 + ((D : ℝ) * (q : ℝ))⁻¹) ^
                  ((β : ℝ) + (c : ℝ) *
                    ((3 + Real.sqrt 5) / 2))) ^ n

end MathlibPlus.Open.Combinatorics.R1933Claim36337
