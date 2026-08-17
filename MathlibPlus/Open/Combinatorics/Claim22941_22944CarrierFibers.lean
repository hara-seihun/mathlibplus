import Mathlib

namespace MathlibPlus.Open.Combinatorics

private def carrierUnion {V : Type*} [DecidableEq V]
    (M₁ M₂ M₃ : Finset V) : Finset V :=
  M₁ ∪ M₂ ∪ M₃

private def carrierImage {V : Type*} [DecidableEq V]
    (F : Finset (Finset V)) (M₁ M₂ M₃ : Finset V) : Finset (Finset V) :=
  F.image (fun A => A ∪ carrierUnion M₁ M₂ M₃)

private def sourceFiber {V : Type*} [DecidableEq V]
    (F : Finset (Finset V)) (M₁ M₂ M₃ G : Finset V) : Finset (Finset V) :=
  F.filter (fun A => A ∪ carrierUnion M₁ M₂ M₃ = G)

private def traceFiber {V : Type*} [DecidableEq V]
    (F : Finset (Finset V)) (M₁ M₂ M₃ G : Finset V) : Finset (Finset V) :=
  (sourceFiber F M₁ M₂ M₃ G).image
    (fun A => A ∩ carrierUnion M₁ M₂ M₃)

/-- The finite distinct-set family and the exact three-block minimum data used
by the carrier-fiber claims.  This repeats the reviewed hypotheses of claim
22940, including its complete nonempty-minimum characterization. -/
private def threeDisjointTripleMinimaData {V : Type*} [DecidableEq V]
    (F : Finset (Finset V)) (M₁ M₂ M₃ : Finset V) : Prop :=
  M₁ ∈ F ∧ M₂ ∈ F ∧ M₃ ∈ F ∧
    M₁.card = 3 ∧ M₂.card = 3 ∧ M₃.card = 3 ∧
    (∀ x, x ∈ M₁ → x ∉ M₂) ∧
    (∀ x, x ∈ M₁ → x ∉ M₃) ∧
    (∀ x, x ∈ M₂ → x ∉ M₃) ∧
    (∀ A, A ∈ F → ∀ B, B ∈ F → A ∪ B ∈ F) ∧
    (∀ A, A ∈ F → A.Nonempty →
      ((∀ B, B ∈ F → B.Nonempty → B ⊆ A → A ⊆ B) ↔
        A = M₁ ∨ A = M₂ ∨ A = M₃))

/-- Claim 22941: with the exact ambient family of finite sets, the carrier is
`M₁ ∪ M₂ ∪ M₃`, and each image label has the stated trace fiber. -/
def ninePointCarrierAndFibers_claim22941 : Prop :=
  ∀ (V : Type*) [DecidableEq V]
    (F : Finset (Finset V)) (M₁ M₂ M₃ : Finset V),
    let K := carrierUnion M₁ M₂ M₃
    let carriers := F.image (fun A => A ∪ K)
    ∀ G, G ∈ carriers →
      ∀ S : Finset V,
        S ∈ traceFiber F M₁ M₂ M₃ G ↔
          ∃ A : Finset V,
            A ∈ F ∧ A ∪ K = G ∧ A ∩ K = S

/-- Claim 22942: the source fibers partition the distinct finite family, and
all trace fibers are nonempty, contain the carrier, are union-closed, and are
closed under adjoining each of the three minimum blocks. -/
def exactCarrierFiberReduction_claim22942 : Prop :=
  ∀ (V : Type*) [DecidableEq V]
    (F : Finset (Finset V)) (M₁ M₂ M₃ : Finset V),
    threeDisjointTripleMinimaData F M₁ M₂ M₃ →
    let K := carrierUnion M₁ M₂ M₃
    let carriers := carrierImage F M₁ M₂ M₃
    let fibers := fun G => sourceFiber F M₁ M₂ M₃ G
    let traces := fun G => traceFiber F M₁ M₂ M₃ G
    F = carriers.biUnion fibers ∧
      ∀ G, G ∈ carriers →
        (traces G).Nonempty ∧
          K ∈ traces G ∧
          (∀ S ∈ traces G, ∀ T ∈ traces G,
            S ∪ T ∈ traces G) ∧
          (∀ S ∈ traces G,
            S ∪ M₁ ∈ traces G ∧
              S ∪ M₂ ∈ traces G ∧
                S ∪ M₃ ∈ traces G)

/-- Claim 22943: every nonempty trace contains one of the complete minimum
blocks fixed by the family-minimum hypotheses. -/
def everyNonemptyTraceContainsCompleteMinimumBlock_claim22943 : Prop :=
  ∀ (V : Type*) [DecidableEq V]
    (F : Finset (Finset V)) (M₁ M₂ M₃ : Finset V),
    threeDisjointTripleMinimaData F M₁ M₂ M₃ →
    let K := carrierUnion M₁ M₂ M₃
    let carriers := F.image (fun A => A ∪ K)
    ∀ G, G ∈ carriers →
      ∀ S, S ∈ traceFiber F M₁ M₂ M₃ G → S.Nonempty →
        M₁ ⊆ S ∨ M₂ ⊆ S ∨ M₃ ⊆ S

/-- Claim 22944: an empty trace comes from the empty source member and its
carrier label is the base label `K`. -/
def emptyTraceOnlyBaseFiber_claim22944 : Prop :=
  ∀ (V : Type*) [DecidableEq V]
    (F : Finset (Finset V)) (M₁ M₂ M₃ : Finset V),
    threeDisjointTripleMinimaData F M₁ M₂ M₃ →
    let K := carrierUnion M₁ M₂ M₃
    let carriers := F.image (fun A => A ∪ K)
    ∀ G, G ∈ carriers →
      (∅ : Finset V) ∈ traceFiber F M₁ M₂ M₃ G →
        (∅ : Finset V) ∈ F ∧ G = K

end MathlibPlus.Open.Combinatorics
