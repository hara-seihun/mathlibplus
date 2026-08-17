import Mathlib

open Classical

namespace MathlibPlus.Open.Combinatorics.R0581

noncomputable section

/-- Union-closedness of a finite ordinary family of finite sets. -/
def unionClosed {V : Type*} [DecidableEq V]
    (F : Finset (Finset V)) : Prop :=
  ∀ A ∈ F, ∀ B ∈ F, A ∪ B ∈ F

/-- The complete inclusion-minimal nonempty members are the three displayed
pairwise-disjoint three-sets. -/
def threeMinimaSetup {V : Type*} [DecidableEq V]
    (F : Finset (Finset V)) (M : Fin 3 → Finset V) : Prop :=
  (∀ i : Fin 3, M i ∈ F ∧ (M i).card = 3) ∧
    (∀ i j : Fin 3, i ≠ j → Disjoint (M i) (M j)) ∧
      unionClosed F ∧
        (∀ A, A ∈ F → A.Nonempty →
          ((∀ B, B ∈ F → B.Nonempty → B ⊆ A → A ⊆ B) ↔
            ∃ i : Fin 3, A = M i))

/-- The nine-point minimum carrier. -/
def minimumCarrier {V : Type*} [DecidableEq V]
    (M : Fin 3 → Finset V) : Finset V :=
  M 0 ∪ M 1 ∪ M 2

/-- The image of the source family under adjoining the minimum carrier. -/
def carrierFibers {V : Type*} [DecidableEq V]
    (F : Finset (Finset V)) (K : Finset V) : Finset (Finset V) :=
  F.image (fun A => A ∪ K)

/-- The unweighted trace fiber over a carrier-fiber member. -/
def traceFiber {V : Type*} [DecidableEq V]
    (F : Finset (Finset V)) (K G : Finset V) : Finset (Finset V) :=
  (F.filter (fun A => A ∪ K = G)).image (fun A => A ∩ K)

/-- The local integer charge q(S)=2|S|-9. -/
def localCharge {V : Type*} [DecidableEq V]
    (S : Finset V) : ℤ :=
  2 * (S.card : ℤ) - 9

/-- Membership frequency of a coordinate in the ordinary family. -/
def coordinateFrequency {V : Type*} [DecidableEq V]
    (F : Finset (Finset V)) (x : V) : ℕ :=
  (F.filter (fun A => x ∈ A)).card

/-- The sum of local charges over all unweighted carrier fibers. -/
def globalCharge {V : Type*} [DecidableEq V]
    (F : Finset (Finset V)) (M : Fin 3 → Finset V) : ℤ :=
  let K := minimumCarrier M
  Finset.sum (carrierFibers F K)
    (fun G => Finset.sum (traceFiber F K G) localCharge)

/-- The local hypotheses used by the completion-only charge inequality. -/
def localTraceConditions {V : Type*} [DecidableEq V]
    (M : Fin 3 → Finset V) (H : Finset (Finset V)) : Prop :=
  let K := minimumCarrier M
  H.Nonempty ∧
    (∀ S ∈ H, S ⊆ K) ∧
      (∀ S ∈ H, S.Nonempty → ∃ i : Fin 3, M i ⊆ S) ∧
        (∀ S ∈ H, ∀ i : Fin 3, S ∪ M i ∈ H)

/-- The global fiber-charge identity and its nonnegative consequence. -/
def claim_22950 : Prop :=
  ∀ {V : Type*} [DecidableEq V]
    (F : Finset (Finset V)) (M : Fin 3 → Finset V),
    threeMinimaSetup F M →
      let K := minimumCarrier M
      globalCharge F M =
          2 * Finset.sum K (fun x => (coordinateFrequency F x : ℤ)) -
            9 * (F.card : ℤ) ∧
        0 ≤ globalCharge F M

/-- The nine-coordinate average and abundant-coordinate consequence. -/
def claim_22951 : Prop :=
  ∀ {V : Type*} [DecidableEq V]
    (F : Finset (Finset V)) (M : Fin 3 → Finset V),
    threeMinimaSetup F M →
      let K := minimumCarrier M
      2 * Finset.sum K (fun x => (coordinateFrequency F x : ℤ)) ≥
          9 * (F.card : ℤ) →
        K.card = 9 ∧
          Finset.sum K (fun x => (coordinateFrequency F x : ℚ)) / 9 ≥
              (F.card : ℚ) / 2 ∧
            ∃ x ∈ K, 2 * coordinateFrequency F x ≥ F.card

end

end MathlibPlus.Open.Combinatorics.R0581
