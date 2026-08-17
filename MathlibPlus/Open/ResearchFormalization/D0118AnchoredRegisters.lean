import Mathlib
import MathlibPlus.Open.LinearAlgebra.DeletionStableBoundedAnchor
import MathlibPlus.Open.MatroidBatch

namespace MathlibPlus.Open.ResearchFormalization.D0118

open MathlibPlus.Open

noncomputable section

/-- The exact outside-register behavior relative to the anchor span. -/
def outsideRegisterSemantics
    {ι F : Type*} [DecidableEq ι] [Field F]
    {d : ℕ} (v : ι → Fin d → F) (E A K : Finset ι)
    (hA : A ⊆ K) (hcard : A.card ≤ d - 1) : Prop :=
  let H_A := MathlibPlus.Open.MatroidBatch.anchorSpan d K A hA hcard v
  (outRegister v E A = OutsideCode.zero ↔
      ∀ k : ι, k ∈ E → v k ∈ H_A) ∧
    (∀ e : ι,
      outRegister v E A = OutsideCode.one e ↔
        e ∈ E ∧ v e ∉ H_A ∧
          ∀ k : ι, k ∈ E → v k ∉ H_A → k = e) ∧
      (outRegister v E A = OutsideCode.many ↔
        ∃ k l : ι,
          k ∈ E ∧ l ∈ E ∧
            v k ∉ H_A ∧ v l ∉ H_A ∧ k ≠ l)

/-- Claim 5618: the outside register is the zero/one/many commutative fold
of exactly the labels whose stored vectors lie outside `H_A`. -/
def claim5618
    {ι F : Type*} [DecidableEq ι] [Field F]
    (d : ℕ) (K E A : Finset ι) (v : ι → Fin d → F)
    (_hE : E ⊆ K) (hA : A ⊆ K) (hcard : A.card ≤ d - 1) : Prop :=
  outsideRegisterSemantics v E A K hA hcard

/-- Claim 5619: the bounded anchor set together with `e` is an anchored
coloop witness exactly through the singleton outside code. -/
def claim5619
    {ι F : Type*} [DecidableEq ι] [Field F]
    (d : ℕ) (K E A : Finset ι) (v : ι → Fin d → F)
    (e : ι) (_hE : E ⊆ K) : Prop :=
  A ⊆ K.erase e ∧
      A.card ≤ d - 1 ∧
        outRegister v E A = OutsideCode.one e

end
end MathlibPlus.Open.ResearchFormalization.D0118
