import Mathlib

namespace MathlibPlus.Open.MatroidBatch

open scoped BigOperators

noncomputable section

/-- A block column is exposed alone by a row functional. -/
def exposedByRowFunctional {F ι : Type*} [Field F] [DecidableEq ι]
    (d : ℕ) (E : Finset ι) (v : ι → Fin d → F) (k : ι) : Prop :=
  k ∈ E ∧
    ∃ α : (Fin d → F) →ₗ[F] F,
      α (v k) ≠ 0 ∧ ∀ ℓ ∈ E, ℓ ≠ k → α (v ℓ) = 0

/-- The represented-matroid coloop test for a finite vector family. -/
def coloopLabel {F ι : Type*} [Field F] [DecidableEq ι]
    (d : ℕ) (E : Finset ι) (v : ι → Fin d → F) (k : ι) : Prop :=
  k ∈ E ∧
    v k ∉ Submodule.span F (v '' ((↑(E.erase k) : Set ι)))

/-- Exact equivalence between row exposure and the span coloop test. -/
def exposureIsColoopIff {F ι : Type*} [Field F] [DecidableEq ι]
    (d : ℕ) (E : Finset ι) (v : ι → Fin d → F) (k : ι) : Prop :=
  exposedByRowFunctional d E v k ↔ coloopLabel d E v k

/-- The coloop set in the register, including its labels and vectors. -/
def coloopCoreC {F ι : Type*} [Field F] [DecidableEq ι]
    (d : ℕ) (E : Finset ι) (v : ι → Fin d → F) :
    Set (ι × (Fin d → F)) :=
  {p | p.1 ∈ E ∧ p.2 = v p.1 ∧ coloopLabel d E v p.1}

/-- The span of all non-coloop vectors. -/
def coloopCoreN {F ι : Type*} [Field F] [DecidableEq ι]
    (d : ℕ) (E : Finset ι) (v : ι → Fin d → F) :
    Submodule F (Fin d → F) :=
  Submodule.span F
    {x | ∃ k ∈ E, ¬ coloopLabel d E v k ∧ x = v k}

/-- The coloop-core register `(N(E), C(E))`. -/
def coloopCoreRegister {F ι : Type*} [Field F] [DecidableEq ι]
    (d : ℕ) (E : Finset ι) (v : ι → Fin d → F) :
    Submodule F (Fin d → F) × Set (ι × (Fin d → F)) :=
  (coloopCoreN d E v, coloopCoreC d E v)

/-- Deletion of a set of labels from a finite family. -/
def deleteLabels {ι : Type*} [DecidableEq ι]
    (E : Finset ι) (X : Set ι) : Finset ι := by
  classical
  exact E.filter (fun k => k ∉ X)

/-- The complete response register after a puncture `X ⊆ B`. -/
def punctureResponse {F ι : Type*} [Field F] [DecidableEq ι]
    (d : ℕ) (E : Finset ι) (v : ι → Fin d → F) (B : Set ι) :
    {X : Set ι // X ⊆ B} →
      Submodule F (Fin d → F) × Set (ι × (Fin d → F)) :=
  fun X => coloopCoreRegister d (deleteLabels E X.1) v

/-- Deletion-stable context equivalence relative to `B`. -/
def punctureEquivalent {F ι : Type*} [Field F] [DecidableEq ι]
    (d : ℕ) (E E' : Finset ι) (v v' : ι → Fin d → F) (B : Set ι) : Prop :=
  ∀ X : {X : Set ι // X ⊆ B},
    punctureResponse d E v B X = punctureResponse d E' v' B X

/-- The static register comparison, the `X = ∅` instance of the response. -/
def staticRegisterEqual {F ι : Type*} [Field F] [DecidableEq ι]
    (d : ℕ) (E E' : Finset ι) (v v' : ι → Fin d → F) : Prop :=
  coloopCoreRegister d E v = coloopCoreRegister d E' v'

/-- The span of the exactly stored anchor vectors. -/
def anchorSpan {F ι : Type*} [Field F] [DecidableEq ι]
    (d : ℕ) (K A : Finset ι) (hA : A ⊆ K) (hcard : A.card ≤ d - 1)
    (v : ι → Fin d → F) :
    Submodule F (Fin d → F) :=
  Submodule.span F (v '' ((↑A : Set ι)))

/-- A target is a coloop after deleting `X`. -/
def isColoopAfterDeletion {F ι : Type*} [Field F] [DecidableEq ι]
    (d : ℕ) (E : Finset ι) (v : ι → Fin d → F) (e : ι) (X : Finset ι) : Prop :=
  coloopLabel d (E.filter (fun k => k ∉ (↑X : Set ι))) v e

/-- The inclusion-minimal activation sets for a fixed target. -/
def minimalActivationFamily {F ι : Type*} [Field F] [DecidableEq ι]
    (d : ℕ) (E : Finset ι) (v : ι → Fin d → F) (e : ι) : Set (Finset ι) :=
  {X | X ⊆ E.erase e ∧ isColoopAfterDeletion d E v e X ∧
    ∀ Y, Y ⊆ E.erase e → isColoopAfterDeletion d E v e Y → ¬ Y ⊂ X}

end

end MathlibPlus.Open.MatroidBatch
