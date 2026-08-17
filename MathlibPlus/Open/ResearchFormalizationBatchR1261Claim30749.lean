import Mathlib

open scoped LinearAlgebra.Projectivization

noncomputable section

namespace MathlibPlus.Open.ResearchFormalizationBatchR1261Claim30749

/-- The two uniform projective action types in the primitive local layer. -/
inductive ProjectiveActionKind
  | point
  | hyperplane

/-- A projective point, or a projective point of the dual space (a hyperplane). -/
def projectiveBlock (K : Type u) [Field K] (d : ℕ) :
    ProjectiveActionKind → Type u
  | .point => ℙ K (Fin d → K)
  | .hyperplane => ℙ K (Module.Dual K (Fin d → K))

/-- The supported-coordinate sizes supplied by the primitive local layer. -/
def allowableSupportSize {I : Type*} [Finite I] (supported : Set I) : Prop :=
  Nat.card {i : I // i ∈ supported} = 1 ∨
    Nat.card {i : I // i ∈ supported} = 4 ∨
      Nat.card {i : I // i ∈ supported} = 12

/-- Laws for the displayed action on each supported block. -/
def blockActionLaws {T I : Type*} [Group T] (B : I → Type*)
    (action : ∀ i : I, T → B i → B i) : Prop :=
  ∀ i : I,
    (∀ x : B i, action i 1 x = x) ∧
      ∀ g h : T, ∀ x : B i,
        action i (g * h) x = action i g (action i h x)

/-- The common projective action transported to every supported block. -/
def equivariantBlockFamily {K T I : Type*} [Field K] [Group T]
    (d : ℕ) (kind : ProjectiveActionKind)
    [MulAction T (projectiveBlock K d kind)] (B : I → Type*)
    (supported : Set I) (action : ∀ i : I, T → B i → B i)
    (identification : ∀ i : I, projectiveBlock K d kind ≃ B i) : Prop :=
  ∀ i : I, i ∈ supported → ∀ t : T, ∀ p : projectiveBlock K d kind,
    action i t (identification i p) = identification i (t • p)

/-- A point stabilizer section on a family of supported blocks. -/
def canonicalFixedSection {K T I : Type*} [Field K] [Group T]
    (d : ℕ) (kind : ProjectiveActionKind)
    [MulAction T (projectiveBlock K d kind)] (B : I → Type*)
    (supported : Set I) (action : ∀ i : I, T → B i → B i)
    (identification : ∀ i : I, projectiveBlock K d kind ≃ B i) : Prop :=
  ∀ p : projectiveBlock K d kind, ∀ i : I, i ∈ supported →
    (∀ y : B i,
      ((∀ t : T, t • p = p → action i t y = y) ↔
        y = identification i p)) ∧
      (∀ y z : B i,
        y ≠ identification i p → z ≠ identification i p →
          ∃ t : T, t • p = p ∧ action i t y = z)

/--
Claim 30749: for one uniform projective-point or hyperplane action, the
point stabilizer of the simple two-transitive factor fixes exactly the
transported point on every supported block and is transitive on its
complement.
-/
def claim30749 : Prop :=
  ∀ (K : Type*) [Field K] [Fintype K] (d : ℕ)
    (kind : ProjectiveActionKind) (T : Type*) [Group T]
    [MulAction T (projectiveBlock K d kind)],
    IsSimpleGroup T →
      MulAction.IsMultiplyPretransitive T (projectiveBlock K d kind) 2 →
        ∀ (I : Type*) [Fintype I] (B : I → Type*)
          (supported : Set I)
          (action : ∀ i : I, T → B i → B i)
          (identification : ∀ i : I, projectiveBlock K d kind ≃ B i),
          allowableSupportSize supported →
            blockActionLaws B action →
              equivariantBlockFamily d kind B supported action identification →
                canonicalFixedSection d kind B supported action identification

end MathlibPlus.Open.ResearchFormalizationBatchR1261Claim30749
