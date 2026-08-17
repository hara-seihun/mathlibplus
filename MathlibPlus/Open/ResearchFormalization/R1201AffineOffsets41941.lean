import MathlibPlus.Open.ResearchFormalization.R1144DistinctLabels

namespace MathlibPlus.Open.ResearchFormalization.R1201AffineOffsets41941

noncomputable section

open MathlibPlus.Open.ResearchFormalization.R1144DistinctLabels

abbrev C7 := ZMod 7

def properFiberSupport (fibers : C7 → Set C7) : Set C7 :=
  {x | (fibers x).Nonempty ∧ fibers x ≠ Set.univ}

def pointCoPointFiber (S : Set C7) : Prop :=
  (∃ a : C7, S = ({a} : Set C7)) ∨
    ∃ a : C7, S = ({a} : Set C7)ᶜ

def pointCoPointFiberProfile (fibers : C7 → Set C7) : Prop :=
  ∀ x : C7, x ∈ properFiberSupport fibers →
    pointCoPointFiber (fibers x)

def fanoLineComplementFiberProfile
    (fibers : C7 → Set C7) (F : Set (Set C7)) : Prop :=
  (F = fanoA ∨ F = fanoB) ∧
    ∀ x : C7, x ∈ properFiberSupport fibers →
      fibers x ∈ F ∨
        ∃ L : Set C7, L ∈ F ∧ fibers x = Lᶜ

def relativeDerivative (δ : Equiv.Perm C7) (r : C7) : C7 → C7 :=
  fun s => δ (r + s) - δ r

def shiftedDerivativeCompatibility
    (X : Set C7) (r : C7 → C7)
    (δ : C7 → Equiv.Perm C7) : Prop :=
  ∀ x ∈ X, ∀ x' ∈ X, ∀ y : C7,
    relativeDerivative (δ y) (r x) =
      relativeDerivative (δ (y + x' - x)) (r x')

def nonlinearFiberCondition (δ : C7 → Equiv.Perm C7) : Prop :=
  ∃ y : C7, ¬ affinePointPermutation (δ y)

def affineOnSupport (X : Set C7) (r : C7 → C7) : Prop :=
  ∃ m n : C7, ∀ x ∈ X, r x = m * x + n

/-- Claim 41941: in the point/co-point and Fano-line/complement nonlinear
branches, the proper-fibre offsets have the common affine form. -/
def affineOffsetsInNonlinearBranches_claim41941 : Prop :=
  (∀ (fibers : C7 → Set C7) (r : C7 → C7)
      (δ : C7 → Equiv.Perm C7),
    pointCoPointFiberProfile fibers →
    nonlinearFiberCondition δ →
    shiftedDerivativeCompatibility (properFiberSupport fibers) r δ →
    affineOnSupport (properFiberSupport fibers) r) ∧
  (∀ (fibers : C7 → Set C7) (r : C7 → C7)
      (δ : C7 → Equiv.Perm C7) (F : Set (Set C7)),
    fanoLineComplementFiberProfile fibers F →
    nonlinearFiberCondition δ →
    shiftedDerivativeCompatibility (properFiberSupport fibers) r δ →
    affineOnSupport (properFiberSupport fibers) r)

end

end MathlibPlus.Open.ResearchFormalization.R1201AffineOffsets41941
