import MathlibPlus.Open.ResearchFormalization.R1148Claim41323
import MathlibPlus.Open.ResearchFormalization.R1148Claim41327

namespace MathlibPlus.Open.ResearchFormalization.R1148Claim31561

noncomputable section

abbrev F7 := ZMod 7
abbrev V := F7 × F7

open MathlibPlus.Open.ResearchFormalization.R1148Claim41323
open MathlibPlus.Open.ResearchFormalization.R1148Claim41327

/-- The indices of the nonempty, non-full vertical fibres of a section. -/
def properFiberIndices (B : Set V) : Set F7 :=
  {x | (verticalFiber B x).Nonempty ∧
    verticalFiber B x ≠ (Set.univ : Set F7)}

/-- A fibre with one point. -/
def singletonFiber (S : Set F7) : Prop :=
  Set.ncard S = 1

/-- A fibre with one missing point. -/
def coSingletonFiber (S : Set F7) : Prop :=
  Set.ncard Sᶜ = 1

/-- A size-three line in one of the two admitted cyclic Fano systems. -/
def cyclicFanoLine (S : Set F7) : Prop :=
  S ∈ fanoA ∨ S ∈ fanoB

/-- A complement of a line in one of the two admitted cyclic Fano systems. -/
def cyclicFanoLineComplement (S : Set F7) : Prop :=
  ∃ F : Set (Set F7),
    (F = fanoA ∨ F = fanoB) ∧ S ∈ lineComplementFamily F

/-- The exceptional alternatives in the affine branch. -/
def affineBranchHypothesis (B : Set V) : Prop :=
  (∃ x ∈ properFiberIndices B,
    ¬ (singletonFiber (verticalFiber B x) ∨
      coSingletonFiber (verticalFiber B x) ∨
      cyclicFanoLine (verticalFiber B x) ∨
      cyclicFanoLineComplement (verticalFiber B x))) ∨
    (∃ x₁ ∈ properFiberIndices B, ∃ x₂ ∈ properFiberIndices B,
      x₁ ≠ x₂ ∧
      ∃ F G : Set (Set F7),
        (F = fanoA ∨ F = fanoB) ∧
          (G = fanoA ∨ G = fanoB) ∧ F ≠ G ∧
          verticalFiber B x₁ ∈ F ∧ verticalFiber B x₂ ∈ G)

/-- The affine form and the coefficient identities asserted in the affine
branch.  The first identity retains the fibre-wise notation
`p_x(v)=d*v+c_x`; the second is the common-multiplier conclusion. -/
def affineBranchConclusion
    (ε : F7) (p : F7 → Equiv.Perm F7)
    (σ : Equiv.Perm V) : Prop :=
  ∃ (d k : F7) (c e : F7 → F7),
    d ≠ 0 ∧
      (∀ x v : F7, p x v = d * v + c x) ∧
        (∀ x u : F7, c (x + 2 • u) - c x = 2 * e u) ∧
          (∀ y : F7, c y = k * y) ∧
            (∀ x y : F7,
              σ (x, y) = (ε * x, k * x + d * y)) ∧
              σ ∈ triangularLinearStabilizer

/-- Claim 31561: in the non-exceptional branch with at least two proper
fibres, the exact zero-fixing fibre permutation is affine, with the common
multiplier, displacement equation, linear displacement, and order-84
triangular-stabilizer conclusion displayed explicitly. -/
def claim31561 : Prop :=
  ∀ (B : Set V) (ε : F7)
    (p q : F7 → Equiv.Perm F7) (σ τ : Equiv.Perm V),
    sameSignProfile ε (fun x y => p x y) (fun x y => q x y) σ τ →
      adjacentSetEquation B σ τ →
        2 ≤ Set.ncard (properFiberIndices B) →
          affineBranchHypothesis B →
            affineBranchConclusion ε p σ

end

end MathlibPlus.Open.ResearchFormalization.R1148Claim31561
