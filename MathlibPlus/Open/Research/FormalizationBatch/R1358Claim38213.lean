import Mathlib

namespace MathlibPlus.Open.Research.FormalizationBatch.R1358Claim38213

open scoped BigOperators

private abbrev G := (ZMod 2 × ZMod 2 × ZMod 2) × ZMod 9
private abbrev B := ZMod 2 × ZMod 2 × ZMod 2
private abbrev H := ZMod 9

private abbrev Connection (k : ℕ) :=
  {S : Finset G //
    S.card = k ∧ (0 : G) ∉ S ∧ ∀ x ∈ S, -x ∈ S}

def adjacency (S : Finset G) (x y : G) : Prop :=
  x ≠ y ∧ y - x ∈ S

def graphIsomorphism (S T : Finset G) : Prop :=
  ∃ e : Equiv.Perm G, ∀ x y,
    adjacency S x y ↔ adjacency T (e x) (e y)

def graphAutomorphism (S : Finset G) (e : Equiv.Perm G) : Prop :=
  ∀ x y, adjacency S x y ↔ adjacency S (e x) (e y)

def presentationOrbit (S T : Finset G) : Prop :=
  ∃ e : G ≃+ G, T = S.image e

def cayleyCI (S : Connection 16) : Prop :=
  ∀ T : Connection 16,
    graphIsomorphism S.1 T.1 →
      ∃ e : G ≃+ G, T.1 = S.1.image e

def allGraphTypeRepresentatives : Prop :=
  ∃ reps : Finset (Connection 16),
    reps.card = 255151 ∧
    ∀ S : Connection 16,
      ∃! R : Connection 16,
        R ∈ reps ∧ graphIsomorphism S.1 R.1

def allPresentationOrbitRepresentatives : Prop :=
  ∃ reps : Finset (Connection 16),
    reps.card = 255151 ∧
    ∀ S : Connection 16,
      ∃! R : Connection 16,
        R ∈ reps ∧ presentationOrbit S.1 R.1

def naturalBinaryFiberPreserved (S : Connection 16) : Prop :=
  ∀ e : Equiv.Perm G,
    graphAutomorphism S.1 e →
      ∀ C ∈ (Finset.univ : Finset H).image (fun h =>
        (Finset.univ : Finset B).image (fun b => (b, h))),
        ∃ D ∈ (Finset.univ : Finset H).image (fun h =>
          (Finset.univ : Finset B).image (fun b => (b, h))),
          C.image e = D

def partitionBreaking (S : Connection 16) : Prop :=
  ¬ naturalBinaryFiberPreserved S

def baseAction (S : Connection 16) : Set (Equiv.Perm H) :=
  {σ | ∃ e : Equiv.Perm G,
    graphAutomorphism S.1 e ∧
      e ((0 : B), (0 : H)) = ((0 : B), (0 : H)) ∧
      naturalBinaryFiberPreserved S ∧
      ∀ b : B, ∀ h : H, (e (b, h)).2 = σ h}

def nonlinearBase (S : Connection 16) : Prop :=
  ∃ σ : Equiv.Perm H,
    σ ∈ baseAction S ∧
      ¬ ∃ e : H ≃+ H, ∀ h, e h = σ h

def connected (S : Connection 16) : Prop :=
  AddSubgroup.closure (S.1 : Set G) = ⊤

def partitionBreakingRepresentatives : Prop :=
  ∃ reps : Finset (Connection 16),
    reps.card = 7389 ∧
    (∀ R ∈ reps, partitionBreaking R) ∧
    ∀ S : Connection 16, partitionBreaking S →
      ∃! R : Connection 16,
        R ∈ reps ∧ partitionBreaking R ∧ graphIsomorphism S.1 R.1

def connectedPartitionBreakingRepresentatives : Prop :=
  ∃ reps : Finset (Connection 16),
    reps.card = 4530 ∧
    (∀ R ∈ reps, partitionBreaking R ∧ connected R) ∧
    ∀ S : Connection 16, partitionBreaking S → connected S →
      ∃! R : Connection 16,
        R ∈ reps ∧ partitionBreaking R ∧ connected R ∧
          graphIsomorphism S.1 R.1

def nonlinearBaseRepresentatives : Prop :=
  ∃ reps : Finset (Connection 16),
    reps.card = 254 ∧
    (∀ R ∈ reps,
      naturalBinaryFiberPreserved R ∧ nonlinearBase R ∧ cayleyCI R) ∧
    ∀ S : Connection 16,
      naturalBinaryFiberPreserved S → nonlinearBase S →
        ∃! R : Connection 16,
          R ∈ reps ∧ naturalBinaryFiberPreserved R ∧ nonlinearBase R ∧
            graphIsomorphism S.1 R.1

def connectedNonlinearBaseRepresentatives : Prop :=
  ∃ reps : Finset (Connection 16),
    reps.card = 236 ∧
    (∀ R ∈ reps,
      naturalBinaryFiberPreserved R ∧ nonlinearBase R ∧ connected R ∧
        cayleyCI R) ∧
    ∀ S : Connection 16,
      naturalBinaryFiberPreserved S → nonlinearBase S → connected S →
        ∃! R : Connection 16,
          R ∈ reps ∧ naturalBinaryFiberPreserved R ∧ nonlinearBase R ∧
            connected R ∧ graphIsomorphism S.1 R.1

/-- Claim 38213: the two exact ambient exception families on the concrete
`C₂³ × C₉` valency-16 atlas are disjoint, have the displayed graph-type
counts and connected subcounts, and every exception has a singleton ordinary
isomorphism fiber modulo group automorphisms. -/
def claim38213 : Prop :=
  allGraphTypeRepresentatives ∧
    allPresentationOrbitRepresentatives ∧
    partitionBreakingRepresentatives ∧
    connectedPartitionBreakingRepresentatives ∧
    nonlinearBaseRepresentatives ∧
    connectedNonlinearBaseRepresentatives ∧
    (∀ S T : Connection 16,
      graphIsomorphism S.1 T.1 ↔ presentationOrbit S.1 T.1) ∧
    (∀ S : Connection 16,
      partitionBreaking S → ¬ nonlinearBase S) ∧
    7389 + 254 = (7643 : ℕ) ∧
    (∀ S : Connection 16,
      (partitionBreaking S ∨ nonlinearBase S) → cayleyCI S)

end MathlibPlus.Open.Research.FormalizationBatch.R1358Claim38213
