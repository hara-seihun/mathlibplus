import MathlibPlus.Open.Research.FormalizationBatch.R1358Claim38213

namespace MathlibPlus.Open.Research.FormalizationBatch.R1358Claim38207

private abbrev G := (ZMod 2 × ZMod 2 × ZMod 2) × ZMod 9

private abbrev Connection (k : ℕ) :=
  {S : Finset G //
    S.card = k ∧ (0 : G) ∉ S ∧ ∀ x ∈ S, -x ∈ S}

def adjacency (S : Finset G) (x y : G) : Prop :=
  x ≠ y ∧ y - x ∈ S

def graphIsomorphism (S T : Finset G) : Prop :=
  ∃ e : Equiv.Perm G, ∀ x y,
    adjacency S x y ↔ adjacency T (e x) (e y)

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

/-- Claim 38207: the valency-16 presentation-orbit atlas has the same
cardinality as the ordinary graph-isomorphism atlas, with no CI defects. -/
def claim38207 : Prop :=
  allGraphTypeRepresentatives ∧
    allPresentationOrbitRepresentatives ∧
    (∀ S T : Connection 16,
      graphIsomorphism S.1 T.1 ↔ presentationOrbit S.1 T.1) ∧
    (∀ S : Connection 16, cayleyCI S)

end MathlibPlus.Open.Research.FormalizationBatch.R1358Claim38207
