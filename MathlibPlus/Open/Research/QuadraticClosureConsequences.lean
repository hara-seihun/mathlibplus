import MathlibPlus.Open.Research.QuadraticClosures

namespace MathlibPlus.Open.Research.QuadraticClosures

noncomputable section

abbrev QuadraticClass := ZMod 3 × ZMod 3 × ZMod 3

def quadraticRepresentative (c : QuadraticClass) : QuadraticE → QuadraticE :=
  quadraticQ 0 0 c.1 c.2.1 c.2.2

def displayedQuadraticPermutation (c : QuadraticClass)
    (q : Equiv.Perm QuadraticE) : Prop :=
  ∀ x : QuadraticE, q x = quadraticRepresentative c x

def exactQuadraticClosure (q : Equiv.Perm QuadraticE) :
    Set (Equiv.Perm QuadraticE) :=
  quadraticTwoClosure (quadraticGenerated q : Set (Equiv.Perm QuadraticE))

def displayedInTwoClosure (c : QuadraticClass) : Prop :=
  ∃ q : Equiv.Perm QuadraticE,
    displayedQuadraticPermutation c q ∧ q ∈ exactQuadraticClosure q

def alternateClosureConjugator (c : QuadraticClass) : Prop :=
  ∃ (q c' : Equiv.Perm QuadraticE),
    displayedQuadraticPermutation c q ∧
      c' ∈ exactQuadraticClosure q ∧
      Set.image (fun t => c'⁻¹ * t * c') quadraticTranslationSet =
        Set.image (fun t => q⁻¹ * t * q) quadraticTranslationSet

/-- Claim 27835: the exact 2-closure is idempotent for every one of the 27
quadratic-coefficient representatives. -/
def all27TwoClosureIdempotent_claim27835 : Prop :=
  ∀ c : QuadraticClass,
    ∀ q : Equiv.Perm QuadraticE,
      displayedQuadraticPermutation c q →
        quadraticTwoClosure (exactQuadraticClosure q) =
          exactQuadraticClosure q

/-- Claim 27838: the displayed quadratic transporter lies in its exact
2-closure in exactly three classes; in each of the other 24 classes a distinct
closure element conjugates the two regular translation subgroups. -/
def displayedTransporterThreeOfTwentySeven_claim27838 : Prop := by
  classical
  letI : Fintype QuadraticClass := inferInstance
  letI : Fintype {c : QuadraticClass // displayedInTwoClosure c} :=
    Fintype.ofFinite _
  letI : Fintype {c : QuadraticClass // ¬displayedInTwoClosure c} :=
    Fintype.ofFinite _
  exact
    Fintype.card {c : QuadraticClass // displayedInTwoClosure c} = 3 ∧
      Fintype.card {c : QuadraticClass // ¬displayedInTwoClosure c} = 24 ∧
      (∀ c : QuadraticClass,
        ¬displayedInTwoClosure c → alternateClosureConjugator c)

end

end MathlibPlus.Open.Research.QuadraticClosures
