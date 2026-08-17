import MathlibPlus.Open.Combinatorics.ResearchFormalizationBatch_01a00449_34ca_760c_84ef_ba44bc77fc60

namespace MathlibPlus.Open.Combinatorics.LeafDeletionSupportClaims

open scoped BigOperators
open Classical

noncomputable section

/-- The free abelian group on the unrooted tree types of order `n`. -/
abbrev IntegerTreeSpace (n : ℕ) :=
  MathlibPlus.Open.Combinatorics.UnlabelledTree n →₀ ℤ

/-- One occurrence of each leaf-deletion card, with repeated cards retained. -/
noncomputable def leafDeletionBasisInteger (n : ℕ)
    (P : MathlibPlus.Open.Combinatorics.UnlabelledTree (n + 1)) :
    IntegerTreeSpace n :=
  ∑ v : Fin (n + 1),
    if h : MathlibPlus.Open.Combinatorics.isLeaf
        (MathlibPlus.Open.Combinatorics.chosenTreeRep P) v then
      Finsupp.single
        (MathlibPlus.Open.Combinatorics.deleteTree P ⟨v, h⟩) (1 : ℤ)
    else 0

/-- The integral leaf-deletion incidence map. -/
noncomputable def leafDeletionInteger :
    (n : ℕ) → IntegerTreeSpace n →ₗ[ℤ] IntegerTreeSpace (n - 1)
  | 0 => 0
  | n + 1 =>
      Finsupp.lift (IntegerTreeSpace n) ℤ
        (MathlibPlus.Open.Combinatorics.UnlabelledTree (n + 1))
        (leafDeletionBasisInteger n)

/-- The coefficient of the order-`n` card `H` in the deletion incidence of `P`. -/
def leafCardMultiplicity {n : ℕ}
    (P : MathlibPlus.Open.Combinatorics.UnlabelledTree (n + 1))
    (H : MathlibPlus.Open.Combinatorics.UnlabelledTree n) : ℤ :=
  leafDeletionBasisInteger n P H

/-- The distinct support hyperedge of a parent tree. -/
def leafSupport {n : ℕ}
    (P : MathlibPlus.Open.Combinatorics.UnlabelledTree (n + 1)) :
    Set (MathlibPlus.Open.Combinatorics.UnlabelledTree n) :=
  {H | 0 < leafCardMultiplicity P H}

/-- The parent extension set of one card. -/
def extensionSet {n : ℕ}
    (H : MathlibPlus.Open.Combinatorics.UnlabelledTree n) :
    Set (MathlibPlus.Open.Combinatorics.UnlabelledTree (n + 1)) :=
  {P | H ∈ leafSupport P}

/-- The signed leaf-deletion boundary of an integral support-two source. -/
def signedLeafBoundary {n : ℕ}
    (Pplus Pminus : MathlibPlus.Open.Combinatorics.UnlabelledTree (n + 1))
    (a b : ℤ) : IntegerTreeSpace n :=
  leafDeletionInteger (n + 1)
    (a • Finsupp.single Pplus (1 : ℤ) - b • Finsupp.single Pminus (1 : ℤ))

/-- The coordinate formula displayed for a signed support-two boundary. -/
def signedLeafCoefficient {n : ℕ}
    (Pplus Pminus : MathlibPlus.Open.Combinatorics.UnlabelledTree (n + 1))
    (a b : ℤ) (H : MathlibPlus.Open.Combinatorics.UnlabelledTree n) : ℤ :=
  a * leafCardMultiplicity Pplus H - b * leafCardMultiplicity Pminus H

/-- Positive and negative coordinate supports of an integral tree vector. -/
def positiveSignSupport {n : ℕ} (v : IntegerTreeSpace n) :
    Set (MathlibPlus.Open.Combinatorics.UnlabelledTree n) :=
  {H | 0 < v H}

def negativeSignSupport {n : ℕ} (v : IntegerTreeSpace n) :
    Set (MathlibPlus.Open.Combinatorics.UnlabelledTree n) :=
  {H | v H < 0}

/-- The exact integral support-two leaf-boundary predicate. -/
def integralSupportTwoBoundary {n : ℕ} (v : IntegerTreeSpace n) : Prop :=
  ∃ (Pplus Pminus : MathlibPlus.Open.Combinatorics.UnlabelledTree (n + 1))
    (a b : ℤ),
    0 < a ∧ 0 < b ∧
      v = signedLeafBoundary Pplus Pminus a b ∧
        ∀ H : MathlibPlus.Open.Combinatorics.UnlabelledTree n,
          v H = signedLeafCoefficient Pplus Pminus a b H

/-- Both single-hyperedge containment tests pass for a signed vector. -/
def passesBothSupportTests {n : ℕ} (v : IntegerTreeSpace n) : Prop :=
  (∃ P : MathlibPlus.Open.Combinatorics.UnlabelledTree (n + 1),
      positiveSignSupport v ⊆ leafSupport P) ∧
    (∃ P : MathlibPlus.Open.Combinatorics.UnlabelledTree (n + 1),
      negativeSignSupport v ⊆ leafSupport P)

/-- S2: signs of a two-parent signed boundary are supported by their
corresponding leaf-deletion hyperedges, with the equivalent extension-set form. -/
def twoHyperedgeSignSupport_claim47814 : Prop :=
  ∀ (n : ℕ)
    (Pplus Pminus : MathlibPlus.Open.Combinatorics.UnlabelledTree (n + 1))
    (a b : ℤ),
    0 < a → 0 < b →
      let v := signedLeafBoundary Pplus Pminus a b
      (∀ H : MathlibPlus.Open.Combinatorics.UnlabelledTree n,
        v H = signedLeafCoefficient Pplus Pminus a b H) ∧
        positiveSignSupport v ⊆ leafSupport Pplus ∧
        negativeSignSupport v ⊆ leafSupport Pminus ∧
        ((positiveSignSupport v).Nonempty →
          ∀ H, H ∈ positiveSignSupport v → Pplus ∈ extensionSet H) ∧
        ((negativeSignSupport v).Nonempty →
          ∀ H, H ∈ negativeSignSupport v → Pminus ∈ extensionSet H)

/-- S3: failed single-hyperedge containment rejects every integral support-two
source, while passing both tests is explicitly not sufficient. -/
def supportTwoRejectionAndLimitation_claim47818 : Prop :=
  (∀ (n : ℕ) (v : IntegerTreeSpace n),
    ((¬ ∃ P : MathlibPlus.Open.Combinatorics.UnlabelledTree (n + 1),
        positiveSignSupport v ⊆ leafSupport P) ∨
      (¬ ∃ P : MathlibPlus.Open.Combinatorics.UnlabelledTree (n + 1),
        negativeSignSupport v ⊆ leafSupport P)) →
      ¬ integralSupportTwoBoundary v) ∧
  (∃ (n : ℕ) (v : IntegerTreeSpace n),
    passesBothSupportTests v ∧ ¬ integralSupportTwoBoundary v)

end

end MathlibPlus.Open.Combinatorics.LeafDeletionSupportClaims
