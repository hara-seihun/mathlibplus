import MathlibPlus.Open.ResearchFormalization.R1255.Claims30659_30662

namespace MathlibPlus.Open.ResearchFormalization.R1255Claim30657Repair

open MathlibPlus.Open.ResearchFormalization.R1255

noncomputable section

abbrev KernelGroup (N : Type*) [AddCommGroup N] (q : ℕ) :=
  Multiplicative (N × ZMod q)
abbrev ComplementGroup := Multiplicative (ZMod 3)
abbrev ScalarExtension {N : Type*} [AddCommGroup N] {q : ℕ}
    (φ : ComplementGroup →* MulAut (KernelGroup N q)) :=
  SemidirectProduct (KernelGroup N q) ComplementGroup φ

def coordinateAction {N : Type*} [AddCommGroup N]
    {q : ℕ} (ω : ZMod q) (θ : N ≃+ N)
    (φ : ComplementGroup →* MulAut (KernelGroup N q)) : Prop :=
  ∀ (i : LayerCoordinate) (n : N) (z : ZMod q),
    φ (i : ComplementGroup) ((n, z) : KernelGroup N q) =
      ((thetaPower θ i n, (ω ^ i.val) * z) : KernelGroup N q)

def regularPointCopy {N : Type*} [AddCommGroup N] [Fintype N]
    {q : ℕ} (G : Type*) [Group G]
    (R : Subgroup (Equiv.Perm (Point N q))) : Prop :=
  (∀ u v : Point N q, ∃! r : R,
    (r : Equiv.Perm (Point N q)) u = v) ∧
    Nonempty (R ≃* G)

def invariantPartition {N : Type*} [AddCommGroup N]
    {q : ℕ} (R : Subgroup (Equiv.Perm (Point N q)))
    (C : Set (Set (Point N q))) : Prop :=
  (∀ B : Set (Point N q), B ∈ C → B.Nonempty) ∧
    (∀ x : Point N q, ∃! B : Set (Point N q), B ∈ C ∧ x ∈ B) ∧
      (∀ r : Equiv.Perm (Point N q), r ∈ R →
        ∀ B : Set (Point N q), B ∈ C →
          ∃ D : Set (Point N q), D ∈ C ∧ Set.image r B = D)

def coarserFixedBPartition {N : Type*} [AddCommGroup N]
    {q : ℕ} (R : Subgroup (Equiv.Perm (Point N q)))
    (C : Set (Set (Point N q))) : Prop :=
  invariantPartition R C ∧
    ∀ b : QuotientCoordinate q, ∃ D : Set (Point N q),
      D ∈ C ∧ block (N := N) b ⊆ D

/-- A fixed-`b` partition is maximal proper when the only invariant partition
coarser than it is itself or the one-block partition. -/
def maximalProperFixedBSystem {N : Type*} [AddCommGroup N]
    {q : ℕ} (R : Subgroup (Equiv.Perm (Point N q))) : Prop :=
  preservesBlockSystem R ∧
    ∀ C : Set (Set (Point N q)),
      coarserFixedBPartition R C →
        C = blockPartition (N := N) (q := q) ∨ C = {Set.univ}

def primitiveScalarAction (q : ℕ) (ω : ZMod q) : Prop :=
  (∀ a c : ZMod q, ∃ σ : Equiv.Perm (ZMod q),
    σ ∈ scalarQuotientAction q ω ∧ σ a = c) ∧
    (∀ S : Set (ZMod q), S.Nonempty →
      (∀ σ : Equiv.Perm (ZMod q), σ ∈ scalarQuotientAction q ω →
        Set.image σ S = S ∨ Disjoint (Set.image σ S) S) →
      (S.Subsingleton ∨ S = Set.univ))

def rightRegularContext {N : Type*} [AddCommGroup N] [Fintype N]
    (q : ℕ) (ω : ZMod q) (θ : N ≃+ N)
    (φ : ComplementGroup →* MulAut (KernelGroup N q))
    (R : Subgroup (Equiv.Perm (Point N q))) : Prop :=
  Nat.Prime q ∧ q % 3 = 1 ∧
    quotientScalarOrderThree q ω ∧
      localOrderThreeFixedPointFree θ ∧
        coordinateAction ω θ φ ∧
          exactRightRegularCopy ω θ R ∧
            regularPointCopy (ScalarExtension φ) R

/-- Claim 30657: every orientation code gives an explicitly conjugated second
regular copy, with the same literal maximal fixed-`b` block system and the
same primitive scalar quotient action. -/
def claim30657 : Prop :=
  ∀ {N : Type*} [AddCommGroup N] [Fintype N]
    (q : ℕ) (ω : ZMod q) (θ : N ≃+ N)
    (φ : ComplementGroup →* MulAut (KernelGroup N q))
    (R : Subgroup (Equiv.Perm (Point N q))),
    rightRegularContext q ω θ φ R →
      ∀ ε : QuotientCoordinate q → Bool,
        let T := conjugatedCopy (orientationMap ε) R
        regularPointCopy (ScalarExtension φ) T ∧
          (∀ b : QuotientCoordinate q,
            Set.image (orientationMap ε)
                (block (N := N) (q := q) b) =
              block (N := N) (q := q) b) ∧
          maximalProperFixedBSystem R ∧
            maximalProperFixedBSystem T ∧
              inducedBlockAction R = scalarQuotientAction q ω ∧
                inducedBlockAction T = scalarQuotientAction q ω ∧
                  primitiveScalarAction q ω

end

end MathlibPlus.Open.ResearchFormalization.R1255Claim30657Repair
