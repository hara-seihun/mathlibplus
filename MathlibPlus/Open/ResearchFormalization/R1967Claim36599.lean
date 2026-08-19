import MathlibPlus.Open.ResearchFormalization.R1967Claim36596

namespace MathlibPlus.Open.ResearchFormalization.R1967Claim36599

open MathlibPlus.Open.ResearchFormalization.R1967
open MathlibPlus.Open.ResearchFormalization.R1967Claim36593
open MathlibPlus.Open.ResearchFormalization.R1967Claim36596

noncomputable section

/-- Quotient vectors outside the direction subspace of the affine hyperplane. -/
def outsideQuotientVectors36599
    {r : ℕ} (ell : QuotientVector r →+ ZMod 2) : Set (QuotientVector r) :=
  {u | ell u ≠ 0}

/-- The reverse in-plane neighbours supported by one fixed outside vector. -/
def specialStateFan36599
    {n r : ℕ}
    (H : Set (Fin n))
    (F : ∀ i : Fin n, OmittedVector n i →+ QuotientVector r)
    (ell : ∀ i : Fin n, QuotientVector r →+ ZMod 2)
    (m : ∀ i : Fin n, QuotientVector r)
    (i : Fin n) (u : QuotientVector r) : Set (Fin n) :=
  {j | ∃ x : Cube n,
    specialStatePair36596 H F m i j x ∧
      outsideDisplacement36596 (j := j) (F i) (ell i) x ∧
      quotientDisplacement36596 (j := j) (F i) x = u ∧
      inPlaneDisplacement36596 (j := i) (F j) (ell j) x ∧
      quotientDisplacement36596 (j := i) (F j) x ≠ 0}

/-- The finite out-neighbour set induced by the canonical orientation of the
special-state graph. -/
def specialStateOutNeighbors36599
    {n r : ℕ}
    (H : Set (Fin n))
    (F : ∀ i : Fin n, OmittedVector n i →+ QuotientVector r)
    (ell : ∀ i : Fin n, QuotientVector r →+ ZMod 2)
    (m : ∀ i : Fin n, QuotientVector r)
    (i : Fin n) : Set (Fin n) :=
  {j | orientedSpecialPair36596 H F ell m i j}

/-- The degree bound `D_q = (q/2)(q/2-1)` in the exact target-native
special-state carrier. -/
def specialStateDegreeBound36599 (q : ℕ) : ℚ :=
  (q : ℚ) / 2 * ((q : ℚ) / 2 - 1)

/-- Claim 36599: in the exact C₄-free hypercube and lossless quotient setup,
there are `q/2` outside quotient vectors, each supports at most `q/2-1`
reverse in-plane neighbours, and the canonically oriented special-state graph
has the resulting maximum outdegree and edge bound. -/
def claim36599 : Prop :=
  ∀ (n r : ℕ), 2 ≤ r →
    ∀ f : ∀ i : Fin n, DirectionFunction n i,
      targetNativeHypercubeSetup36593 n r f →
        let q : ℕ := 2 ^ r
        let H : Set (Fin n) := hyperplanePlusOneDirections (r := r) f
        ∀ (F : ∀ i : Fin n,
            OmittedVector n i →+ QuotientVector r)
          (ell : ∀ i : Fin n, QuotientVector r →+ ZMod 2)
          (c : ∀ i : Fin n, ZMod 2)
          (m : ∀ i : Fin n, QuotientVector r),
          quotientWitnesses36596 f H F ell c m →
            (∀ i, i ∈ H →
              (Set.ncard (outsideQuotientVectors36599 (ell i)) : ℚ) =
                (q : ℚ) / 2) ∧
            (∀ i, i ∈ H → ∀ u : QuotientVector r,
              ell i u ≠ 0 →
                (Set.ncard (specialStateFan36599 H F ell m i u) : ℚ) ≤
                  (q : ℚ) / 2 - 1) ∧
            (∀ i, i ∈ H →
              (Set.ncard (specialStateOutNeighbors36599 H F ell m i) : ℚ) ≤
                specialStateDegreeBound36599 q) ∧
            specialStateDegreeBound36599 q =
              (q : ℚ) * ((q : ℚ) - 2) / 4 ∧
            (Set.ncard (specialStateEdgeSet36596 H F m) : ℚ) ≤
              specialStateDegreeBound36599 q * (Set.ncard H : ℚ)

end

end MathlibPlus.Open.ResearchFormalization.R1967Claim36599
