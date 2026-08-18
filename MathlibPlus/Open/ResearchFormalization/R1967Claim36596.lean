import MathlibPlus.Open.ResearchFormalization.R1967Claim36593

namespace MathlibPlus.Open.ResearchFormalization.R1967Claim36596

open MathlibPlus.Open.ResearchFormalization.R1967
open MathlibPlus.Open.ResearchFormalization.R1967Claim36593

noncomputable section

/-- Extend a quotient map from the omitted-coordinate basepoint space to the
full cube by ignoring the named coordinate. -/
def fullCubeQuotientMap36596
    {n r : ℕ} {i : Fin n}
    (F : OmittedVector n i →+ QuotientVector r) :
    Cube n → QuotientVector r :=
  fun x => F (basepointVector i x)

/-- The exact lossless hyperplane-plus-one witness carried by one direction. -/
def quotientWitness36596
    {n r : ℕ} {i : Fin n}
    (f : DirectionFunction n i)
    (F : OmittedVector n i →+ QuotientVector r)
    (ell : QuotientVector r →+ ZMod 2)
    (c : ZMod 2) (m : QuotientVector r) : Prop :=
  Function.Surjective F ∧
    ell ≠ 0 ∧
    ell m ≠ c ∧
    (∀ x, f x = true ↔
      (ell (F x) = c ∨ F x = m)) ∧
    (∀ v, v ∈ quotientTranslationStabilizer f ↔ F v = 0)

/-- Quotient witnesses for every direction in the exact hyperplane-plus-one
 tier. -/
def quotientWitnesses36596
    {n r : ℕ}
    (f : ∀ i : Fin n, DirectionFunction n i)
    (H : Set (Fin n))
    (F : ∀ i : Fin n, OmittedVector n i →+ QuotientVector r)
    (ell : ∀ i : Fin n, QuotientVector r →+ ZMod 2)
    (c : ∀ i : Fin n, ZMod 2)
    (m : ∀ i : Fin n, QuotientVector r) : Prop :=
  ∀ i, i ∈ H → quotientWitness36596 (f i) (F i) (ell i) (c i) (m i)

/-- The full-cube special state in direction `i`. -/
def specialStateSet36596
    {n r : ℕ}
    (H : Set (Fin n))
    (F : ∀ i : Fin n, OmittedVector n i →+ QuotientVector r)
    (m : ∀ i : Fin n, QuotientVector r)
    (x : Cube n) : Set (Fin n) :=
  {i | i ∈ H ∧ fullCubeQuotientMap36596 (F i) x = m i}

/-- The quotient displacement seen by direction `i` when coordinate `j` is
flipped. -/
def quotientDisplacement36596
    {n r : ℕ} {i j : Fin n}
    (F : OmittedVector n i →+ QuotientVector r)
    (x : Cube n) : QuotientVector r :=
  F (basepointVector i (flipAt j x)) + F (basepointVector i x)

/-- A displacement is outside the direction subspace of the affine
hyperplane exactly when its defining functional is nonzero. -/
def outsideDisplacement36596
    {n r : ℕ} {i j : Fin n}
    (F : OmittedVector n i →+ QuotientVector r)
    (ell : QuotientVector r →+ ZMod 2)
    (x : Cube n) : Prop :=
  ell (quotientDisplacement36596 (j := j) F x) ≠ 0

def inPlaneDisplacement36596
    {n r : ℕ} {i j : Fin n}
    (F : OmittedVector n i →+ QuotientVector r)
    (ell : QuotientVector r →+ ZMod 2)
    (x : Cube n) : Prop :=
  ell (quotientDisplacement36596 (j := j) F x) = 0

/-- A pair of directions occurs together in one special state. -/
def specialStatePair36596
    {n r : ℕ}
    (H : Set (Fin n))
    (F : ∀ i : Fin n, OmittedVector n i →+ QuotientVector r)
    (m : ∀ i : Fin n, QuotientVector r)
    (i j : Fin n) (x : Cube n) : Prop :=
  i ∈ specialStateSet36596 H F m x ∧
    j ∈ specialStateSet36596 H F m x

/-- The canonical orientation of a co-occurring pair is the direction whose
cross-coordinate displacement is outside its hyperplane direction subspace. -/
def orientedSpecialPair36596
    {n r : ℕ}
    (H : Set (Fin n))
    (F : ∀ i : Fin n, OmittedVector n i →+ QuotientVector r)
    (ell : ∀ i : Fin n, QuotientVector r →+ ZMod 2)
    (m : ∀ i : Fin n, QuotientVector r)
    (i j : Fin n) : Prop :=
  i ≠ j ∧
    ∃ x : Cube n,
      specialStatePair36596 H F m i j x ∧
        outsideDisplacement36596 (j := j) (F i) (ell i) x

/-- The special-state edge set, with each unordered edge represented once by
its increasing ordered pair. -/
def specialStateEdgeSet36596
    {n r : ℕ}
    (H : Set (Fin n))
    (F : ∀ i : Fin n, OmittedVector n i →+ QuotientVector r)
    (m : ∀ i : Fin n, QuotientVector r) : Set (Fin n × Fin n) :=
  {p | p.1 < p.2 ∧
    ∃ x : Cube n, specialStatePair36596 H F m p.1 p.2 x}

/-- Uniform probability on the finite full cube, represented by exact rational
cardinality. -/
noncomputable def cubeProbability36596
    {n : ℕ} (E : Set (Cube n)) : ℚ :=
  (Set.ncard E : ℚ) / (Fintype.card (Cube n) : ℚ)

noncomputable def specialStateProbability36596
    {n r : ℕ}
    (H : Set (Fin n))
    (F : ∀ i : Fin n, OmittedVector n i →+ QuotientVector r)
    (m : ∀ i : Fin n, QuotientVector r)
    (i : Fin n) : ℚ :=
  cubeProbability36596
    {x | i ∈ specialStateSet36596 H F m x}

noncomputable def specialStatePairProbability36596
    {n r : ℕ}
    (H : Set (Fin n))
    (F : ∀ i : Fin n, OmittedVector n i →+ QuotientVector r)
    (m : ∀ i : Fin n, QuotientVector r)
    (i j : Fin n) : ℚ :=
  cubeProbability36596
    {x | specialStatePair36596 H F m i j x}

/-- The exact one-outside-displacement orientation supplied by the quotient
trichotomy for every special-state pair. -/
def canonicalOutsideOrientation36596
    {n r : ℕ}
    (H : Set (Fin n))
    (F : ∀ i : Fin n, OmittedVector n i →+ QuotientVector r)
    (ell : ∀ i : Fin n, QuotientVector r →+ ZMod 2)
    (m : ∀ i : Fin n, QuotientVector r) : Prop :=
  ∀ i j : Fin n, ∀ x : Cube n,
    specialStatePair36596 H F m i j x →
      i ≠ j →
        ((outsideDisplacement36596 (j := j) (F i) (ell i) x ∧
            inPlaneDisplacement36596 (j := i) (F j) (ell j) x ∧
            quotientDisplacement36596 (j := i) (F j) x ≠ 0) ∨
          (outsideDisplacement36596 (j := i) (F j) (ell j) x ∧
            inPlaneDisplacement36596 (j := j) (F i) (ell i) x ∧
            quotientDisplacement36596 (j := j) (F i) x ≠ 0))

/-- Claim 36596: after the exact target-native hypercube and quotient setup,
the special-state graph has the stated uniform one-point and pair-incidence
bounds, is canonically oriented by the outside displacement, and satisfies
the Jensen/pair-incidence lower edge bound. -/
def claim36596 : Prop :=
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
              specialStateProbability36596 H F m i = 1 / (q : ℚ)) ∧
            (∀ i j, i ∈ H → j ∈ H → i ≠ j →
              specialStatePairProbability36596 H F m i j ≤ 1 / (q : ℚ)) ∧
            canonicalOutsideOrientation36596 H F ell m ∧
            (Set.ncard (specialStateEdgeSet36596 H F m) : ℚ) ≥
              ((Set.ncard H : ℚ) ^ 2) / (2 * (q : ℚ)) -
                (Set.ncard H : ℚ) / 2

end

end MathlibPlus.Open.ResearchFormalization.R1967Claim36596
