import MathlibPlus.Open.ResearchFormalization.R1967Claim36596

namespace MathlibPlus.Open.ResearchFormalization.R1967Claim36597

open MathlibPlus.Open.ResearchFormalization.R1967
open MathlibPlus.Open.ResearchFormalization.R1967Claim36593
open MathlibPlus.Open.ResearchFormalization.R1967Claim36596

noncomputable section

/-- Both lower edges of the translated `i,j` square are selected.  Their
selection values are the two original direction functions evaluated at the
basepoint represented by the translated origin. -/
def lowerEdgesAtTranslatedOrigin36597
    {n : ℕ} (f : ∀ i : Fin n, DirectionFunction n i)
    (i j : Fin n) (x : Cube n) : Prop :=
  f i (basepointVector i x) = true ∧
    f j (basepointVector j x) = true

/-- Exactly one of the two quotient displacements is outside its affine
hyperplane direction subspace, with the reverse displacement nonzero and
in-plane. -/
def oneOutsideReverseInPlane36597
    {n r : ℕ}
    (F : ∀ i : Fin n, OmittedVector n i →+ QuotientVector r)
    (ell : ∀ i : Fin n, QuotientVector r →+ ZMod 2)
    (i j : Fin n) (x : Cube n) : Prop :=
  (outsideDisplacement36596 (j := j) (F i) (ell i) x ∧
      inPlaneDisplacement36596 (j := i) (F j) (ell j) x ∧
      quotientDisplacement36596 (j := i) (F j) x ≠ 0) ∨
    (outsideDisplacement36596 (j := i) (F j) (ell j) x ∧
      inPlaneDisplacement36596 (j := j) (F i) (ell i) x ∧
      quotientDisplacement36596 (j := j) (F i) x ≠ 0)

def exactlyOneOutside36597
    {n r : ℕ}
    (F : ∀ i : Fin n, OmittedVector n i →+ QuotientVector r)
    (ell : ∀ i : Fin n, QuotientVector r →+ ZMod 2)
    (i j : Fin n) (x : Cube n) : Prop :=
  (outsideDisplacement36596 (j := j) (F i) (ell i) x ∧
      ¬ outsideDisplacement36596 (j := i) (F j) (ell j) x) ∨
    (outsideDisplacement36596 (j := i) (F j) (ell j) x ∧
      ¬ outsideDisplacement36596 (j := j) (F i) (ell i) x)

/-- The exact oriented conclusion for one special-state pair. -/
def specialPairOrientation36597
    {n r : ℕ}
    (F : ∀ i : Fin n, OmittedVector n i →+ QuotientVector r)
    (ell : ∀ i : Fin n, QuotientVector r →+ ZMod 2)
    (i j : Fin n) (x : Cube n) : Prop :=
  oneOutsideReverseInPlane36597 F ell i j x ∧
    exactlyOneOutside36597 F ell i j x

/-- Claim 36597: in the exact target-native hypercube and lossless quotient
setup, every co-occurring special-state pair has both lower edges selected at
the translated origin, and its two displacements have the unique outside/
in-plane orientation.  The resulting orientation is well-defined on every
edge of the special-state graph. -/
def claim36597 : Prop :=
  ∀ (n r : ℕ), 2 ≤ r →
    ∀ f : ∀ i : Fin n, DirectionFunction n i,
      targetNativeHypercubeSetup36593 n r f →
        let H : Set (Fin n) := hyperplanePlusOneDirections (r := r) f
        ∀ (F : ∀ i : Fin n,
            OmittedVector n i →+ QuotientVector r)
          (ell : ∀ i : Fin n, QuotientVector r →+ ZMod 2)
          (c : ∀ i : Fin n, ZMod 2)
          (m : ∀ i : Fin n, QuotientVector r),
          quotientWitnesses36596 f H F ell c m →
            (∀ i j : Fin n, ∀ x : Cube n,
              specialStatePair36596 H F m i j x →
                i ≠ j →
                  lowerEdgesAtTranslatedOrigin36597 f i j x ∧
                    specialPairOrientation36597 F ell i j x) ∧
            (∀ p : Fin n × Fin n,
              p ∈ specialStateEdgeSet36596 H F m →
                ((orientedSpecialPair36596 H F ell m p.1 p.2 ∧
                    ¬ orientedSpecialPair36596 H F ell m p.2 p.1) ∨
                  (orientedSpecialPair36596 H F ell m p.2 p.1 ∧
                    ¬ orientedSpecialPair36596 H F ell m p.1 p.2)))

end

end MathlibPlus.Open.ResearchFormalization.R1967Claim36597
