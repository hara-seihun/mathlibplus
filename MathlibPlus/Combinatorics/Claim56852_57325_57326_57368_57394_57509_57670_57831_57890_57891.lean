import Mathlib

namespace MathlibPlus.Combinatorics.Claim56852

/-- The exact finite row-union census from claim 56852.  The inverse-closed
sets and their spans are source carriers; their numerical receipts are exposed
as parameters rather than replaced by an invented model of the construction. -/
def inverseClosedRowUnionCensus_claim56852
    (inverseClosedS0 inverseClosedSLambda : Prop)
    (sizeS0 sizeSLambda spanRankS0 spanRankSLambda : ℕ) : Prop :=
  inverseClosedS0 ∧
    inverseClosedSLambda ∧
    sizeS0 = 2 * 7 * 11 ^ 3 ∧
    sizeSLambda = 2 * 7 * 11 ^ 3 ∧
    spanRankS0 = 7 ∧
    spanRankSLambda = 7

/-- The displayed row-union cardinality evaluates to `18,634`. -/
theorem rowUnionCardinality_claim56852 :
    2 * 7 * 11 ^ 3 = (18634 : ℕ) := by
  norm_num

end MathlibPlus.Combinatorics.Claim56852

namespace MathlibPlus.Combinatorics.Claim57325

/-- The exact four-valued rank-triple census for the fourteen retained
`p = 7` sections.  The section and rank constructions are source carriers;
the finite index and frequency fields retain the complete reported census. -/
def p7SectionCensus_claim57325
    (eligibleSectionCount : ℕ)
    (rankTriple : Fin 14 → ℕ × ℕ × ℕ) : Prop :=
  eligibleSectionCount = 14 ∧
    (∀ i,
      rankTriple i = (0, 81, 0) ∨
      rankTriple i = (0, 87, 0) ∨
      rankTriple i = (0, 98, 0) ∨
      rankTriple i = (0, 99, 0)) ∧
    (Finset.univ.filter (fun i => rankTriple i = (0, 81, 0))).card = 10 ∧
    (Finset.univ.filter (fun i => rankTriple i = (0, 87, 0))).card = 1 ∧
    (Finset.univ.filter (fun i => rankTriple i = (0, 98, 0))).card = 2 ∧
    (Finset.univ.filter (fun i => rankTriple i = (0, 99, 0))).card = 1

end MathlibPlus.Combinatorics.Claim57325

namespace MathlibPlus.Combinatorics.Claim57326

/-- The exact singleton retained-section and rank-triple receipt for `p = 11`. -/
def p11SectionCensus_claim57326
    (eligibleSectionCount : ℕ)
    (rankTriple : ℕ × ℕ × ℕ) : Prop :=
  eligibleSectionCount = 1 ∧ rankTriple = (0, 40, 0)

end MathlibPlus.Combinatorics.Claim57326

namespace MathlibPlus.Combinatorics.Claim57368

/-- The exact screen-count interface from claim 57368.  `Test` and the rank
functions retain the source's tested augmented/coefficient-rank comparison;
the screen's finite-field and map-generation semantics are deliberately left
as explicit carriers. -/
def splitCubicScreenCensus_claim57368
    {Test : Type*}
    (tripleCountAt11 tripleCountAt13 binaryCount₁ binaryCount₂
      binaryCount₃ binaryCount₄ : ℕ)
    (mixedCount : ZMod 7 → ℕ)
    (augmentedRank coefficientRank : Test → ℕ)
    (verticalShearDefect : Prop) : Prop :=
  tripleCountAt11 = 120 ∧
    tripleCountAt13 = 216 ∧
    binaryCount₁ = 5 ∧
    binaryCount₂ = 35 ∧
    binaryCount₃ = 35 ∧
    binaryCount₄ = 330 ∧
    (∀ a : ZMod 7, a ≠ 0 → mixedCount a = 35) ∧
    (∀ t, augmentedRank t = coefficientRank t) ∧
    ¬ verticalShearDefect

end MathlibPlus.Combinatorics.Claim57368

namespace MathlibPlus.Combinatorics.Claim57394

/-- The exact count and endpoint portion of the proof-critical certificate
inventory in claim 57394.  Numerical interval margins are retained by the
positive-margin and roundoff fields; the receipt's approximate decimal
printing is not silently promoted to an exact rational value. -/
def proofCriticalCertificateInventory_claim57394
    (verificationPass : Bool)
    (primeFibreReplayTasks taylorTasks freshCauchyCertificates
      heightTailCertificates sparseCells replayMutations taylorMutations
      loadBearingMutationRejections finiteEndpoint analyticTailStart : ℕ)
    (finiteEndpointMargin bridgeMargin tailLowerEndpoint roundoffBound : ℚ) : Prop :=
  verificationPass = true ∧
    primeFibreReplayTasks = 50 ∧
    taylorTasks = 96 ∧
    freshCauchyCertificates = 96 ∧
    heightTailCertificates = 6 ∧
    sparseCells = 525 ∧
    replayMutations = 150 ∧
    taylorMutations = 576 ∧
    loadBearingMutationRejections = 726 ∧
    finiteEndpoint = 174767473 ∧
    analyticTailStart = 174767474 ∧
    0 < finiteEndpointMargin ∧
    0 < bridgeMargin ∧
    0 < tailLowerEndpoint ∧
    roundoffBound < 1 / 100000

end MathlibPlus.Combinatorics.Claim57394

namespace MathlibPlus.Combinatorics.Claim57509

/-- The exact support-four no-mismatch interface from claim 57509.  `eligible`
encodes the source's at-most-four-atom and nonempty-section conditions, while
`Z` and `f` retain the invariant and collision-map carriers. -/
def supportFourNoDefect_claim57509
    {U V : Type*}
    (eligible : U → Prop)
    (Z : U → V)
    (f : U → U)
    (eligibleUnionCount mismatchCount : ℕ) : Prop :=
  eligibleUnionCount = 35280 ∧
    mismatchCount = 0 ∧
    ∀ S, eligible S → Z S = Z (f S)

end MathlibPlus.Combinatorics.Claim57509

namespace MathlibPlus.Combinatorics.Claim57670

/-- The audited-family no-defect receipt from claim 57670.  The atom,
automorphism, and transporter predicates are parameters so the source group
and derivative-orbit constructions remain visible rather than being replaced
by an unrelated finite model. -/
def auditedFamilyNoDefect_claim57670
    {Atom Aut : Type*}
    (labelRepresentativeCount sectionCount atomCount automorphismCount : ℕ)
    (nonidentity : Atom → Prop)
    (carries : Atom → Aut → Prop) : Prop :=
  labelRepresentativeCount = 30 ∧
    sectionCount = 2001 ∧
    atomCount = 60030 ∧
    automorphismCount = 1008 ∧
    ∀ atom, nonidentity atom → ∃ φ, carries atom φ

end MathlibPlus.Combinatorics.Claim57670

namespace MathlibPlus.Combinatorics.Claim57831

/-- The exact finite-family audit interface from claim 57831.  Each
`reachable...` field records the corresponding exhaustive finite result; no
universal conclusion about the surrounding infinite model family is added. -/
def finiteModelFamiliesAudit_claim57831
    (oddCubicTwoPlusTwoPlusTwo cyclicTwoPlusTwoPlusTwo
      oddCubicThreePlusThree degreeFiveThreePlusThree
      centralVoltageFourPlusTwo quotientVoltageThreePlusThree
      nonTriangularDifferenceCount : ℕ)
    (reachableOddCubicTwoPlusTwoPlusTwo
      reachableCyclicTwoPlusTwoPlusTwo
      reachableOddCubicThreePlusThree
      reachableDegreeFiveThreePlusThree
      reachableNonTriangular
      reachableCentralVoltageFourPlusTwo
      reachableQuotientVoltageThreePlusThree : Prop) : Prop :=
  oddCubicTwoPlusTwoPlusTwo = 100 ∧
    cyclicTwoPlusTwoPlusTwo = 100 ∧
    oddCubicThreePlusThree = 10 ∧
    degreeFiveThreePlusThree = 10 ∧
    centralVoltageFourPlusTwo = 50 ∧
    quotientVoltageThreePlusThree = 30 ∧
    nonTriangularDifferenceCount = 5 ^ 6 - 1 ∧
    nonTriangularDifferenceCount = 15624 ∧
    reachableOddCubicTwoPlusTwoPlusTwo ∧
    reachableCyclicTwoPlusTwoPlusTwo ∧
    reachableOddCubicThreePlusThree ∧
    reachableDegreeFiveThreePlusThree ∧
    reachableNonTriangular ∧
    reachableCentralVoltageFourPlusTwo ∧
    reachableQuotientVoltageThreePlusThree

/-- The sparse nontriangular difference count in claim 57831. -/
theorem nonTriangularDifferenceCount_claim57831 :
    5 ^ 6 - 1 = (15624 : ℕ) := by
  norm_num

end MathlibPlus.Combinatorics.Claim57831

namespace MathlibPlus.Combinatorics.Claim57890

/-- The `(p,b,a) = (5,3,2)` finite-control receipt from claim 57890. -/
def finiteControlClaim57890
    (p b a retainedProfileCount : ℕ)
    (defectDimension : Fin retainedProfileCount → ℕ) : Prop :=
  p = 5 ∧
    b = 3 ∧
    a = 2 ∧
    retainedProfileCount = 40 ∧
    ∀ profile, defectDimension profile = 0

end MathlibPlus.Combinatorics.Claim57890

namespace MathlibPlus.Combinatorics.Claim57891

/-- The `(p,b,a) = (3,4,2)` attempt/retention receipt from claim 57891. -/
def finiteControlClaim57891
    (p b a attemptedProfileCount retainedProfileCount : ℕ)
    (defectDimension : Fin retainedProfileCount → ℕ) : Prop :=
  p = 3 ∧
    b = 4 ∧
    a = 2 ∧
    attemptedProfileCount = 40 ∧
    retainedProfileCount = 31 ∧
    ∀ profile, defectDimension profile = 0

end MathlibPlus.Combinatorics.Claim57891
