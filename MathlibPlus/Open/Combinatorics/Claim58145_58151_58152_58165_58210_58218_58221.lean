import MathlibPlus.Basic

namespace MathlibPlus.Open.Combinatorics

/--
Claim 58145: the exact finite Sylow/regular-representative census.  The
underlying graph-automorphism group and its tested representative predicate
remain explicit carriers; the numerical records are not promoted to a
universal classification theorem.
-/
def sylowThreeReplayClaim58145
    (sylowThreeOrder representativeOrder subgroupConjugacyClassCount
      regularRepresentativeCount ambientConjugacyClassCount : ℕ)
    (testedRepresentativesHaveRequiredProperties : Prop) : Prop :=
  sylowThreeOrder = 2187 ∧
    representativeOrder = (3 : ℕ) ^ 6 ∧
    subgroupConjugacyClassCount = 24740 ∧
    regularRepresentativeCount = 1 ∧
    ambientConjugacyClassCount = 1 ∧
    testedRepresentativesHaveRequiredProperties

/--
Claim 58151: the finite fusion screen has 24 positions and 18 tested
eligible fusions, and every tested fusion has the stated conjugacy outcome.
The two graph-group predicates are supplied by the source-specific carrier.
-/
def fusionScreenClaim58151
    (positionCount testedFusionCount : ℕ)
    (everyTestedFusionHasConjugateRegularGroups : Prop)
    (noOrdinaryCICountercertificate : Prop) : Prop :=
  positionCount = 24 ∧
    testedFusionCount = 18 ∧
    everyTestedFusionHasConjugateRegularGroups ∧
    noOrdinaryCICountercertificate

/--
Claim 58152: exact replay receipt for the 24 pairs and 18 tested fusions.
`comparisonsUseLiteralFiniteData` and `fixedSeedIsReproducibilityRecord`
are explicit source-carrier facts; the latter is not introduced as a
mathematical hypothesis about arbitrary inputs.
-/
def noDefectReplayClaim58152
    (status : String) (pairCount testedCount : ℕ)
    (comparisonsUseLiteralFiniteData fixedSeedIsReproducibilityRecord : Prop) : Prop :=
  status = "NO_DEFECT" ∧
    pairCount = 24 ∧
    testedCount = 18 ∧
    comparisonsUseLiteralFiniteData ∧
    fixedSeedIsReproducibilityRecord

/-- The two exact three-mode rank signatures in Claim 58165. -/
def modeRankSignaturesClaim58165
    (k₁modeOne k₁periodThree k₁periodNine
      k₃modeOne k₃periodThree k₃periodNine : ℕ) : Prop :=
  k₁modeOne = 2 ∧
    k₁periodThree = 0 ∧
    k₁periodNine = 0 ∧
    k₃modeOne = 0 ∧
    k₃periodThree = 2 ∧
    k₃periodNine = 0

/--
Claim 58210: the exact translated-C3 replay counts.  The finite scout and
unsupported-line facts are parameters because the packet does not provide a
Lean model of the maps, supports, or graph-fusion operation.
-/
def translatedC3ReplayClaim58210
    (totalRows sizeThreeRows sizeSixRows sizeThreeEscapes sizeSixEscapes
      sizeThreeInvariantRows sizeSixInvariantRows sizeSixVisitsPerOrientation
      sizeSixNoncollisionActiveIndices : ℕ)
    (fixedFamilyRankThreeScoutsFindNoDefect
      firstUnsupportedLineIsSixActiveTranslatedC3 : Prop) : Prop :=
  totalRows = 120960 ∧
    sizeThreeRows = 80640 ∧
    sizeSixRows = 40320 ∧
    sizeThreeEscapes = 80352 ∧
    sizeSixEscapes = 40176 ∧
    sizeThreeInvariantRows = 288 ∧
    sizeSixInvariantRows = 144 ∧
    sizeSixVisitsPerOrientation = 120960 ∧
    sizeSixNoncollisionActiveIndices = 3 ∧
    fixedFamilyRankThreeScoutsFindNoDefect ∧
    firstUnsupportedLineIsSixActiveTranslatedC3

/--
Claim 58218: exact screen counts and zero-failure receipts.  The finite
vector-space, map, and component/profile carriers are deliberately exposed
through their receipt values rather than reconstructed from unstated source
conventions.
-/
def finiteScreenReceiptClaim58218
    (sparseMapCount sparseSelectionsPerRow shearMapCount shearSelectionsPerRow
      expandedMapCount expandedSelectionsPerRow controlSize₁ controlSize₂
      controlSize₃ hyperplaneProfileMismatches componentFormulaFailures
      cubicCorrectionRank cubicAugmentedRank cubicComponentProfileMismatches : ℕ) : Prop :=
  sparseMapCount = 512 ∧
    sparseSelectionsPerRow = 256 ∧
    shearMapCount = 64 ∧
    shearSelectionsPerRow = 256 ∧
    expandedMapCount = 64 ∧
    expandedSelectionsPerRow = 1024 ∧
    controlSize₁ = 9 ∧
    controlSize₂ = 81 ∧
    controlSize₃ = 6561 ∧
    hyperplaneProfileMismatches = 0 ∧
    componentFormulaFailures = 0 ∧
    cubicCorrectionRank = cubicAugmentedRank ∧
    cubicComponentProfileMismatches = 0

/--
Claim 58221: exact rank-one projective-fibre counts for weights 1 through 12,
with the total and the reported tangent-flatness conclusions retained as
explicit source predicates.
-/
def projectiveFibreReceiptClaim58221
    (weight₁ weight₂ weight₃ weight₄ weight₅ weight₆ weight₇ weight₈
      weight₉ weight₁₀ weight₁₁ weight₁₂ totalFibreCount : ℕ)
    (allFourteenDifferencesHavePositiveTDegree noTangentFlatFibreInRange : Prop) : Prop :=
  weight₁ = 0 ∧
    weight₂ = 0 ∧
    weight₃ = 0 ∧
    weight₄ = 0 ∧
    weight₅ = 0 ∧
    weight₆ = 0 ∧
    weight₇ = 0 ∧
    weight₈ = 0 ∧
    weight₉ = 0 ∧
    weight₁₀ = 1 ∧
    weight₁₁ = 3 ∧
    weight₁₂ = 10 ∧
    totalFibreCount = 14 ∧
    allFourteenDifferencesHavePositiveTDegree ∧
    noTangentFlatFibreInRange

end MathlibPlus.Open.Combinatorics

