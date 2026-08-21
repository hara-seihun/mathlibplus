-- UNVERIFIED (native-decide): submitted but not kernel-verified, so it is not built and MathlibPlus.lean does not import it. See unverified.txt.
import MathlibPlus.Algebra.Claim43805

namespace MathlibPlus.Algebra.Claim43805

theorem stable_iff_union_of_listed_orbits (B : Finset F) :
    stableSupport B ↔ isUnionOfListedHOrbits B := by
  change scaleByThree B = B ↔
    ∃ S : Finset F, S ⊆ orbitRepresentatives ∧ S.biUnion hOrbit = B
  revert B
  native_decide

theorem raw_nonempty_proper_stable_support_count :
    rawNonemptyProperStableSupportCount = 30 := by
  native_decide

theorem normalized_stable_support_count : normalizedStableSupports.card = 10 := by
  native_decide

theorem normalized_orbit_size_histogram :
    normalizedOrbitSizeCount 1 = 2 ∧
    normalizedOrbitSizeCount 2 = 2 ∧
    normalizedOrbitSizeCount 4 = 6 := by
  native_decide

end MathlibPlus.Algebra.Claim43805
