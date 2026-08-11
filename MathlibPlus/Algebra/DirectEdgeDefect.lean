import Mathlib

namespace MathlibPlus.Algebra.DirectEdgeDefect

/-!
The direct-edge defect in claim 34356 is the alternating two-column
expression `R_A U_B - U_A R_B`.  The index type abstracts the rooted
objects; no tree-specific structure is needed for the two stated
identities.
-/

/-- The direct-edge defect of two rooted-column coordinates. -/
def delta {R ι : Type*} [CommRing R]
    (rootR rootU : ι → R) (A B : ι) : R :=
  rootR A * rootU B - rootU A * rootR B

/-- The direct-edge defect is antisymmetric. -/
theorem delta_antisymm {R ι : Type*} [CommRing R]
    (rootR rootU : ι → R) (A B : ι) :
    delta rootR rootU A B = -delta rootR rootU B A := by
  unfold delta
  ring

/-- The direct-edge defect vanishes on the diagonal. -/
theorem delta_self {R ι : Type*} [CommRing R]
    (rootR rootU : ι → R) (A : ι) :
    delta rootR rootU A A = 0 := by
  unfold delta
  ring

end MathlibPlus.Algebra.DirectEdgeDefect
