import Mathlib

namespace MathlibPlus.GraphTheory

open scoped Pointwise

noncomputable section

/-- The two coordinate copies of `𝔽₅^3` used by the finite Hénon connection set. -/
abbrev F5Vec3 := Fin 3 → ZMod 5

/-- The ambient six-dimensional `𝔽₅`-space, represented as two coordinate blocks. -/
abbrev HénonSpace := F5Vec3 × F5Vec3

/-- The polynomial map in the finite rank-six construction. -/
def henonF (z : F5Vec3) : F5Vec3 :=
  ![z 0 ^ 2 + z 0 * z 1 * z 2, z 1 ^ 2, z 2 ^ 2]

/-- The four marked directions and their negatives. -/
def markerDirections : Set F5Vec3 :=
  {![1, 0, 0], ![0, 1, 0], ![0, 0, 1], ![0, 1, 1]}

def markerDirectionsSymm : Set F5Vec3 :=
  markerDirections ∪ (fun z => -z) '' markerDirections

/-- The mixed-difference fibre attached to a marked direction. -/
def mixedDifferenceFibre (z : F5Vec3) : Submodule (ZMod 5) F5Vec3 :=
  Submodule.span (ZMod 5)
    ((Set.range (fun a : F5Vec3 => henonF (a + z) - henonF a - henonF z) : Set F5Vec3) ∪
      (Set.range (fun a : F5Vec3 =>
        (henonF (a - z) - henonF a - henonF (-z) : F5Vec3)) : Set F5Vec3))

/-- The signed fibre union `S` from the rank-six finite construction. -/
def connectionSet : Set HénonSpace :=
  {p | ∃ z : F5Vec3, z ∈ markerDirectionsSymm ∧ p.2 = z ∧
    p.1 ∈ mixedDifferenceFibre z}

/-- The coupled Hénon bijection. -/
def q : HénonSpace → HénonSpace :=
  fun p => (p.2, p.1 + henonF p.2)

/-- The displayed inverse of `q`. -/
def qInverse : HénonSpace → HénonSpace :=
  fun p => (p.2 - henonF p.1, p.1)

end

end MathlibPlus.GraphTheory

namespace MathlibPlus.Algebra.Claim6562

open MathlibPlus.GraphTheory

/-- Claim 6562: the displayed inverse identities and bijectivity of the
source's coupled Hénon map. -/
def q_inverse_and_bijective : Prop :=
  (∀ p : HénonSpace, qInverse (q p) = p ∧ q (qInverse p) = p) ∧
    Function.Bijective q

end MathlibPlus.Algebra.Claim6562

namespace MathlibPlus.GraphTheory

/-- Claim 6566: the exact signed fibre union has cardinality 360. -/
def exactConnectionSetCard_claim6566 : Prop :=
  Set.ncard connectionSet = 360

/-- Claim 6567: the zero element is absent from the exact connection set. -/
def identityFreeConnectionSet_claim6567 : Prop :=
  (0 : HénonSpace) ∉ connectionSet

/-- Claim 6568: the exact signed fibre union is inverse-closed. -/
def connectionSet_neg_claim6568 : Prop :=
  connectionSet = -connectionSet

end MathlibPlus.GraphTheory
