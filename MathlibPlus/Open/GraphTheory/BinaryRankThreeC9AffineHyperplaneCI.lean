import Mathlib

namespace MathlibPlus.Open.GraphTheory

abbrev BinaryThree := Fin 3 → ZMod 2
abbrev BinaryThreeTimesNine := BinaryThree × ZMod 9

def binaryPlane (W : Submodule (ZMod 2) BinaryThree) : Prop :=
  W < (⊤ : Submodule (ZMod 2) BinaryThree) ∧
    Module.finrank (ZMod 2) W = 2

def binaryAffineCoset (a : BinaryThree)
    (W : Submodule (ZMod 2) BinaryThree) : Set BinaryThree :=
  {x | ∃ w ∈ (W : Set BinaryThree), x = a + w}

/-- Claim 61314: the complete inverse-closed affine-hyperplane sector in
`C₂³ × C₉` has the ordinary undirected CI property against arbitrary
connection-set targets. -/
def binaryRankThreeC9AffineHyperplaneCI_claim61314 : Prop :=
  ∀ (W : Submodule (ZMod 2) BinaryThree) (a : BinaryThree),
    binaryPlane W →
      a ∉ (W : Set BinaryThree) →
        ∀ S : Set BinaryThreeTimesNine,
          S ⊆ (binaryAffineCoset a W ×ˢ (Set.univ : Set (ZMod 9))) →
            S ⊆ ({0} : Set BinaryThreeTimesNine)ᶜ →
              (∀ x ∈ S, -x ∈ S) →
                ∀ T : Set BinaryThreeTimesNine,
                  T ⊆ ({0} : Set BinaryThreeTimesNine)ᶜ →
                    (∀ x ∈ T, -x ∈ T) →
                      Nonempty
                          (SimpleGraph.addCayley S ≃g
                            SimpleGraph.addCayley T) →
                        ∃ A : BinaryThree ≃ₗ[ZMod 2] BinaryThree,
                          ∃ u : ZMod 9 ≃+ ZMod 9,
                            (fun x : BinaryThreeTimesNine =>
                                (A x.1, u x.2)) '' S = T

end MathlibPlus.Open.GraphTheory
