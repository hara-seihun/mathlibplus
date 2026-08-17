import Mathlib

namespace MathlibPlus.Open.ResearchFormalization.R1148

noncomputable section

open Classical

abbrev AffinePlane31555 := Fin 2 → ZMod 7
abbrev LinearGroup31555 :=
  LinearMap.GeneralLinearGroup (ZMod 7) AffinePlane31555

def pairVector31555 (u v : ZMod 7) : AffinePlane31555 :=
  ![u, v]

def kernelConnectionSet31555
    (Q I : Finset (ZMod 7)) : Set AffinePlane31555 :=
  {v | (∃ i, i ∈ I ∧ v = pairVector31555 0 i) ∨
    (∃ q, q ∈ Q ∧ ∃ y : ZMod 7, v = pairVector31555 q y)}

def kernelAdjacency31555
    (Q I : Finset (ZMod 7))
    (x y : AffinePlane31555) : Prop :=
  x ≠ y ∧ y - x ∈ kernelConnectionSet31555 Q I

def zeroAutomorphismSet31555
    (Q I : Finset (ZMod 7)) : Set (Equiv.Perm AffinePlane31555) :=
  {g | g 0 = 0 ∧
    ∀ x y, kernelAdjacency31555 Q I x y ↔
      kernelAdjacency31555 Q I (g x) (g y)}

def zeroStabilizer31555
    (Q I : Finset (ZMod 7)) :
    Subgroup (Equiv.Perm AffinePlane31555) :=
  Subgroup.closure (zeroAutomorphismSet31555 Q I)

def triangularLinearMap31555
    (g : Equiv.Perm AffinePlane31555) : Prop :=
  ∃ ε c d : ZMod 7,
    (ε = 1 ∨ ε = -1) ∧ d ≠ 0 ∧
      ∀ x : AffinePlane31555,
        g x = pairVector31555 (ε * x 0) (c * x 0 + d * x 1)

def linearMapPermutation31555
    (L : LinearGroup31555) : Equiv.Perm AffinePlane31555 :=
  (L.toLinearEquiv).toEquiv

def linearIntersection31555
    (Q I : Finset (ZMod 7)) : Set (Equiv.Perm AffinePlane31555) :=
  {g | g ∈ zeroStabilizer31555 Q I ∧
    ∃ L : LinearGroup31555, g = linearMapPermutation31555 L}

/-- Claim 31555: all four explicit kernel graphs have the stated zero
stabilizer order, and their linear intersection is precisely the 84-map
triangular family. -/
def claim31555 : Prop :=
  ∀ Q I : Finset (ZMod 7),
    (Q = {-1, 1} ∨ Q = {-1, 1, -2, 2}) →
    (I = ∅ ∨ I = (Finset.univ : Finset (ZMod 7)).erase 0) →
    Nat.card {g : Equiv.Perm AffinePlane31555 //
      g ∈ zeroStabilizer31555 Q I} =
      23601831786829578240000000 ∧
    Nonempty (zeroStabilizer31555 Q I ≃*
      (Equiv.Perm (Fin 6) ×
        (Fin 6 → Equiv.Perm (Fin 7)) × Multiplicative (ZMod 2))) ∧
    Nat.card {g : Equiv.Perm AffinePlane31555 //
      g ∈ linearIntersection31555 Q I} = 84 ∧
    (∀ L : LinearGroup31555,
      linearMapPermutation31555 L ∈ zeroStabilizer31555 Q I ↔
        triangularLinearMap31555 (linearMapPermutation31555 L))

end
end MathlibPlus.Open.ResearchFormalization.R1148
