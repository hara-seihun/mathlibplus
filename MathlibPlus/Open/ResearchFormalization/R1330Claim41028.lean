import MathlibPlus.Open.ResearchFormalization.R1330Claim41027

namespace MathlibPlus.Open.ResearchFormalization.R1330Claim41028

noncomputable section

open MathlibPlus.Open.Research.R1330Formalization_41037
open MathlibPlus.Open.ResearchFormalization.R1330Claim41027

/-- The two coordinate translations on the actual `V` carrier. -/
def xCoordinateTranslation (p : ℕ) : Equiv.Perm (V p) :=
  Equiv.addLeft (1, 0)

def yCoordinateTranslation (p : ℕ) : Equiv.Perm (V p) :=
  Equiv.addLeft (0, 1)

/-- The two displayed elementary linear transvections. -/
def firstTransvection (p : ℕ) (u : Equiv.Perm (V p)) : Prop :=
  ∀ x y : ZMod p, u (x, y) = (x, y + x)

def secondTransvection (p : ℕ) (u : Equiv.Perm (V p)) : Prop :=
  ∀ x y : ZMod p, u (x, y) = (x + y, y)

/-- A displayed permutation is the conjugate of the specified coordinate
translation by one of the exact shear/inverse-function pairs. -/
def shearConjugateOfTranslation (p : ℕ)
    (q qInv : V p → V p) (t u : Equiv.Perm (V p)) : Prop :=
  u ∈ conjugatedPointTranslationPermutations p q qInv ∧
    ∀ z : V p, u z = q (t (qInv z))

/-- The determinant-one linear permutations of the concrete pair carrier. -/
def sl2Carrier (p : ℕ) : Set (Equiv.Perm (V p)) :=
  {u | ∃ a b c d : ZMod p,
    a * d - b * c = 1 ∧
      ∀ x y : ZMod p,
        u (x, y) = (a * x + b * y, c * x + d * y)}

def sl2PermutationGroup (p : ℕ) : Subgroup (Equiv.Perm (V p)) :=
  Subgroup.closure (sl2Carrier p)

/-- The affine special-linear carrier `P ⋊ SL(2,p)` on `V`. -/
def aslCarrier (p : ℕ) : Set (Equiv.Perm (V p)) :=
  {u | ∃ a b c d t₁ t₂ : ZMod p,
    a * d - b * c = 1 ∧
      ∀ x y : ZMod p,
        u (x, y) =
          (a * x + b * y + t₁, c * x + d * y + t₂)}

/-- Claim 41028: the actual conjugates of the two coordinate translations give
 the displayed transvections after the exact translation correction; the two
transvections generate the determinant-one linear carrier, and both actual
coordinate projections contain the resulting affine special-linear carrier. -/
def claim41028 : Prop :=
  ∀ (p : ℕ) (hp : Nat.Prime p), Odd p →
    letI : NeZero p := ⟨hp.ne_zero⟩
    ∃ F : Equiv.Perm (Ω p),
      (∀ z : Ω p, F z = blockShear p z) ∧
        coordinateProjectionContainments p F ∧
          xCoordinateTranslation p ∈ pointTranslationGroup p ∧
            yCoordinateTranslation p ∈ pointTranslationGroup p ∧
              ∃ u v : Equiv.Perm (V p),
                firstTransvection p u ∧
                  secondTransvection p v ∧
                    u ∈ sl2Carrier p ∧
                      v ∈ sl2Carrier p ∧
                        (∃ cA : Equiv.Perm (V p),
                          shearConjugateOfTranslation p
                            (shearA p) (shearAInverse p)
                            (xCoordinateTranslation p) cA ∧
                            cA ∈ rotationCoordinateProjection p F ∧
                            cA ∈ reflectionCoordinateProjection p F ∧
                            u = (xCoordinateTranslation p)⁻¹ * cA ∧
                            firstTransvection p
                              ((xCoordinateTranslation p)⁻¹ * cA) ∧
                            (xCoordinateTranslation p)⁻¹ * cA ∈
                              rotationCoordinateProjection p F ∧
                            (xCoordinateTranslation p)⁻¹ * cA ∈
                              reflectionCoordinateProjection p F) ∧
                        (∃ cB : Equiv.Perm (V p),
                          shearConjugateOfTranslation p
                            (shearB p) (shearBInverse p)
                            (yCoordinateTranslation p) cB ∧
                            cB ∈ rotationCoordinateProjection p F ∧
                            cB ∈ reflectionCoordinateProjection p F ∧
                            v = (yCoordinateTranslation p)⁻¹ * cB ∧
                            secondTransvection p
                              ((yCoordinateTranslation p)⁻¹ * cB) ∧
                            (yCoordinateTranslation p)⁻¹ * cB ∈
                              rotationCoordinateProjection p F ∧
                            (yCoordinateTranslation p)⁻¹ * cB ∈
                              reflectionCoordinateProjection p F) ∧
                        Subgroup.closure
                            ({u, v} : Set (Equiv.Perm (V p))) =
                          sl2PermutationGroup p ∧
                          aslCarrier p ⊆
                            rotationCoordinateProjection p F ∧
                          aslCarrier p ⊆
                            reflectionCoordinateProjection p F

end

end MathlibPlus.Open.ResearchFormalization.R1330Claim41028
