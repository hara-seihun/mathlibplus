import MathlibPlus.Open.Research.R1330Claim41037

namespace MathlibPlus.Open.ResearchFormalization.R1330Claim41027

open MathlibPlus.Open.Research.R1330Formalization_41037

noncomputable section

/-- The regular translation subgroup on the concrete point carrier V. -/
def pointTranslationGroup (p : ℕ) : Subgroup (Equiv.Perm (V p)) :=
  Subgroup.closure (Set.range (fun v : V p => Equiv.addLeft v))

/-- Conjugation of the concrete translation subgroup by a displayed shear.
 The maps q and qInv are the explicit A,A⁻¹ or B,B⁻¹ formulas. -/
def conjugatedPointTranslationPermutations (p : ℕ)
    (q qInv : V p → V p) : Set (Equiv.Perm (V p)) :=
  {a | ∃ t : pointTranslationGroup p,
    ∀ z : V p,
      a z = q (((t : Equiv.Perm (V p)) (qInv z)))}

/-- The two displayed shears have the explicit inverse maps used by the
 conjugates and by the mixed map. -/
def shearAInverse (p : ℕ) : V p → V p :=
  fun z => (z.1, z.2 - binomTwo p z.1)

def shearBInverse (p : ℕ) : V p → V p :=
  fun z => (z.1 - binomTwo p z.2, z.2)

/-- The mixed map g = B A⁻¹ on the exact V carrier. -/
def mixedShear (p : ℕ) : V p → V p :=
  fun z => shearB p (shearAInverse p z)

/-- The restriction to one common permutation on the three rotation blocks. -/
def rotationCoordinateProjection (p : ℕ) (F : Equiv.Perm (Ω p)) :
    Set (Equiv.Perm (V p)) :=
  {a | ∃ b : Equiv.Perm (V p), ∃ k : Equiv.Perm (Ω p),
    blockKernel p F k ∧ actsAsPair p a b k}

/-- The restriction to one common permutation on the three reflection blocks. -/
def reflectionCoordinateProjection (p : ℕ) (F : Equiv.Perm (Ω p)) :
    Set (Equiv.Perm (V p)) :=
  {b | ∃ a : Equiv.Perm (V p), ∃ k : Equiv.Perm (Ω p),
    blockKernel p F k ∧ actsAsPair p a b k}

/-- The singleton set of the explicitly displayed mixed permutation, expressed
 without introducing an unverified Equiv structure for its formula. -/
def mixedShearPermutations (p : ℕ) : Set (Equiv.Perm (V p)) :=
  {g | ∀ z : V p, g z = mixedShear p z}

/-- Every kernel element has one common restriction on each of the two
 three-block families. -/
def commonCoordinateRestrictions (p : ℕ) (F : Equiv.Perm (Ω p)) : Prop :=
  ∀ k : Equiv.Perm (Ω p), blockKernel p F k →
    ∃ a b : Equiv.Perm (V p), actsAsPair p a b k

/-- The two coordinate projections contain P, P^A, P^B, and the mixed map. -/
def coordinateProjectionContainments (p : ℕ) (F : Equiv.Perm (Ω p)) : Prop :=
  (pointTranslationGroup p : Set (Equiv.Perm (V p))) ⊆
      rotationCoordinateProjection p F ∧
    (pointTranslationGroup p : Set (Equiv.Perm (V p))) ⊆
      reflectionCoordinateProjection p F ∧
      conjugatedPointTranslationPermutations p (shearA p) (shearAInverse p) ⊆
        rotationCoordinateProjection p F ∧
        conjugatedPointTranslationPermutations p (shearA p) (shearAInverse p) ⊆
          reflectionCoordinateProjection p F ∧
          conjugatedPointTranslationPermutations p (shearB p) (shearBInverse p) ⊆
            rotationCoordinateProjection p F ∧
            conjugatedPointTranslationPermutations p (shearB p) (shearBInverse p) ⊆
              reflectionCoordinateProjection p F ∧
              mixedShearPermutations p ⊆ rotationCoordinateProjection p F ∧
                mixedShearPermutations p ⊆ reflectionCoordinateProjection p F

/-- Claim 41027: the concrete six-block kernel has common rotation and
 reflection restrictions, and both coordinate projections contain the
 displayed translation, conjugate-translation, and mixed maps. -/
def claim41027 : Prop :=
  ∀ p : ℕ, ∀ hp : Nat.Prime p, Odd p →
    letI : NeZero p := ⟨hp.ne_zero⟩
    ∃ F : Equiv.Perm (Ω p),
      (∀ z : Ω p, F z = blockShear p z) ∧
        commonCoordinateRestrictions p F ∧
          coordinateProjectionContainments p F

end

end MathlibPlus.Open.ResearchFormalization.R1330Claim41027
