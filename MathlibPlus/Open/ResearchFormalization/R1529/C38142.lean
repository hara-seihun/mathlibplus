import Mathlib

namespace MathlibPlus.Open.ResearchFormalization.R1529C38142

noncomputable section

abbrev Block := ZMod 8
abbrev Line (q : ℕ) := ZMod q
abbrev Slope (q : ℕ) := (ZMod q)ˣ
abbrev Pair (q : ℕ) := ZMod q × ZMod q

def affineMap (q : ℕ) (hp : Nat.Prime q)
    (a : Slope q) (t : Line q) : Equiv.Perm (Line q) := by
  letI : Fact (Nat.Prime q) := ⟨hp⟩
  exact (Equiv.smulRight (Units.ne_zero a)).trans (Equiv.addRight t)

def normalizedSlopeWord (a : Block → Slope q) : Prop := a 0 = 1
def normalizedTranslationWord (t : Block → Line q) : Prop := t 0 = 0

def periodicSlope (a : Block → Slope q) (d : Block) : Prop :=
  ∀ k : Block, a (k + d) = a k

def nonperiodicSlope (a : Block → Slope q) (d : Block) : Prop :=
  ¬ periodicSlope a d

def slopeRatio (a : Block → Slope q) (k : Block) : Slope q :=
  a (k + 1) * (a k)⁻¹

def deltaShift (t : Block → Line q) (d k : Block) : Line q :=
  t (k + d) - t k

def gammaShift (t : Block → Line q) (d k : Block) : Line q :=
  (-1 : Line q) ^ k.val * deltaShift t d k

def phiMap (q : ℕ) (hp : Nat.Prime q)
    (a : Block → Slope q) (t : Block → Line q) (d k : Block) :
    Equiv.Perm (Line q) :=
  affineMap q hp (a k) (gammaShift t d k)

def shiftedDerivative (q : ℕ) (hp : Nat.Prime q)
    (a : Block → Slope q) (t : Block → Line q) (d k : Block) :
    Equiv.Perm (Line q) :=
  (phiMap q hp a t d k).symm.trans (phiMap q hp a t d (k + 1))

def projectedDerivativeGroup (q : ℕ) (hp : Nat.Prime q)
    (a : Block → Slope q) (t : Block → Line q) (d : Block) :
    Subgroup (Equiv.Perm (Line q)) :=
  Subgroup.closure (Set.range (shiftedDerivative q hp a t d))

def translationPlaneGenerated (q : ℕ)
    (source target : Pair q) : AddSubgroup (Pair q) :=
  AddSubgroup.closure ({source, target} : Set (Pair q))

def sourceDiagonalTranslation (q : ℕ) (c : Line q) : Equiv.Perm (Pair q) :=
  Equiv.addRight (c, c)

def shiftedTargetTranslation (q : ℕ) (a0 a1 : Line q) (c : Line q) :
    Equiv.Perm (Pair q) :=
  Equiv.addRight (a0 * c, a1 * c)

def evenNonzeroSeparation (d : Block) : Prop :=
  d ≠ 0 ∧ d.val % 2 = 0

def shiftOrbit (d k : Block) : Finset Block := by
  classical
  exact Finset.univ.filter (fun j =>
    ∃ n : Fin 8, j = k + (n.val : Block) * d)

def orbitSum (t : Block → Line q) (d k : Block) : Line q :=
  ∑ j ∈ shiftOrbit d k, deltaShift t d j

def gammaConstantOnOrbit
    (t : Block → Line q) (d k : Block) : Prop :=
  ∀ j ∈ shiftOrbit d k, gammaShift t d j = gammaShift t d k

def slopeConstantOnOrbit
    (a : Block → Slope q) (d k : Block) : Prop :=
  ∀ j ∈ shiftOrbit d k, a j = a k

/-- Claim 38142: a nonperiodic normalized slope word supplies unequal-slope
source/target translations whose generated vector subgroup is the full
ordered two-coordinate translation plane. -/
def claim38142_nonperiodicSlopePairsGenerateFullPlane : Prop :=
  ∀ (q : ℕ) (hp : Nat.Prime q) (d : Block)
    (a : Block → Slope q),
    d ≠ 0 → normalizedSlopeWord a → nonperiodicSlope a d →
      ∃ k : Block, ∃ c : Line q,
        c ≠ 0 ∧
        (a k : Line q) ≠ (a (k + d) : Line q) ∧
        sourceDiagonalTranslation q c ≠
          shiftedTargetTranslation q (a k) (a (k + d)) c ∧
        translationPlaneGenerated q (c, c)
            ((a k : Line q) * c, (a (k + d) : Line q) * c) = ⊤


end

end MathlibPlus.Open.ResearchFormalization.R1529C38142
