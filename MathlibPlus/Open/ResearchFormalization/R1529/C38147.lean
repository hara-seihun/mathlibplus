import Mathlib

namespace MathlibPlus.Open.ResearchFormalization.R1529C38147

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

/-- Claim 38147: for an even nonzero separation, the two/four-point shift
orbits remain in one parity class; the common-fixed-point telescope forces the
shifted correction to vanish on every orbit in odd characteristic. -/
def claim38147_evenSeparationDefectsVanish : Prop :=
  ∀ (q : ℕ) (hp : Nat.Prime q), 2 < q →
    ∀ (d : Block), evenNonzeroSeparation d →
      (∀ k : Block,
        (d = 4 → (shiftOrbit d k).card = 2) ∧
        ((d = 2 ∨ d = 6) → (shiftOrbit d k).card = 4) ∧
        ∀ j ∈ shiftOrbit d k, j.val % 2 = k.val % 2) ∧
      ∀ (a : Block → Slope q) (t : Block → Line q),
        normalizedSlopeWord a → normalizedTranslationWord t →
        periodicSlope a d →
        ∀ z₀ u : Line q,
          (∀ k : Block,
            gammaShift t d k = z₀ - u * (a k : Line q)) →
          (IsUnit (2 : Line q) ∧ IsUnit (4 : Line q)) ∧
          (∀ k : Block,
            slopeConstantOnOrbit a d k ∧
              gammaConstantOnOrbit t d k ∧
              orbitSum t d k = 0) ∧
          ∀ k : Block, gammaShift t d k = 0

end

end MathlibPlus.Open.ResearchFormalization.R1529C38147
