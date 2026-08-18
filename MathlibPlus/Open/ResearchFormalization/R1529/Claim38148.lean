import MathlibPlus.Open.ResearchFormalization.R1529Claim38235
import MathlibPlus.Open.ResearchFormalization.R1529.C38146

namespace MathlibPlus.Open.ResearchFormalization.R1529.Claim38148

abbrev Block := MathlibPlus.Open.ResearchFormalization.R1529C38146.Block
abbrev Line (q : ℕ) := MathlibPlus.Open.ResearchFormalization.R1529C38146.Line q
abbrev Profile (q : ℕ) [NeZero q] :=
  MathlibPlus.Open.ResearchFormalization.R1529Claim38235.NormalizedAffineProfile q

def oddSeparation (d : Block) : Prop :=
  d.val % 2 = 1

def coprimeWithEight (d : Block) : Prop :=
  Nat.gcd d.val 8 = 1

def normalizedProfileData (q : ℕ) [NeZero q] (p : Profile q) : Prop :=
  MathlibPlus.Open.ResearchFormalization.R1529C38146.normalizedSlopeWord p.1.a ∧
    MathlibPlus.Open.ResearchFormalization.R1529C38146.normalizedTranslationWord p.1.t

def translationFree (q : ℕ) [NeZero q] (hp : Nat.Prime q)
    (p : Profile q) (d : Block) : Prop :=
  ¬ ∃ c : Line q, c ≠ 0 ∧
    Equiv.addRight c ∈
      MathlibPlus.Open.ResearchFormalization.R1529C38146.projectedDerivativeGroup
        q hp p.1.a p.1.t d

def gammaConstantAt (q : ℕ) [NeZero q] (hp : Nat.Prime q)
    (p : Profile q) (d : Block) (Γ : Line q) : Prop :=
  ∀ k : Block,
    MathlibPlus.Open.ResearchFormalization.R1529C38146.gammaShift p.1.t d k = Γ

def identityDifferenceMap (q : ℕ) [NeZero q] (hp : Nat.Prime q)
    (p : Profile q) (d : Block) : Prop :=
  ∀ k : Block,
    MathlibPlus.Open.ResearchFormalization.R1529C38146.phiMap
        q hp p.1.a p.1.t d k = Equiv.refl (Line q)

def alternatingPureTranslationProfileAt
    (q : ℕ) [NeZero q] (p : Profile q) (ε : Line q) : Prop :=
  (∀ j : Block, p.1.a j = 1) ∧
    ∀ j : Block,
      p.1.t j = if j.val % 2 = 0 then 0 else ε

/-- Claim 38148: an odd separation has unit gcd with eight; in the
translation-free periodic case, normalized slopes are trivial and the common
Gamma value has precisely the zero identity and nonzero alternating-
translation alternatives. -/
def claim38148 : Prop :=
  (∀ d : Block, oddSeparation d → coprimeWithEight d) ∧
    ∀ (q : ℕ) [NeZero q],
      ∀ hp : Nat.Prime q, q % 2 = 1 →
        ∀ (p : Profile q) (d : Block),
          normalizedProfileData q p →
            oddSeparation d →
              MathlibPlus.Open.ResearchFormalization.R1529C38146.periodicSlope
                  p.1.a d →
                (∀ j : Block, p.1.a j = 1) ∧
                  (translationFree q hp p d →
                    (∃ Γ : Line q,
                      gammaConstantAt q hp p d Γ ∧
                        ((Γ = 0 → identityDifferenceMap q hp p d) ∧
                          (Γ ≠ 0 →
                            alternatingPureTranslationProfileAt q p Γ))) ∧
                      (∀ ε : Line q, ε ≠ 0 →
                        (gammaConstantAt q hp p d ε ↔
                          alternatingPureTranslationProfileAt q p ε)))

end MathlibPlus.Open.ResearchFormalization.R1529.Claim38148
