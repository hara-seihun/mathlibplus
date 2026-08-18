import MathlibPlus.Open.ResearchFormalization.R1529Claim38235

namespace MathlibPlus.Open.ResearchFormalization.R1529Claim38161

open MathlibPlus.Open.ResearchFormalization.R1529Claim38235

/-- The exact normalized alternating chart with a specified nonzero translation. -/
def alternatingTranslationAt (q : ℕ) [NeZero q]
    (p : NormalizedAffineProfile q) (ε : ZMod q) : Prop :=
  ∀ j : Fin 8,
    p.1.a j = 1 ∧
      p.1.t j = if j.val % 2 = 0 then 0 else ε

/-- Claim 38161: every nonzero normalized alternating translation conjugates
    the displayed standard regular copy to itself. -/
def claim38161 : Prop :=
  ∀ (q : ℕ) [NeZero q],
    Nat.Prime q →
      q % 2 = 1 →
        ∀ ε : ZMod q, ε ≠ 0 →
          ∀ p : NormalizedAffineProfile q,
            alternatingTranslationAt q p ε →
              equalCopyProfile q p

end MathlibPlus.Open.ResearchFormalization.R1529Claim38161
