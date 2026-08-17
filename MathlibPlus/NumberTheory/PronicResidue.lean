import MathlibPlus.NumberTheory.PronicImage

namespace MathlibPlus.NumberTheory.PronicResidue

noncomputable section

open Classical

/-- The pronic map on the natural-number interval. -/
def pronicValue (u : ℕ) : ℕ := u * (u + 1)

/-- The exact pronic image `S_X`. -/
def pronicImage (X : ℕ) : Finset ℕ :=
  (Finset.Icc 0 X).image pronicValue

/-- Claim 35346's high-prime injectivity statement on the full interval
`0, ..., X`. -/
def pronic_injective_mod_prime : Prop :=
  ∀ (X p : ℕ),
    Nat.Prime p →
      2 * X + 1 < p →
        ∀ (u v : ℕ),
          u ∈ Finset.Icc 0 X →
            v ∈ Finset.Icc 0 X →
              Nat.ModEq p (pronicValue u) (pronicValue v) →
                u = v

/-- Claim 35346's consequence for every residue class of a prime above the
`2X+1` threshold. -/
def pronic_residue_class_subsingleton : Prop :=
  ∀ (X p : ℕ),
    Nat.Prime p →
      2 * X + 1 < p →
        ∀ a : ZMod p,
          ((pronicImage X).filter (fun y : ℕ => (y : ZMod p) = a)).card ≤ 1

end

end MathlibPlus.NumberTheory.PronicResidue
