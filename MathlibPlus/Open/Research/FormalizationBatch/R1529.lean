import Mathlib

namespace MathlibPlus.Open.Research.FormalizationBatch.R1529

private noncomputable instance finiteSubtypeR1529 {α : Type} [Finite α] {p : α → Prop} :
    Finite {x : α // p x} :=
  Finite.of_injective Subtype.val Subtype.val_injective

/-- The affine-permutation predicate used by the blockwise chart and affine-subgroup claims. -/
def isAffinePermutation (q : ℕ) (f : Equiv.Perm (ZMod q)) : Prop :=
  ∃ a : (ZMod q)ˣ, ∃ b : ZMod q, ∀ x : ZMod q,
    f x = (a : ZMod q) * x + b

/-- Claim 38140: a blockwise affine chart independently chooses one affine map per block. -/
def claim38140BlockwiseAffineChart
    (q : ℕ) (F : Equiv.Perm (ZMod q × Fin 8)) : Prop :=
  ∃ f : Fin 8 → Equiv.Perm (ZMod q),
    (∀ j : Fin 8, isAffinePermutation q (f j)) ∧
      ∀ x : ZMod q, ∀ j : Fin 8, F (x, j) = (f j x, j)

/-- The translation by `c` on the affine line over `ZMod q`. -/
def translation (q : ℕ) (c : ZMod q) : Equiv.Perm (ZMod q) :=
  Equiv.addRight c

/-- Claim 38144: the prime affine-subgroup translation/fixed-point dichotomy. -/
def claim38144PrimeAffineSubgroupDichotomy : Prop :=
  ∀ q : ℕ, Nat.Prime q →
    ∀ Y : Subgroup (Equiv.Perm (ZMod q)),
      (∀ g : Equiv.Perm (ZMod q), g ∈ Y → isAffinePermutation q g) →
        ((∃ c : ZMod q, c ≠ 0 ∧ translation q c ∈ Y) →
            ∀ c : ZMod q, translation q c ∈ Y) ∧
          ((¬ ∃ c : ZMod q, c ≠ 0 ∧ translation q c ∈ Y) →
            ¬ q ∣ Nat.card Y ∧
              ∃ p : ZMod q, ∀ g : Equiv.Perm (ZMod q), g ∈ Y → g p = p)

/-- An eight-block affine profile at `q = 7`, before normalization. -/
structure AffineProfileSeven where
  a : ZMod 8 → (ZMod 7)ˣ
  t : ZMod 8 → ZMod 7
  deriving Fintype

/-- Globally normalized profiles have slope one and translation zero at block zero. -/
abbrev NormalizedAffineProfileSeven :=
  {p : AffineProfileSeven // p.a 0 = 1 ∧ p.t 0 = 0}

/-- A normalized slope word periodic with respect to a nonzero block separation. -/
abbrev PeriodicSlopeWordSeven (d : ZMod 8) :=
  {a : ZMod 8 → (ZMod 7)ˣ // a 0 = 1 ∧ ∀ k : ZMod 8, a (k + d) = a k}
noncomputable def periodicSlopeCountSeven (d : ZMod 8) : ℕ :=
  Nat.card (PeriodicSlopeWordSeven d)

/-- The slope/separation/translation cases left by the periodic part of the census. -/
abbrev PeriodicHardProfileSeven :=
  {p : ZMod 8 × AffineProfileSeven //
    p.1 ≠ 0 ∧ p.2.a 0 = 1 ∧ p.2.t 0 = 0 ∧
      ∀ k : ZMod 8, p.2.a (k + p.1) = p.2.a k}

/-- Claim 38264: the exact normalized septenary profile and periodic-case census. -/
def claim38264ExactSeptenaryCensus : Prop :=
  Nat.card AffineProfileSeven = 42 ^ 8 ∧
    Nat.card NormalizedAffineProfileSeven = 42 ^ 7 ∧
    Nat.card (PeriodicSlopeWordSeven 1) = 1 ∧
    Nat.card (PeriodicSlopeWordSeven 2) = 6 ∧
    Nat.card (PeriodicSlopeWordSeven 3) = 1 ∧
    Nat.card (PeriodicSlopeWordSeven 4) = 216 ∧
    Nat.card (PeriodicSlopeWordSeven 5) = 1 ∧
    Nat.card (PeriodicSlopeWordSeven 6) = 6 ∧
    Nat.card (PeriodicSlopeWordSeven 7) = 1 ∧
    (∑ d : {d : ZMod 8 // d ≠ 0}, periodicSlopeCountSeven d) = 232 ∧
    Nat.card PeriodicHardProfileSeven = 232 * 7 ^ 7 ∧
    42 ^ 8 = 9_682_651_996_416 ∧
    42 ^ 7 = 230_539_333_248 ∧
    232 * 7 ^ 7 = 191_061_976

end MathlibPlus.Open.Research.FormalizationBatch.R1529
