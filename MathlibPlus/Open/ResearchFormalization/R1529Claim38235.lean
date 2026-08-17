import Mathlib

namespace MathlibPlus.Open.ResearchFormalization.R1529Claim38235

noncomputable section

abbrev BlockPoint (q : ℕ) := ZMod q × Fin 8
abbrev PhasePoint (q : ℕ) := ZMod q × ZMod 8

structure AffineProfile (q : ℕ) [NeZero q] where
  a : Fin 8 → (ZMod q)ˣ
  t : Fin 8 → ZMod q
  deriving Fintype

abbrev NormalizedAffineProfile (q : ℕ) [NeZero q] :=
  {p : AffineProfile q // p.a 0 = 1 ∧ p.t 0 = 0}

/-- The change from the eight block labels to the additive phase coordinate. -/
def phaseCoordinateEquiv (q : ℕ) : BlockPoint q ≃ PhasePoint q :=
  Equiv.prodCongr (Equiv.refl (ZMod q)) (ZMod.finEquiv 8).toEquiv

def phaseSignEquiv (q : ℕ) (j : ZMod 8) : Equiv.Perm (ZMod q) :=
  if j.val % 2 = 0 then Equiv.refl (ZMod q) else Equiv.neg (ZMod q)

/-- Left multiplication in the standard `C_q ⋊ C_8` eight-block action. -/
def phaseRegularPermutation (q : ℕ) (g : PhasePoint q) :
    Equiv.Perm (PhasePoint q) :=
  Equiv.prodCongr
    ((phaseSignEquiv q g.2).trans (Equiv.addRight g.1))
    (Equiv.addRight g.2)

def regularPermutation (q : ℕ) (g : BlockPoint q) :
    Equiv.Perm (BlockPoint q) :=
  let e := phaseCoordinateEquiv q
  e.trans (phaseRegularPermutation q (e g)) |>.trans e.symm

def regularGroup (q : ℕ) : Subgroup (Equiv.Perm (BlockPoint q)) :=
  Subgroup.closure (Set.range (regularPermutation q))

/-- A normalized blockwise affine chart, retained as an explicit function so
that the statement does not hide its eight independent local charts. -/
def profileChart (q : ℕ) [NeZero q] (p : AffineProfile q) : BlockPoint q → BlockPoint q :=
  fun x =>
    ((p.a x.2 : ZMod q) * x.1 + p.t x.2, x.2)

def profileInverse (q : ℕ) [NeZero q] (p : AffineProfile q) : BlockPoint q → BlockPoint q :=
  fun x =>
    ((p.a x.2 : ZMod q)⁻¹ * (x.1 - p.t x.2), x.2)

/-- The transported regular copy, expressed directly through the displayed
chart and its explicit affine inverse. -/
def transportedRegularSet (q : ℕ) [NeZero q] (p : AffineProfile q) :
    Set (Equiv.Perm (BlockPoint q)) :=
  {u | ∃ r : Equiv.Perm (BlockPoint q), r ∈ regularGroup q ∧
    ∀ x : BlockPoint q,
      u x = profileInverse q p (r (profileChart q p x))}

def transportedRegularGroup (q : ℕ) [NeZero q] (p : AffineProfile q) :
    Subgroup (Equiv.Perm (BlockPoint q)) :=
  Subgroup.closure (transportedRegularSet q p)

def generatedPair (q : ℕ) [NeZero q] (p : AffineProfile q) :
    Subgroup (Equiv.Perm (BlockPoint q)) :=
  Subgroup.closure
    ((regularGroup q : Set (Equiv.Perm (BlockPoint q))) ∪
      transportedRegularSet q p)

/-- Membership in the ordered binary two-closure of the generated regular
pair, written without an opaque callback. -/
def inOrderedTwoClosure (q : ℕ) [NeZero q] (p : AffineProfile q) : Prop :=
  ∀ x y : BlockPoint q,
    ∃ g : Equiv.Perm (BlockPoint q),
      g ∈ generatedPair q p ∧
        profileChart q p x = g x ∧ profileChart q p y = g y

def equalCopyProfile (q : ℕ) [NeZero q] (p : NormalizedAffineProfile q) : Prop :=
  transportedRegularGroup q p.1 = regularGroup q

def alternatingTranslationProfile (q : ℕ) [NeZero q]
    (p : NormalizedAffineProfile q) : Prop :=
  ∃ ε : ZMod q, ε ≠ 0 ∧
    ∀ j : Fin 8,
      p.1.a j = 1 ∧
        p.1.t j = if j.val % 2 = 0 then 0 else ε

/-- Claim 38235: exact general-prime normalized profile count, the complete
alternating equal-copy exception, and ordered-two-closure for every remainder. -/
def claim38235 : Prop :=
  ∀ (q : ℕ) [NeZero q], Nat.Prime q → q % 2 = 1 →
    Nat.card (NormalizedAffineProfile q) =
        (q * (q - 1)) ^ 7 ∧
      Nat.card {p : NormalizedAffineProfile q // equalCopyProfile q p} = q - 1 ∧
      (∀ p : NormalizedAffineProfile q,
        equalCopyProfile q p ↔ alternatingTranslationProfile q p) ∧
      (∀ p : NormalizedAffineProfile q,
        ¬ equalCopyProfile q p → inOrderedTwoClosure q p.1)

end
end MathlibPlus.Open.ResearchFormalization.R1529Claim38235
