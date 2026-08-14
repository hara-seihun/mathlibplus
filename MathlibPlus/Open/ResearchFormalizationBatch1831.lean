import Mathlib

namespace MathlibPlus.Open.ResearchFormalizationBatch1831

def claim32706 : Prop :=
  ∀ (p : ℕ), (hp : Nat.Prime p) → Odd p →
    letI : Fact (Nat.Prime p) := ⟨hp⟩
    let P := Projectivization (ZMod p) (Fin 2 → ZMod p)
    letI : Fintype P := Fintype.ofFinite P
    letI : DecidableEq P := Classical.decEq P
    Fintype.card P = p + 1 ∧ Fintype.card (P → Fin 5) = 5 ^ (p + 1)

abbrev C7 : Type := ZMod 7 × ZMod 7

abbrev C7Atom : Type :=
  {s : Finset C7 // ∃ v : C7, v ≠ 0 ∧ s = {v, -v}}

abbrev C7Line [Fact (Nat.Prime 7)] : Type :=
  Projectivization (ZMod 7) C7

noncomputable def c7Representative (a : C7Atom) : C7 := Classical.choose a.property

noncomputable def c7LineOfAtom [Fact (Nat.Prime 7)] (a : C7Atom) : C7Line :=
  Projectivization.mk (ZMod 7) (c7Representative a) (Classical.choose_spec a.property).1

def claim32714 [Fact (Nat.Prime 7)] (ell : C7Line) (c : C7Atom → Fin 5) : Prop :=
  letI : Fintype C7Atom := Fintype.ofFinite C7Atom
  letI : Fintype C7Line := Fintype.ofFinite C7Line
  letI : DecidableEq C7Line := Classical.decEq C7Line
  Fintype.card C7Atom = 24 ∧
    Fintype.card C7Line = 8 ∧
    (∀ line : C7Line,
      Fintype.card {a : C7Atom // c7LineOfAtom a = line} = 3) ∧
    (∀ line : C7Line, line ≠ ell →
      ∃ color : Fin 5, ∀ a : C7Atom, c7LineOfAtom a = line → c a = color) ∧
    ¬ ∃ color : Fin 5, ∀ a : C7Atom, c7LineOfAtom a = ell → c a = color

def claim32715 [Fact (Nat.Prime 7)] : Prop :=
  letI : Fintype C7Atom := Fintype.ofFinite C7Atom
  letI : Fintype C7Line := Fintype.ofFinite C7Line
  letI : DecidableEq C7Line := Classical.decEq C7Line
  let nonconstantPredicate : (C7Atom → Fin 5) → C7Line → Prop :=
    fun c ell => ¬ ∃ color : Fin 5, ∀ a : C7Atom, c7LineOfAtom a = ell → c a = color
  let fixedSlice (ell : C7Line) :=
    {c : C7Atom → Fin 5 //
      Fintype.card C7Atom = 24 ∧
      Fintype.card C7Line = 8 ∧
      (∀ line : C7Line,
        Fintype.card {a : C7Atom // c7LineOfAtom a = line} = 3) ∧
      (∀ line : C7Line, line ≠ ell →
        ∃ color : Fin 5, ∀ a : C7Atom, c7LineOfAtom a = line → c a = color) ∧
      nonconstantPredicate c ell}
  letI : ∀ ell : C7Line, Fintype (fixedSlice ell) :=
    fun _ => Fintype.ofFinite (fixedSlice _)
  let tier := Σ ell : C7Line, fixedSlice ell
  letI : Fintype tier := Fintype.ofFinite tier
  Fintype.card tier = 75_000_000 ∧
    ∀ ell : C7Line, Fintype.card (fixedSlice ell) = 9_375_000

end MathlibPlus.Open.ResearchFormalizationBatch1831
