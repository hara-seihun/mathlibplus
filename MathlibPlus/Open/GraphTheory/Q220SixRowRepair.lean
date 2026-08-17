import MathlibPlus.Open.Research.BatchQ220_01a00154

namespace MathlibPlus.Open.GraphTheory.Q220SixRow

open MathlibPlus.Open.Research

noncomputable section

abbrev Q220 := MathlibPlus.Open.Research.Q220

def q220Inverse (a : Q220) : Q220 :=
  let even : Prop := a.2.2.val % 2 = 0
  let e11 : ZMod 11 := if even then 1 else -1
  let e5 : ZMod 5 := if even then 1 else -1
  (-(e11 * a.1),
    -(e5 * a.2.1),
    Fin.ofNat 4 ((4 - a.2.2.val) % 4))

def q220Aut (f : Q220 → Q220) : Prop :=
  Function.Bijective f ∧
    ∀ a b : Q220, f (q220Mul a b) = q220Mul (f a) (f b)

def q220Connection (S : Finset Q220) : Prop :=
  q220One ∉ S ∧ ∀ x : Q220, x ∈ S ↔ q220Inverse x ∈ S

def q220Adjacency (S : Finset Q220) (x y : Q220) : Prop :=
  x ≠ y ∧ q220Mul (q220Inverse x) y ∈ S

def q220GraphIso (S T : Finset Q220) : Prop :=
  ∃ e : Equiv.Perm Q220, ∀ x y : Q220,
    q220Adjacency S x y ↔ q220Adjacency T (e x) (e y)

def q220ExactCIAt (k : ℕ) : Prop :=
  ∀ S T : Finset Q220,
    S.card = k → T.card = k →
    q220Connection S → q220Connection T →
    (q220GraphIso S T ↔
      ∃ α : Q220 → Q220, q220Aut α ∧ T = S.image α)

/-- Claim 43651: exactly the six fixed-group rows 7, 8, 9 and their
loopless complements 212, 211, 210 have the exact CI fibre property. -/
def claim43651 : Prop :=
  q220Model ∧
    q220ExactCIAt 7 ∧
    q220ExactCIAt 8 ∧
    q220ExactCIAt 9 ∧
    q220ExactCIAt 212 ∧
    q220ExactCIAt 211 ∧
    q220ExactCIAt 210

end

end MathlibPlus.Open.GraphTheory.Q220SixRow
