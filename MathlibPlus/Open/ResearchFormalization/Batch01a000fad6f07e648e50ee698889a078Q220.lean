import Mathlib

namespace MathlibPlus.Open.ResearchFormalization.BatchQ220

abbrev Q220 := ZMod 11 × ZMod 5 × ZMod 4

def q220Mul (g h : Q220) : Q220 :=
  (g.1 + ((-1 : ZMod 11) ^ g.2.2.val) * h.1,
    g.2.1 + ((-1 : ZMod 5) ^ g.2.2.val) * h.2.1,
    g.2.2 + h.2.2)

def q220One : Q220 := (0, 0, 0)

def q220Inv (g : Q220) : Q220 :=
  (-(((-1 : ZMod 11) ^ g.2.2.val) * g.1),
    -(((-1 : ZMod 5) ^ g.2.2.val) * g.2.1),
    -g.2.2)

def q220GroupLaw : Prop :=
  (∀ x y z : Q220, q220Mul (q220Mul x y) z = q220Mul x (q220Mul y z)) ∧
    (∀ x : Q220, q220Mul q220One x = x ∧ q220Mul x q220One = x) ∧
    (∀ x : Q220,
      q220Mul x (q220Inv x) = q220One ∧
        q220Mul (q220Inv x) x = q220One)

def q220Pow (g : Q220) : Nat → Q220
  | 0 => q220One
  | n + 1 => q220Mul g (q220Pow g n)

def q220HasOrder (g : Q220) (n : Nat) : Prop :=
  q220Pow g n = q220One ∧
    ∀ m : Nat, 0 < m → m < n → q220Pow g m ≠ q220One

def q220A : Q220 := (1, 0, 0)

def q220B : Q220 := (0, 1, 0)

def q220C : Q220 := (0, 0, 1)

/-- Claim 44380: the displayed sign semidirect product is the group of order
220 with the three indicated generator orders. -/
def claim_44380 : Prop :=
  q220GroupLaw ∧
    Fintype.card Q220 = 220 ∧
    q220HasOrder q220A 11 ∧
    q220HasOrder q220B 5 ∧
    q220HasOrder q220C 4

/-- Claim 44402: the same explicitly displayed semidirect-product carrier has
order 220 and inversion action on both odd factors. -/
def claim_44402 : Prop :=
  q220GroupLaw ∧
    Fintype.card Q220 = 11 * 5 * 4 ∧
    (∀ (x X : ZMod 11) (y Y : ZMod 5) (i j : ZMod 4),
      q220Mul (x, y, i) (X, Y, j) =
        (x + ((-1 : ZMod 11) ^ i.val) * X,
          y + ((-1 : ZMod 5) ^ i.val) * Y,
          i + j))

end MathlibPlus.Open.ResearchFormalization.BatchQ220
