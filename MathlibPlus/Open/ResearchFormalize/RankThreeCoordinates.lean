import Mathlib

namespace MathlibPlus.Open.ResearchFormalize

/-- The two-dimensional `𝔽₇` coordinate used for the middle component. -/
abbrev RankThreeVector := ZMod 7 × ZMod 7

/-- Points `(b,(x,y),i)` in the finite rank-three replay. -/
structure RankThreePoint where
  b : ZMod 7
  n : RankThreeVector
  i : ZMod 3
deriving DecidableEq, Fintype

/-- The powers of `2` indexed by the three elements of `C₃`. -/
def rankThreeTwoPow (i : ZMod 3) : ZMod 7 :=
  2 ^ i.val

/-- The powers of `2` indexed by the negative of the three elements of `C₃`. -/
def rankThreeTwoNegPow (j : ZMod 3) : ZMod 7 :=
  2 ^ (-j).val

/-- The right-action coordinate multiplication from the finite replay. -/
def rankThreeRightMul (a z : RankThreePoint) : RankThreePoint :=
  { b := rankThreeTwoNegPow z.i * (a.b + z.b)
    n := a.n + rankThreeTwoPow a.i • z.n
    i := a.i + z.i }

/-- Group-law content of the coordinate setup, stated without an unproved instance. -/
def IsGroupLaw {α : Type*} (op : α → α → α) (one : α) : Prop :=
  (∀ a b c, op (op a b) c = op a (op b c)) ∧
    (∀ a, op one a = a ∧ op a one = a) ∧
    (∀ a, ∃ b, op a b = one ∧ op b a = one)

/-- Sign codes and their action on the `C₃` coordinate. -/
def RankThreeSignCode :=
  {ε : ZMod 7 → ZMod 3 // ∀ b, ε b = 1 ∨ ε b = -1}

def rankThreeSignMap (ε : RankThreeSignCode) (s : RankThreePoint) : RankThreePoint :=
  { s with i := ε.1 s.b * s.i }

/--
The exact finite coordinate setup: the displayed multiplication is a group
law on 1029 points, and the sign-code map has the stated coordinate formula.
-/
def rankThreeCoordinateSetupClaim : Prop :=
  Fintype.card RankThreePoint = 1029 ∧
    IsGroupLaw rankThreeRightMul
      ({ b := 0, n := (0, 0), i := 0 } : RankThreePoint) ∧
    (∀ (a z : RankThreePoint),
      rankThreeRightMul a z =
        { b := 2 ^ (-z.i).val * (a.b + z.b)
          n := a.n + (2 ^ a.i.val : ZMod 7) • z.n
          i := a.i + z.i }) ∧
    (∀ (ε : RankThreeSignCode) (s : RankThreePoint),
      rankThreeSignMap ε s =
        { b := s.b, n := s.n, i := ε.1 s.b * s.i })

end MathlibPlus.Open.ResearchFormalize
