import Mathlib

namespace MathlibPlus.Open.ResearchFormalizationBatch_20260817_R1253

noncomputable section

abbrev RepairSpiderXY30632 := MvPolynomial (Fin 2) ℤ

local notation "Xₛ" => (MvPolynomial.X (0 : Fin 2) : RepairSpiderXY30632)
local notation "Yₛ" => (MvPolynomial.X (1 : Fin 2) : RepairSpiderXY30632)

/-- The long-end `L`, `q`, and `h` in the two-variable polynomial ring. -/
def repairL30632 : RepairSpiderXY30632 := 1 + Xₛ

def repairQ30632 : RepairSpiderXY30632 := Xₛ ^ 2 + Xₛ + 1

def repairH30632 (a b : ℕ) : RepairSpiderXY30632 :=
  repairL30632 ^ a * repairQ30632 ^ (b - 1)

/-- The separate endpoint-rooted `P₃` base polynomial. -/
def repairP3Base30632 : RepairSpiderXY30632 :=
  Xₛ ^ 3 + Xₛ ^ 2 + Xₛ + 1 + Yₛ

/-- The `B` coefficient, with the `d=1` base case kept separate from the
long-end formula. -/
def repairB30632 (a b : ℕ) : RepairSpiderXY30632 :=
  if a + b = 1 then
    Xₛ ^ 3 + Xₛ ^ 2 + Xₛ + 1
  else
    repairH30632 a b + Xₛ ^ (1 + a + 2 * b - 2) * repairQ30632

/-- The `A` coefficient, with the endpoint-rooted `P₃` base case explicit. -/
def repairA30632 (a b : ℕ) : RepairSpiderXY30632 :=
  if a + b = 1 then
    1
  else
    let d := a + b
    (repairQ30632 + repairL30632 + 1) * repairH30632 a b -
      Xₛ ^ (1 + a + 2 * b - 4) *
        (Xₛ ^ 3 +
          MvPolynomial.C (((d + 1 : ℕ) : ℤ)) * Xₛ ^ 2 +
          MvPolynomial.C (((d + 1 : ℕ) : ℤ)) * Xₛ +
          MvPolynomial.C (((d - 1 : ℕ) : ℤ)))

def repairLongEndFactor30632 (a b : ℕ) : RepairSpiderXY30632 :=
  repairB30632 a b + Yₛ * repairA30632 a b

/-- Claim 30632: after retaining the separate endpoint-rooted `P₃` base
case, every long-end factor is irreducible in `ℤ[x,y]`. -/
def claim30632 : Prop :=
  ∀ (a b : ℕ), 0 < b →
    Irreducible (repairLongEndFactor30632 a b)

end
end MathlibPlus.Open.ResearchFormalizationBatch_20260817_R1253
