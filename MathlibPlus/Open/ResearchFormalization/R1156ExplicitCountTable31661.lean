import MathlibPlus.Open.ResearchFormalization.R1156Claim31657_31660

namespace MathlibPlus.Open.ResearchFormalization.R1156ExplicitCountTable31661

open MathlibPlus.Open.ResearchFormalization.R1156

noncomputable section

structure CountRow where
  allAssignments : ℕ
  solvableOffsets : ℕ
  compatibleFamilies : ℕ
  nonaffineSolvable : ℕ

def countRow {k : ℕ} (hk : 2 ≤ k) : CountRow :=
  { allAssignments := Nat.card (NormalizedOffsetAssignments k hk)
    solvableOffsets := Nat.card (SolvableOffsetAssignments k hk)
    compatibleFamilies := Nat.card (CompatibleStateFamilies k hk)
    nonaffineSolvable :=
      Nat.card {z : NormalizedOffsetAssignments k hk //
        assignmentIsSolvable z ∧ ¬assignmentIsAffine z} }

def formulaRow (k : ℕ) : CountRow :=
  { allAssignments := Nat.choose 7 k * 7 ^ (k - 1)
    solvableOffsets := 7 * Nat.choose 7 k
    compatibleFamilies := 84 * 7 * Nat.choose 7 k
    nonaffineSolvable := 0 }

def displayedRows : Fin 6 → CountRow :=
  ![
    { allAssignments := 147, solvableOffsets := 147,
      compatibleFamilies := 12348, nonaffineSolvable := 0 },
    { allAssignments := 1715, solvableOffsets := 245,
      compatibleFamilies := 20580, nonaffineSolvable := 0 },
    { allAssignments := 12005, solvableOffsets := 245,
      compatibleFamilies := 20580, nonaffineSolvable := 0 },
    { allAssignments := 50421, solvableOffsets := 147,
      compatibleFamilies := 12348, nonaffineSolvable := 0 },
    { allAssignments := 117649, solvableOffsets := 49,
      compatibleFamilies := 4116, nonaffineSolvable := 0 },
    { allAssignments := 117649, solvableOffsets := 7,
      compatibleFamilies := 588, nonaffineSolvable := 0 }
  ]

/-- Claim 31661: the complete normalized-offset classification has exactly
its six displayed support-size rows, including the zero nonaffine-solvable
column. -/
def claim31661 : Prop :=
  (∀ (k : ℕ) (hk : 2 ≤ k),
    k ≤ 7 → countRow hk = formulaRow k) ∧
    (∀ i : Fin 6,
      formulaRow (i.1 + 2) = displayedRows i)

end

end MathlibPlus.Open.ResearchFormalization.R1156ExplicitCountTable31661
