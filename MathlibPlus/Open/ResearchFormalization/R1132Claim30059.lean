import Mathlib

namespace MathlibPlus.Open.ResearchFormalization.R1132

noncomputable section

abbrev C7_30059 := ZMod 7

def translateSet30059 (B : Set C7_30059) (t : C7_30059) : Set C7_30059 :=
  {x | ∃ b ∈ B, x = b + t}

def translationDevelopment30059 (B : Set C7_30059) : Set (Set C7_30059) :=
  {C | ∃ t : C7_30059, C = translateSet30059 B t}

def pointImage30059 (π : Equiv.Perm C7_30059)
    (B : Set C7_30059) : Set C7_30059 :=
  π '' B

def developmentPreserved30059
    (B : Set C7_30059) (π : Equiv.Perm C7_30059) : Prop :=
  Set.image (pointImage30059 π) (translationDevelopment30059 B) =
    translationDevelopment30059 (pointImage30059 π B)

def relevantSubset30059 (n : ℕ) (B : Set C7_30059) : Prop :=
  B.ncard = n

def incidenceRowCount30059 (n : ℕ) : ℕ :=
  Nat.card {z : (Set C7_30059) × Equiv.Perm C7_30059 //
    relevantSubset30059 n z.1 ∧ developmentPreserved30059 z.1 z.2}

def subsetCount30059 (n : ℕ) : ℕ :=
  Nat.card {B : Set C7_30059 // relevantSubset30059 n B}

/-- The exact subset and development-isomorphism incidence census for C₇. -/
def claim30059 : Prop :=
  subsetCount30059 2 = 21 ∧
    subsetCount30059 3 = 35 ∧
    subsetCount30059 4 = 35 ∧
    subsetCount30059 5 = 21 ∧
    incidenceRowCount30059 2 = 126 ∧
    incidenceRowCount30059 3 = 798 ∧
    incidenceRowCount30059 4 = 798 ∧
    incidenceRowCount30059 5 = 126

end
end MathlibPlus.Open.ResearchFormalization.R1132
