import Mathlib

namespace MathlibPlus.Open.Research.R4242

abbrev B := ZMod 8
abbrev FibrePoint (m : ℕ) := B × ZMod m

def sMap (j : B) : B :=
  if j = 0 then 1 else if j = 1 then 2 else if j = 2 then 3 else
  if j = 3 then 4 else if j = 4 then 5 else if j = 5 then 6 else
  if j = 6 then 7 else 0

def tMap (j : B) : B :=
  if j = 0 then 1 else if j = 1 then 6 else if j = 2 then 3 else
  if j = 3 then 0 else if j = 4 then 5 else if j = 5 then 2 else
  if j = 6 then 7 else 4

def q1Map (j : B) : B :=
  if j = 0 then 0 else if j = 1 then 1 else if j = 2 then 6 else
  if j = 3 then 7 else if j = 4 then 4 else if j = 5 then 5 else
  if j = 6 then 2 else 3

def q2Map (j : B) : B :=
  if j = 0 then 0 else if j = 1 then 3 else if j = 2 then 2 else
  if j = 3 then 5 else if j = 4 then 4 else if j = 5 then 7 else
  if j = 6 then 6 else 1

def q3Map (j : B) : B :=
  if j = 0 then 0 else if j = 1 then 5 else if j = 2 then 6 else
  if j = 3 then 3 else if j = 4 then 4 else if j = 5 then 1 else
  if j = 6 then 2 else 7

def q4Map (j : B) : B :=
  if j = 0 then 0 else if j = 1 then 7 else if j = 2 then 2 else
  if j = 3 then 1 else if j = 4 then 4 else if j = 5 then 3 else
  if j = 6 then 6 else 5

def regularPermutationSubgroup {Ω : Type*}
    (H : Subgroup (Equiv.Perm Ω)) : Prop :=
  ∀ x y : Ω, ∃! g : H, g.1 x = y

def generatedCopy {Ω : Type*} (a b : Equiv.Perm Ω) :
    Subgroup (Equiv.Perm Ω) :=
  Subgroup.closure ({a, b} : Set (Equiv.Perm Ω))

def eCopy {m : ℕ} (a b : Equiv.Perm (FibrePoint m))
    (H : Subgroup (Equiv.Perm (FibrePoint m))) : Prop :=
  regularPermutationSubgroup H ∧
    a ^ m = 1 ∧ b ^ 8 = 1 ∧ b * a * b⁻¹ = a⁻¹

def generatedPair {Ω : Type*}
    (R T : Subgroup (Equiv.Perm Ω)) : Subgroup (Equiv.Perm Ω) :=
  Subgroup.closure ((R : Set (Equiv.Perm Ω)) ∪ (T : Set (Equiv.Perm Ω)))

def fibreTrivialLift {m : ℕ} (q : B → B)
    (c : Equiv.Perm (FibrePoint m)) : Prop :=
  ∀ j x, c (j, x) = (q j, x)

def inducesBlock {m : ℕ} (q : B → B)
    (c : Equiv.Perm (FibrePoint m)) : Prop :=
  ∀ j x, (c (j, x)).1 = q j

def identityFixed {m : ℕ} (c : Equiv.Perm (FibrePoint m)) : Prop :=
  c (0, 0) = (0, 0)

def conjugates {m : ℕ}
    (R T : Subgroup (Equiv.Perm (FibrePoint m)))
    (c : Equiv.Perm (FibrePoint m)) : Prop :=
  ∀ r, r ∈ R ↔ c⁻¹ * r * c ∈ T

def prescribedLift {m : ℕ} (q : B → B)
    (R T : Subgroup (Equiv.Perm (FibrePoint m)))
    (c : Equiv.Perm (FibrePoint m)) : Prop :=
  identityFixed c ∧ inducesBlock q c ∧ conjugates R T c

def unorderedOrbital {Ω : Type*}
    (H : Subgroup (Equiv.Perm Ω)) (u : Sym2 Ω) : Set (Sym2 Ω) :=
  Set.range (fun g : H => Sym2.map (g : Equiv.Perm Ω) u)

def fixesAllUnorderedOrbitals {Ω : Type*}
    (H : Subgroup (Equiv.Perm Ω)) (c : Equiv.Perm Ω) : Prop :=
  ∀ u v : Sym2 Ω,
    v ∈ unorderedOrbital H u ↔
      Sym2.map c v ∈ unorderedOrbital H u

def copySetup (m : ℕ) (a bs bt : Equiv.Perm (FibrePoint m)) : Prop :=
  (∀ j x, a (j, x) = (j, x + 1)) ∧
    (∀ j x, bs (j, x) = (sMap j, -x)) ∧
    (∀ j x, bt (j, x) = (tMap j, -x)) ∧
    eCopy a bs (generatedCopy a bs) ∧
    eCopy a bt (generatedCopy a bt) ∧
    Subgroup.closure ({a} : Set (Equiv.Perm (FibrePoint m))) ≤
      generatedCopy a bs ∧
    Subgroup.closure ({a} : Set (Equiv.Perm (FibrePoint m))) ≤
      generatedCopy a bt

/-- S7: the two compatible quotient maps have orbital-preserving fibre-trivial
lifts, while neither bad quotient map has an identity-fixed orbital-preserving
full-copy lift. -/
def claim53503 : Prop :=
  ∀ m : ℕ, 1 < m → Odd m →
    ∀ a bs bt : Equiv.Perm (FibrePoint m), copySetup m a bs bt →
      let R := generatedCopy a bs
      let T := generatedCopy a bt
      let X := generatedPair R T
      (∃ c₂, fibreTrivialLift q2Map c₂ ∧ conjugates R T c₂ ∧
        fixesAllUnorderedOrbitals X c₂) ∧
      (∃ c₄, fibreTrivialLift q4Map c₄ ∧ conjugates R T c₄ ∧
        fixesAllUnorderedOrbitals X c₄) ∧
      (¬ ∃ c, prescribedLift q1Map R T c ∧
        fixesAllUnorderedOrbitals X c) ∧
      (¬ ∃ c, prescribedLift q3Map R T c ∧
        fixesAllUnorderedOrbitals X c)

/-- S8: for either bad quotient row, full orbital transporters still induce
both compatible replacement maps; the obstruction concerns only a prescribed
bad quotient map. -/
def claim53504 : Prop :=
  ∀ m : ℕ, 1 < m → Odd m →
    ∀ a bs bt : Equiv.Perm (FibrePoint m), copySetup m a bs bt →
      let R := generatedCopy a bs
      let T := generatedCopy a bt
      let X := generatedPair R T
      ∀ q : Equiv.Perm B,
        (∀ j, q j = q1Map j) ∨ (∀ j, q j = q3Map j) →
        (∃ c₂, fibreTrivialLift q2Map c₂ ∧ conjugates R T c₂ ∧
          fixesAllUnorderedOrbitals X c₂) ∧
        (∃ c₄, fibreTrivialLift q4Map c₄ ∧ conjugates R T c₄ ∧
          fixesAllUnorderedOrbitals X c₄) ∧
        (¬ ∃ c, prescribedLift (fun j => q j) R T c ∧
          fixesAllUnorderedOrbitals X c)

end MathlibPlus.Open.Research.R4242
