import MathlibPlus.Open.Research.R2214CayleyData

open scoped BigOperators

namespace MathlibPlus.Open.ResearchFormalization.R1397Claim38596

noncomputable section

abbrev F3 := ZMod 3
abbrev ShiftBase := F3 × F3
abbrev TargetBase := Fin 5 → F3
abbrev Omega := F3 × TargetBase

/-- The fixed five-coordinate quotient permutation from the quadratic normal
form. -/
def quotientMap (b : TargetBase) : TargetBase :=
  ![b 0,
    b 1,
    b 2 + b 0 * (b 0 - 1),
    b 3 + (2 * b 0 - 1) * b 1,
    b 4 + b 1 ^ 2]

def quotientMapSpec (qbar : Equiv.Perm TargetBase) : Prop :=
  ∀ b : TargetBase, qbar b = quotientMap b

/-- The lift of a normalized shift through the fixed quotient permutation. -/
def liftedShiftMapSpec (s : ShiftBase → F3)
    (q : Equiv.Perm Omega) : Prop :=
  ∀ (z : F3) (b : TargetBase),
    q (z, b) = (z + s (b 0, b 1), quotientMap b)

/-- The regular translation copy on the actual extension carrier. -/
def regularTranslationGroup : Subgroup (Equiv.Perm Omega) :=
  Subgroup.closure
    (Set.range
      (MathlibPlus.Open.Research.R2214.addTranslation :
        Omega → Equiv.Perm Omega))

def conjugateSet {α : Type*} (q : Equiv.Perm α)
    (K : Subgroup (Equiv.Perm α)) : Set (Equiv.Perm α) :=
  {g | ∃ h : K, g = q.symm * (h : Equiv.Perm α) * q}

/-- `A_s = ⟨R,R^{q_s}⟩` in the source-pure normal form. -/
def generatedGroup (q : Equiv.Perm Omega) : Subgroup (Equiv.Perm Omega) :=
  Subgroup.closure
    ((regularTranslationGroup : Set (Equiv.Perm Omega)) ∪
      conjugateSet q regularTranslationGroup)

def quotientTranslationGroup : Subgroup (Equiv.Perm TargetBase) :=
  Subgroup.closure
    (Set.range
      (MathlibPlus.Open.Research.R2214.addTranslation :
        TargetBase → Equiv.Perm TargetBase))

def quotientGeneratedGroup (qbar : Equiv.Perm TargetBase) :
    Subgroup (Equiv.Perm TargetBase) :=
  Subgroup.closure
    ((quotientTranslationGroup : Set (Equiv.Perm TargetBase)) ∪
      conjugateSet qbar quotientTranslationGroup)

/-- The mixed second difference of the shift function. -/
def mixedSecondDifference (s : ShiftBase → F3)
    (u v x : ShiftBase) : F3 :=
  s (x + u + v) - s (x + u) - s (x + v) + s x

def translatedMixedSecondDifference (s : ShiftBase → F3)
    (u v w : ShiftBase) : ShiftBase → F3 :=
  fun x => mixedSecondDifference s u v (x + w)

def constantProfile (c : F3) : ShiftBase → F3 := fun _ => c

/-- The mixed-second-difference voltage module, including its mandatory
central constant line. -/
def mixedSecondDifferenceModule (s : ShiftBase → F3) :
    Submodule F3 (ShiftBase → F3) :=
  Submodule.span F3
    ({constantProfile 1} ∪
      {h | ∃ u v w : ShiftBase,
        h = translatedMixedSecondDifference s u v w})

def constantCentralLine : Submodule F3 (ShiftBase → F3) :=
  Submodule.span F3 ({constantProfile 1} : Set (ShiftBase → F3))

/-- The central translation associated with a voltage profile. -/
def centralTranslationSpec (ell : ShiftBase → F3)
    (k : Equiv.Perm Omega) : Prop :=
  ∀ (z : F3) (b : TargetBase),
    k (z, b) = (z + ell (b 0, b 1), b)

/-- Inflation of the voltage module to the actual permutations fixing every
quotient block. -/
def inflatedBlockKernel (s : ShiftBase → F3) :
    Set (Equiv.Perm Omega) :=
  {k | ∃ ell : ShiftBase → F3,
    ell ∈ mixedSecondDifferenceModule s ∧ centralTranslationSpec ell k}

/-- The actual block kernel of the generated group, not a proxy module. -/
def actualBlockKernel (q k : Equiv.Perm Omega) : Prop :=
  k ∈ generatedGroup q ∧
    ∀ (z : F3) (b : TargetBase), (k (z, b)).2 = b

def actualBlockKernelSet (q : Equiv.Perm Omega) :
    Set (Equiv.Perm Omega) :=
  {k | actualBlockKernel q k}

def constantCentralLinePermutations : Set (Equiv.Perm Omega) :=
  {k | ∃ c : F3, centralTranslationSpec (constantProfile c) k}

def targetBasis (k : Fin 5) : TargetBase :=
  fun l => if l = k then 1 else 0

/-- A pure translation in one of the five target coordinates, lifted to the
extension without changing the central coordinate. -/
def pureTargetTranslation (k : Fin 5) : Equiv.Perm Omega :=
  MathlibPlus.Open.Research.R2214.addTranslation (0, targetBasis k)

def pureTargetGroup : Subgroup (Equiv.Perm Omega) :=
  Subgroup.closure (Set.range pureTargetTranslation)

def quadraticShift : ShiftBase → F3 := fun x => x.2 ^ 2

/-- Claim 38596: for the literal shift `s(i,j)=j²`, the actual block kernel of
`A_s` is the constant central line (via the exact mixed-second-difference
inflation), one pure target generator is absent, and the generated and fixed
quotient groups have orders `3⁸` and `3⁷`. -/
def claim38596_explicitQuadraticWitness : Prop :=
  ∃ (q : Equiv.Perm Omega) (qbar : Equiv.Perm TargetBase),
    liftedShiftMapSpec quadraticShift q ∧
      quotientMapSpec qbar ∧
      mixedSecondDifferenceModule quadraticShift = constantCentralLine ∧
        actualBlockKernelSet q = inflatedBlockKernel quadraticShift ∧
        inflatedBlockKernel quadraticShift =
          constantCentralLinePermutations ∧
          Nat.card (generatedGroup q) = 3 ^ 8 ∧
            Nat.card (quotientGeneratedGroup qbar) = 3 ^ 7 ∧
              ¬ (pureTargetGroup ≤ generatedGroup q) ∧
                ∃ k : Fin 5,
                  pureTargetTranslation k ∉ generatedGroup q

end

end MathlibPlus.Open.ResearchFormalization.R1397Claim38596
