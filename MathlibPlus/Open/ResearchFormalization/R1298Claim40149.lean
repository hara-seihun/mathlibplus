import Mathlib

namespace MathlibPlus.Open.ResearchFormalization.R1298Claim40149

noncomputable section

abbrev LocalVector := Fin 3 → ZMod 2
abbrev LocalPermutation := Equiv.Perm LocalVector

/-- The canonical chart alphabet: the identity and the transpositions of two
 distinct nonzero vectors. -/
def isCanonicalChart (c : LocalPermutation) : Prop :=
  c = 1 ∨
    ∃ a b : LocalVector,
      a ≠ 0 ∧ b ≠ 0 ∧ a ≠ b ∧ c = Equiv.swap a b

abbrev CanonicalChart := {c : LocalPermutation // isCanonicalChart c}

abbrev ChartTriple := CanonicalChart × CanonicalChart × CanonicalChart

def canonicalChartCard : Prop :=
  Nat.card CanonicalChart = 22

/-- Translation by a vector in `C₂³`. -/
def localTranslation (a : LocalVector) : LocalPermutation :=
  Equiv.addRight a

/-- The local derivative generator from Record 5. -/
def localDerivativeGenerator
    (i j k : CanonicalChart) (a : LocalVector) : LocalPermutation :=
  (i : LocalPermutation)⁻¹ *
      localTranslation ((j : LocalPermutation) a) *
        (k : LocalPermutation) * localTranslation a

def localDerivativeGroup
    (i j k : CanonicalChart) : Subgroup LocalPermutation :=
  Subgroup.closure
    (Set.range (localDerivativeGenerator i j k))

def localPermutationOrbit (H : Subgroup LocalPermutation) (x : LocalVector) :
    Set LocalVector :=
  {y | ∃ h : H, (h : LocalPermutation) x = y}

/-- Record 5: the section chart fixes every orbit of its local derivative
 group setwise. -/
def recordFiveOrbitCondition (i j k : CanonicalChart) : Prop :=
  ∀ x : LocalVector,
    Set.image (i : LocalPermutation)
        (localPermutationOrbit (localDerivativeGroup i j k) x) =
      localPermutationOrbit (localDerivativeGroup i j k) x

def localActionTransitive (i j k : CanonicalChart) : Prop :=
  ∀ x y : LocalVector,
    ∃ h : localDerivativeGroup i j k,
      (h : LocalPermutation) x = y

def tripleFirst (t : ChartTriple) : CanonicalChart := t.1
def tripleSecond (t : ChartTriple) : CanonicalChart := t.2.1
def tripleThird (t : ChartTriple) : CanonicalChart := t.2.2

def tripleRecordFive (t : ChartTriple) : Prop :=
  recordFiveOrbitCondition (tripleFirst t) (tripleSecond t) (tripleThird t)

def tripleTransitive (t : ChartTriple) : Prop :=
  localActionTransitive (tripleFirst t) (tripleSecond t) (tripleThird t)

/-- Claim 40149: the complete canonical triple census, including the exact
transitive/intransitive split and zero Record-5 violations. -/
def claim40149 : Prop :=
  canonicalChartCard ∧
    22 ^ 3 = 10648 ∧
      Nat.card ChartTriple = 10648 ∧
        Nat.card {t : ChartTriple // tripleTransitive t} = 4536 ∧
          Nat.card {t : ChartTriple // ¬tripleTransitive t} = 6112 ∧
            Nat.card {t : ChartTriple // ¬tripleRecordFive t} = 0

end

end MathlibPlus.Open.ResearchFormalization.R1298Claim40149
