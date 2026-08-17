import MathlibPlus.Open.Groups.CyclicFourMinimumTwo

namespace MathlibPlus.Open.ResearchFormalization.Q0051QuadraticForms

noncomputable section

open MathlibPlus.Open.Groups

abbrev F3 := ZMod 3
abbrev Vector2 := Fin 2 → F3
abbrev GL2 := Matrix.GeneralLinearGroup (Fin 2) F3
abbrev QuadraticForm := F3 × (F3 × F3)

/-- The homogeneous quadratic polynomial represented by `(a,b,c)`. -/
def formValue (q : QuadraticForm) (v : Vector2) : F3 :=
  q.1 * (v 0) ^ 2 + q.2.1 * (v 0) * (v 1) + q.2.2 * (v 1) ^ 2

def nonzeroForm (q : QuadraticForm) : Prop :=
  q ≠ (0, (0, 0))

def formEquivalent (q r : QuadraticForm) : Prop :=
  ∃ M : GL2, ∃ u : F3ˣ, ∀ v : Vector2,
    formValue r v = (u : F3) * formValue q (Matrix.mulVec (M : Matrix (Fin 2) (Fin 2) F3) v)

def quadraticOrbit (q : QuadraticForm) : Set QuadraticForm :=
  {r | nonzeroForm r ∧ formEquivalent q r}

def rankOneForm : QuadraticForm := (1, (0, 0))
def splitRankTwoForm : QuadraticForm := (1, (0, -1))
def anisotropicRankTwoForm : QuadraticForm := (1, (0, 1))

abbrev QuotientCarrier := cyclicFourMinimumTwoQuotient

def quadraticShear (q : QuadraticForm) (w : QuotientCarrier) : QuotientCarrier :=
  if w.1 = 1 then
    (w.1, (w.2.1, (w.2.2.1, w.2.2.2 + formValue q (fun i =>
      if i = 0 then w.2.1 else w.2.2.1))))
  else w

def movedBlockCount (q : QuadraticForm) : ℕ :=
  (Finset.univ.filter (fun w : QuotientCarrier =>
    quadraticShear q w ≠ w)).card

def shearCycleSet (q : QuadraticForm) (w : QuotientCarrier) : Set QuotientCarrier :=
  {u | u = w ∨ u = quadraticShear q w ∨
    u = quadraticShear q (quadraticShear q w)}

def shearHasCycleType (q : QuadraticForm) (fixedCycles threeCycles : ℕ) : Prop :=
  (∀ w : QuotientCarrier,
      quadraticShear q (quadraticShear q (quadraticShear q w)) = w) ∧
    Set.ncard {w : QuotientCarrier | quadraticShear q w = w} = fixedCycles ∧
    (∀ w : QuotientCarrier, quadraticShear q w ≠ w →
      (shearCycleSet q w).ncard = 3) ∧
    Set.ncard {O : Set QuotientCarrier |
      ∃ w : QuotientCarrier, quadraticShear q w ≠ w ∧
        O = shearCycleSet q w} = threeCycles

/-- Claim 16161: the 26 nonzero ternary quadratic forms split into the three
exact GL/output-scaling orbits, with the displayed moved-block counts and
quotient cycle types. -/
def claim16161_ternaryQuadraticFormOrbits : Prop :=
  Set.ncard {q : QuadraticForm | nonzeroForm q} = 26 ∧
    Set.ncard (quadraticOrbit rankOneForm) = 8 ∧
    Set.ncard (quadraticOrbit splitRankTwoForm) = 12 ∧
    Set.ncard (quadraticOrbit anisotropicRankTwoForm) = 6 ∧
    (∀ q : QuadraticForm, nonzeroForm q →
      q ∈ quadraticOrbit rankOneForm ∨
        q ∈ quadraticOrbit splitRankTwoForm ∨
          q ∈ quadraticOrbit anisotropicRankTwoForm) ∧
    ¬ formEquivalent rankOneForm splitRankTwoForm ∧
    ¬ formEquivalent rankOneForm anisotropicRankTwoForm ∧
    ¬ formEquivalent splitRankTwoForm anisotropicRankTwoForm ∧
    movedBlockCount rankOneForm = 18 ∧
    movedBlockCount splitRankTwoForm = 12 ∧
    movedBlockCount anisotropicRankTwoForm = 24 ∧
    shearHasCycleType rankOneForm 36 6 ∧
    shearHasCycleType splitRankTwoForm 42 4 ∧
    shearHasCycleType anisotropicRankTwoForm 30 8

end

end MathlibPlus.Open.ResearchFormalization.Q0051QuadraticForms
