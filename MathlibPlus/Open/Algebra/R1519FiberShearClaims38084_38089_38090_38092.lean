import Mathlib
import MathlibPlus.Open.Research.OrbitalCriteria

noncomputable section

namespace MathlibPlus.Open.Algebra.R1519FiberShear

abbrev F3 := ZMod 3

/-- The fiber-shear function on the direct-sum carrier `X × V`. -/
def fiberShearFunction {X V : Type} [AddGroup V]
    (f : X → V) : X × V → X × V :=
  fun p => (p.1, p.2 + f p.1)

/-- A permutation is the displayed fiber shear, without introducing a
proof-bearing equivalence constructor in the open registry. -/
def isFiberShear {X V : Type} [AddGroup V]
    (f : X → V) (q : Equiv.Perm (X × V)) : Prop :=
  ∀ p, q p = fiberShearFunction f p

/-- The standard regular translation subgroup on the additive carrier. -/
def standardTranslationGroup {Ω : Type} [AddGroup Ω] :
    Subgroup (Equiv.Perm Ω) :=
  Subgroup.closure
    (MathlibPlus.Open.Research.OrbitalCriteria.translationSet : Set (Equiv.Perm Ω))

/-- The subgroup conjugated by a displayed permutation. -/
def conjugatedGroup {Ω : Type}
    (N : Subgroup (Equiv.Perm Ω)) (q : Equiv.Perm Ω) :
    Subgroup (Equiv.Perm Ω) :=
  Subgroup.closure
    (MathlibPlus.Open.Research.OrbitalCriteria.conjugateSet q
      (N : Set (Equiv.Perm Ω)))

/-- The exact generated group `H = ⟨N,N^{q_f},-I⟩`. -/
def generatedShearGroup {Ω : Type} [InvolutiveNeg Ω]
    (N : Subgroup (Equiv.Perm Ω)) (q : Equiv.Perm Ω) :
    Subgroup (Equiv.Perm Ω) :=
  Subgroup.closure
    ((N : Set (Equiv.Perm Ω)) ∪
      MathlibPlus.Open.Research.OrbitalCriteria.conjugateSet q
        (N : Set (Equiv.Perm Ω)) ∪
      ({Equiv.neg Ω} : Set (Equiv.Perm Ω)))

/-- A linear correction added to a shear function. -/
def correctedShearFunction {X V : Type}
    [AddCommGroup V] (f : X → V)
    {K : Type} [Semiring K] [AddCommGroup X] [Module K X]
    [Module K V] (ell : X →ₗ[K] V) : X → V :=
  fun x => f x + ell x

def twoIndependentDirections {X : Type} [AddCommGroup X]
    [Module F3 X] (e₀ e₁ : X) : Prop :=
  ∀ a b : F3, a • e₀ + b • e₁ = 0 → a = 0 ∧ b = 0

/-- Claim 38084: adding a linear correction leaves the conjugate regular
translation subgroup unchanged, with the generated `H` setup retained. -/
def fiberShearCorrectionEquivalence_claim38084 : Prop := by
  classical
  exact ∀ {X V : Type}
    [Fintype X] [AddCommGroup X] [Module F3 X]
    [FiniteDimensional F3 X]
    [Fintype V] [AddCommGroup V] [Module F3 V]
    [FiniteDimensional F3 V]
    (f : X → V) (ell : X →ₗ[F3] V),
    let Ω := X × V
    let N := standardTranslationGroup (Ω := Ω)
    ∃ qf qc : Equiv.Perm Ω,
      isFiberShear f qf ∧
      isFiberShear (correctedShearFunction f ell) qc ∧
      let H := generatedShearGroup N qf
      generatedShearGroup N qf = H ∧
        conjugatedGroup N qc = conjugatedGroup N qf

/-- Claim 38089: for every nonzero marked direction, a correction vanishing
on that direction has the exact conjugacy, suborbit-fixing, and 2-closure
conclusions for the generated `H = ⟨N,N^{q_f},-I⟩`. -/
def oneFixedTernaryPlaneShear_claim38089 : Prop := by
  classical
  exact ∀ {X V : Type}
    [Fintype X] [AddCommGroup X] [Module F3 X]
    [FiniteDimensional F3 X]
    [Fintype V] [AddCommGroup V] [Module F3 V]
    [FiniteDimensional F3 V]
    (f : X → V) (e : X),
    e ≠ 0 → Module.finrank F3 V ≤ 2 →
    ∃ ell : X →ₗ[F3] V,
      ell e = 0 ∧
      ∃ qf qc : Equiv.Perm (X × V),
        isFiberShear f qf ∧
        isFiberShear (correctedShearFunction f ell) qc ∧
        let N := standardTranslationGroup (Ω := X × V)
        let H := generatedShearGroup N qf
        conjugatedGroup N qc = conjugatedGroup N qf ∧
          MathlibPlus.Open.Research.OrbitalCriteria.fixesStabilizerOrbits
            qc (H : Set (Equiv.Perm (X × V))) 0 ∧
          qc ∈ MathlibPlus.Open.Research.OrbitalCriteria.twoClosureOf
            (H : Set (Equiv.Perm (X × V)))

/-- Claim 38090: in the generated shear group, conjugacy of the standard
translation group together with setwise fixation of every H₀-suborbit gives
membership in the exact ordered-pair 2-closure. -/
def suborbitFixingImpliesTwoClosureMembership_claim38090 : Prop := by
  classical
  exact ∀ {X V : Type}
    [AddCommGroup X] [Module F3 X]
    [AddCommGroup V] [Module F3 V]
    (f : X → V) (qf q : Equiv.Perm (X × V)),
    isFiberShear f qf →
    (∃ ell : X →ₗ[F3] V,
      isFiberShear (correctedShearFunction f ell) q) →
    let N := standardTranslationGroup (Ω := X × V)
    let H := generatedShearGroup N qf
    conjugatedGroup N q = conjugatedGroup N qf →
    MathlibPlus.Open.Research.OrbitalCriteria.fixesStabilizerOrbits
      q (H : Set (Equiv.Perm (X × V))) 0 →
    q ∈ MathlibPlus.Open.Research.OrbitalCriteria.twoClosureOf
      (H : Set (Equiv.Perm (X × V)))

/-- Claim 38092: if the shear is invariant in one direction and two marked
vectors are independent, the same correction can be chosen to vanish on both,
while retaining the exact generated-group closure conclusions. -/
def compatibleTwoFixedCorrection_claim38092 : Prop := by
  classical
  exact ∀ {X V : Type}
    [Fintype X] [AddCommGroup X] [Module F3 X]
    [FiniteDimensional F3 X]
    [Fintype V] [AddCommGroup V] [Module F3 V]
    [FiniteDimensional F3 V]
    (f : X → V) (e₀ e₁ : X),
    e₀ ≠ 0 → twoIndependentDirections e₀ e₁ →
    Module.finrank F3 V ≤ 2 →
    (∀ x : X, f (x + e₀) = f x) →
    ∃ ell : X →ₗ[F3] V,
      ell e₀ = 0 ∧ ell e₁ = 0 ∧
      ∃ qf qc : Equiv.Perm (X × V),
        isFiberShear f qf ∧
        isFiberShear (correctedShearFunction f ell) qc ∧
        let N := standardTranslationGroup (Ω := X × V)
        let H := generatedShearGroup N qf
        conjugatedGroup N qc = conjugatedGroup N qf ∧
          MathlibPlus.Open.Research.OrbitalCriteria.fixesStabilizerOrbits
            qc (H : Set (Equiv.Perm (X × V))) 0 ∧
          qc ∈ MathlibPlus.Open.Research.OrbitalCriteria.twoClosureOf
            (H : Set (Equiv.Perm (X × V)))

end MathlibPlus.Open.Algebra.R1519FiberShear
