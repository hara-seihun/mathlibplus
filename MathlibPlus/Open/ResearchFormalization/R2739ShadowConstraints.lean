import MathlibPlus.Open.Research.SemidirectCocycle

namespace MathlibPlus.Open.ResearchFormalization.R2739

noncomputable section

abbrev H := MathlibPlus.Open.Research.SemidirectCocycle.ShadowGroup
abbrev W := MathlibPlus.Open.Research.SemidirectCocycle.ShadowModule
abbrev K := ZMod 7

private def dot (u v : W) : K :=
  u.1 * v.1 + u.2 * v.2

/-- The selected complement elements are exactly the elements with second
coordinate one in the fixed `C₁₃ ⋊ C₃` carrier. -/
def selectedComplement (S : Set H) : Prop :=
  S ⊆ {h : H | h.2 = 1}

/-- A normal family assigns one nonzero normal vector to each selected element. -/
def nonzeroNormalFamily (S : Set H) (n : ∀ h : S, W) : Prop :=
  ∀ h : S, n h ≠ 0

/-- The normalized functions obeying all selected-complement defect equations. -/
def normalizedConstraintSpace
    (S : Set H) (n : ∀ h : S, W) : Set (H → W) :=
  {τ | τ MathlibPlus.Open.Research.SemidirectCocycle.shadowIdentity = 0 ∧
    ∀ h : S, ∀ k : H,
      dot (n h)
        (MathlibPlus.Open.Research.SemidirectCocycle.twistedDefect τ h k) = 0}

/-- The cocycle-value shadow retains the same defect equations and additionally
has one common value visible through every selected normal. -/
def cocycleValueShadowSpace
    (S : Set H) (n : ∀ h : S, W) : Set (H → W) :=
  {τ | τ MathlibPlus.Open.Research.SemidirectCocycle.shadowIdentity = 0 ∧
    (∀ h : S, ∀ k : H,
      dot (n h)
        (MathlibPlus.Open.Research.SemidirectCocycle.twistedDefect τ h k) = 0) ∧
    ∃ v : W, ∀ h : S,
      dot (n h) (τ h) = dot (n h) v}

/-- Claim 42497: the search interface compares these two explicitly defined
spaces for selected complement elements and nonzero one-dimensional normals.
No equality or inequality outcome of that comparison is asserted here. -/
def selectedComplementShadowConstraints_claim42497
    (S : Set H) (n : ∀ h : S, W) : Prop :=
  selectedComplement S ∧
    nonzeroNormalFamily S n ∧
    (∀ τ : H → W,
      τ ∈ normalizedConstraintSpace S n ↔
        (τ MathlibPlus.Open.Research.SemidirectCocycle.shadowIdentity = 0 ∧
          ∀ h : S, ∀ k : H,
            dot (n h)
              (MathlibPlus.Open.Research.SemidirectCocycle.twistedDefect τ h k) = 0)) ∧
    (∀ τ : H → W,
      τ ∈ cocycleValueShadowSpace S n ↔
        (τ MathlibPlus.Open.Research.SemidirectCocycle.shadowIdentity = 0 ∧
          (∀ h : S, ∀ k : H,
            dot (n h)
              (MathlibPlus.Open.Research.SemidirectCocycle.twistedDefect τ h k) = 0) ∧
          ∃ v : W, ∀ h : S,
            dot (n h) (τ h) = dot (n h) v))

end

end MathlibPlus.Open.ResearchFormalization.R2739
