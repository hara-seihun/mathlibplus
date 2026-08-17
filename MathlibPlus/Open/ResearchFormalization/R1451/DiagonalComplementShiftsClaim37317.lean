import Mathlib

namespace MathlibPlus.Open.ResearchFormalization.R1451.DiagonalComplementShiftsClaim37317

private abbrev H := ZMod 6 × ZMod 6
private abbrev Ω := H ⊕ H
private abbrev PermutationGroup := Subgroup (Equiv.Perm Ω)

private def diagonalTranslation (a : H) : Equiv.Perm Ω :=
  Equiv.sumCongr (Equiv.addRight a) (Equiv.addRight a)

private def shiftedComplement (a : H) : Equiv.Perm Ω :=
  (Equiv.sumCongr (Equiv.addRight a) (Equiv.addRight (-a))).trans
    (Equiv.sumComm H H)

private def unshiftedSwap : Equiv.Perm Ω := shiftedComplement 0

private def involutory (f : Equiv.Perm Ω) : Prop :=
  ∀ x : Ω, f (f x) = x

private def blockSwap (f : Equiv.Perm Ω) : Prop :=
  (∀ h : H, ∃ h' : H, f (Sum.inl h) = Sum.inr h') ∧
  (∀ h : H, ∃ h' : H, f (Sum.inr h) = Sum.inl h')

private def fixesEachBlock (f : Equiv.Perm Ω) : Prop :=
  (∀ h : H, ∃ h' : H, f (Sum.inl h) = Sum.inl h') ∧
  (∀ h : H, ∃ h' : H, f (Sum.inr h) = Sum.inr h')

private def centralizesH (f : Equiv.Perm Ω) : Prop :=
  ∀ a : H, f * diagonalTranslation a = diagonalTranslation a * f

private def diagonalAlternating (f : Equiv.Perm Ω) : Prop :=
  ∃ p : Equiv.Perm H,
    p ∈ alternatingGroup H ∧ f = Equiv.sumCongr p p

private def normalizesDiagonalAlternating (f : Equiv.Perm Ω) : Prop :=
  ∀ g : Equiv.Perm Ω,
    diagonalAlternating g ↔
      diagonalAlternating (f * g * f⁻¹)

private def twoTorsion (a : H) : Prop :=
  a + a = 0

private def generatedWith (f : Equiv.Perm Ω) : PermutationGroup :=
  Subgroup.closure (Set.range diagonalTranslation ∪ {f})

private def conjugatesToInverse (r s : Equiv.Perm Ω) : Prop :=
  r * s * r⁻¹ = s⁻¹

/-- Claim 37317: in the diagonal alternating-strip case, the block-fixing
complement quotient is a common translation by an element of `H[2]`; there
are exactly four such shifts, and adjoining each shifted block swap gives the
same regular subgroup as adjoining the unshifted swap. -/
def claim37317 : Prop :=
  (∀ r t : Equiv.Perm Ω,
    involutory r → blockSwap r → centralizesH r →
    involutory t → blockSwap t → centralizesH t →
    normalizesDiagonalAlternating (r * t) →
    let s := r * t
    fixesEachBlock s ∧
      centralizesH s ∧
      conjugatesToInverse r s ∧
      ∃! a : H,
        twoTorsion a ∧
        s = diagonalTranslation a ∧
        (∀ h : H, s (Sum.inl h) = Sum.inl (h + a)) ∧
        (∀ h : H, s (Sum.inr h) = Sum.inr (h + a))) ∧
  Set.ncard {a : H | twoTorsion a} = 4 ∧
  (∀ a : H, twoTorsion a →
    normalizesDiagonalAlternating (diagonalTranslation a) ∧
    involutory (shiftedComplement a) ∧
    blockSwap (shiftedComplement a) ∧
    centralizesH (shiftedComplement a) ∧
    shiftedComplement a = unshiftedSwap * diagonalTranslation a ∧
    generatedWith (unshiftedSwap * diagonalTranslation a) =
      generatedWith unshiftedSwap)

end MathlibPlus.Open.ResearchFormalization.R1451.DiagonalComplementShiftsClaim37317
