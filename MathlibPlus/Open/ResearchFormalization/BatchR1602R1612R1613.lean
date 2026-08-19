import Mathlib

namespace MathlibPlus.Open.ResearchFormalization.BatchR1602R1612R1613

noncomputable section

attribute [local instance] Classical.decEq Classical.propDecidable

private abbrev F3 := ZMod 3
private abbrev PlaneDomain39534 := Fin 4 → F3
private abbrev PlaneCodomain39534 := Fin 2 → F3

private def p039534 : PlaneDomain39534 := ![0, 0, 0, 1]
private def p139534 : PlaneDomain39534 := ![1, 0, 0, 1]
private def w039534 : PlaneCodomain39534 := ![1, 0]
private def w139534 : PlaneCodomain39534 := ![0, 1]

private def planeSection39534 (x : PlaneDomain39534) : PlaneCodomain39534 :=
  if x = p039534 then w039534 else if x = p139534 then w139534 else 0

private def planeSupport39534 : Set PlaneDomain39534 :=
  {x | planeSection39534 x ≠ 0}

private def planeValues39534 : Fin 2 → PlaneCodomain39534 :=
  ![w039534, w139534]

/-- Claim 39534: the exact two-point common-line plane section, including its
support, z-translation difference, and basis values. -/
def claim39534_sameLineTwoPointPlaneSection : Prop :=
  planeSection39534 p039534 = w039534 ∧
    planeSection39534 p139534 = w139534 ∧
      (∀ x : PlaneDomain39534,
        x ≠ p039534 → x ≠ p139534 → planeSection39534 x = 0) ∧
        planeSupport39534 = ({p039534, p139534} : Set PlaneDomain39534) ∧
          Set.ncard planeSupport39534 = 2 ∧
            p139534 - p039534 = ![1, 0, 0, 0] ∧
              LinearIndependent F3 planeValues39534 ∧
                Submodule.span F3 (Set.range planeValues39534) = ⊤

private abbrev CarryDomain39535 := Fin 3 → F3

private def nonzeroCarryPoints39535 : Set CarryDomain39535 :=
  {x | x ≠ 0}

private def topCarryFamily39535 : Set (CarryDomain39535 → F3) :=
  {t |
    t 0 = 0 ∧
      Set.ncard (Function.support t) = 2 ∧
        Function.support t ⊆ nonzeroCarryPoints39535 ∧
          ∀ x ∈ Function.support t, t x = 1 ∨ t x = 2}

/-- Claim 39535: the source finite-field top-carry carrier is retained as
functions on `F₃³`, with zero at the origin, exactly two nonzero support points,
and the two nonzero values at each support point. -/
def claim39535_exactTwoPositionTopCarryFamily : Prop :=
  Set.ncard nonzeroCarryPoints39535 = 26 ∧
    Set.ncard topCarryFamily39535 = 1300 ∧
      Set.ncard topCarryFamily39535 = Nat.choose 26 2 * 2 ^ 2

/-- Claim 39631: the independently admitted R-1613 size statement uses the
same fully specified two-position top-carry family. -/
def claim39631_topCarryFamilyCard : Prop :=
  Set.ncard topCarryFamily39535 = 1300 ∧
    Set.ncard topCarryFamily39535 = Nat.choose 26 2 * 2 ^ 2

private def regularPermutationSubgroup39620 {Ω : Type*}
    (H : Subgroup (Equiv.Perm Ω)) : Prop :=
  ∀ a b : Ω, ∃! h : H, h.1 a = b

private def orbitRelation39620 {Ω : Type*}
    (H : Subgroup (Equiv.Perm Ω)) (a b : Ω) : Prop :=
  ∃ h : H, h.1 a = b

/-- Claim 39620: the regular evaluation map is specified by its exact
point-fixing intertwining law, conjugates the two regular copies, and carries
equal corresponding subgroup orbit partitions to themselves. -/
def claim39620_regularActionPointFixingConjugator : Prop :=
  ∀ (Ω : Type*) [Nonempty Ω]
    (R T : Subgroup (Equiv.Perm Ω)) (α : Ω) (θ : R ≃* T),
    regularPermutationSubgroup39620 R →
      regularPermutationSubgroup39620 T →
        ∃ f : Equiv.Perm Ω,
          f α = α ∧
            (∀ r : R, ∀ p : Ω,
              f (r.1 p) = (θ r).1 (f p)) ∧
              (∀ r : R, f (r.1 α) = (θ r).1 α) ∧
                (∀ g : Equiv.Perm Ω,
                  g ∈ T ↔
                    ∃ r : R, r.1 ∈ (R : Set (Equiv.Perm Ω)) ∧
                      g = f * r.1 * f⁻¹) ∧
                  (∀ A B : Subgroup (Equiv.Perm Ω),
                    A ≤ R → B ≤ T →
                      (∀ g : Equiv.Perm Ω,
                        g ∈ B ↔
                          ∃ a : A, g = f * a.1 * f⁻¹) →
                      (∀ x y : Ω,
                        orbitRelation39620 A x y ↔
                          orbitRelation39620 B x y) →
                      (∀ x y : Ω,
                        orbitRelation39620 A x y ↔
                          orbitRelation39620 A (f x) (f y)))

end
end MathlibPlus.Open.ResearchFormalization.BatchR1602R1612R1613
