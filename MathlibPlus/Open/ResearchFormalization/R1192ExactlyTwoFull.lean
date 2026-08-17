import Mathlib

namespace MathlibPlus.Open.ResearchFormalization.R1192ExactlyTwoFull

private abbrev Base := Fin 3 → ZMod 2
private abbrev Fiber := Fin 2 → ZMod 3
private abbrev Group := Base × Fiber

private def basePoint0 : Base := ![0, 0, 0]
private def basePoint1 : Base := ![1, 0, 0]
private def basePoint2 : Base := ![0, 1, 0]
private def basePoint3 : Base := ![1, 1, 0]
private def basePoint5 : Base := ![1, 0, 1]
private def basePoint6 : Base := ![0, 1, 1]
private def basePoint7 : Base := ![1, 1, 1]

private def rho1 : Equiv.Perm Base :=
  (Equiv.swap basePoint6 basePoint7).trans
    (Equiv.swap basePoint5 basePoint6)

private def support123 : Finset Base :=
  {basePoint1, basePoint2, basePoint3}

private def fiberMap
    (σ : Equiv.Perm Base)
    (q : Base → Equiv.Perm Fiber) : Group → Group :=
  fun p => (σ p.1, q p.1 p.2)

private def activeSupport (q : Base → Equiv.Perm Fiber) : Finset Base := by
  classical
  exact Finset.univ.filter
    (fun u => u ≠ basePoint0 ∧ q u ≠ Equiv.refl Fiber)

private def displacementSubgroup
    (q : Base → Equiv.Perm Fiber) (u : Base) : AddSubgroup Fiber :=
  AddSubgroup.closure
    (Set.range (fun t : Fiber => t - q u t + q u 0))

private def normalizedSupportThreeMap
    (f : Equiv.Perm Group)
    (q : Base → Equiv.Perm Fiber) : Prop :=
  rho1 basePoint0 = basePoint0 ∧
    q basePoint0 = Equiv.refl Fiber ∧
      (∀ (a : Base) (b : Fiber), f (a, b) = fiberMap rho1 q (a, b)) ∧
        activeSupport q = support123

private def exactlyTwoFullOneProper
    (q : Base → Equiv.Perm Fiber) : Prop :=
  ∃ w : Base,
    w ∈ activeSupport q ∧
      displacementSubgroup q w ≠ ⊤ ∧
        ∀ u : Base,
          u ∈ activeSupport q → u ≠ w →
            displacementSubgroup q u = ⊤

private def inverseClosedConnection (S : Finset Group) : Prop :=
  0 ∉ S ∧ ∀ x : Group, x ∈ S ↔ -x ∈ S

private def cayleyAdj (S : Finset Group) (x y : Group) : Prop :=
  x ≠ y ∧ y - x ∈ S

private def fIsCayleyIsomorphism
    (f : Equiv.Perm Group) (S T : Finset Group) : Prop :=
  ∀ x y : Group,
    cayleyAdj S x y ↔ cayleyAdj T (f x) (f y)

private def groupAutomorphismTransports
    (S T : Finset Group) : Prop :=
  ∃ α : Group ≃+ Group,
    ∀ x : Group, x ∈ S ↔ α x ∈ T

/-- Claim 41816: the exact normalized `rho1`, support-`{1,2,3}` map class
with exactly two full active displacement subgroups cannot witness an ordinary
undirected Cayley-CI failure. -/
def claim41816_exactlyTwoFullRho1SupportThreeCIHarmless : Prop :=
  ∀ (f : Equiv.Perm Group) (q : Base → Equiv.Perm Fiber),
    normalizedSupportThreeMap f q →
      exactlyTwoFullOneProper q →
        ∀ S T : Finset Group,
          inverseClosedConnection S →
            inverseClosedConnection T →
              fIsCayleyIsomorphism f S T →
                groupAutomorphismTransports S T

end MathlibPlus.Open.ResearchFormalization.R1192ExactlyTwoFull
