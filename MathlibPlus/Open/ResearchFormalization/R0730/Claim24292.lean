import Mathlib

namespace MathlibPlus.Open.ResearchFormalization.R0730.Claim24292

noncomputable section

abbrev Dihedral (m : ℕ) := DihedralGroup (2 * m)

private def rotation (m : ℕ) (k : ZMod (2 * m)) : Dihedral m :=
  DihedralGroup.r k

private def reflection (m : ℕ) : Dihedral m :=
  DihedralGroup.sr 0

private abbrev RotationIndex (m : ℕ) :=
  {k : ℕ // 1 ≤ k ∧ k ≤ m}

private def targetRotationAtom (m : ℕ) (k : RotationIndex m) : Set (Dihedral m) :=
  if Even k.1 then
    {rotation m (k.1 : ZMod (2 * m)),
      rotation m (-(k.1 : ZMod (2 * m)))}
  else
    {rotation m ((1 : ZMod (2 * m)) + (k.1 : ZMod (2 * m))) * reflection m,
      rotation m ((1 : ZMod (2 * m)) - (k.1 : ZMod (2 * m))) * reflection m}

private def halfTurnTarget (m : ℕ) : Set (Dihedral m) :=
  {rotation m (m : ZMod (2 * m))}

private def otherReflectionTarget (m : ℕ) : Set (Dihedral m) :=
  {rotation m (1 : ZMod (2 * m)) * reflection m}

private def targetAtomFamily (m : ℕ) : Set (Set (Dihedral m)) :=
  Set.range (targetRotationAtom m) ∪
    {halfTurnTarget m, otherReflectionTarget m}

private def pairwiseDisjointFamily {G : Type*}
    (family : Set (Set G)) : Prop :=
  ∀ A ∈ family, ∀ B ∈ family, A ≠ B → Disjoint A B

/-- Claim 24292: the target atoms of the complete mixed-prism atom family
are pairwise disjoint in the exact dihedral carrier. -/
def claim24292 : Prop :=
  ∀ (m : ℕ), 3 ≤ m → Odd m →
    pairwiseDisjointFamily (targetAtomFamily m)

end

end MathlibPlus.Open.ResearchFormalization.R0730.Claim24292
