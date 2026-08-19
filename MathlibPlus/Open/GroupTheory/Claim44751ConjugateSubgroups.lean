import Mathlib

namespace MathlibPlus.Open.GroupTheory.Claim44751

/-- The actual ambient symmetric group used by the example. -/
abbrev S3 := Equiv.Perm (Fin 3)

def a : S3 := Equiv.swap 0 1
def b : S3 := Equiv.swap 1 2
def g : S3 := Equiv.swap 0 2

def K : Subgroup S3 := Subgroup.zpowers a
def N : Subgroup S3 := Subgroup.zpowers b

/-- Distinct subgroups can nevertheless be conjugate in their actual ambient
group. -/
def claim44751_distinctSubgroupsCanBeConjugate : Prop :=
  ∃ (K N : Subgroup S3) (g : S3),
    K ≠ N ∧ K.map (MulAut.conj g).toMonoidHom = N

end MathlibPlus.Open.GroupTheory.Claim44751
