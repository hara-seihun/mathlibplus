import MathlibPlus.Basic

namespace MathlibPlus.GroupTheory.Claim41247

/-- The identity-base fiber map associated with an arbitrary family of
permutations `q_h`.  The only structural hypothesis in the source is that
`q 1` is the identity; it is kept as a theorem-level premise rather than
assuming homomorphism or affine structure. -/
noncomputable def identityBaseFiberMap {V H : Type*} [One H]
    (q : H → Equiv.Perm V) : V × H → V × H :=
  fun x => (q x.2 x.1, x.2)

theorem identityBaseFiberMap_is_identity_on_one {V H : Type*} [One H]
    (q : H → Equiv.Perm V) (hq : q 1 = 1) (v : V) :
    identityBaseFiberMap q (v, 1) = (v, 1) := by
  simp [identityBaseFiberMap, hq]

theorem identityBaseFiberMap_fst {V H : Type*} [One H]
    (q : H → Equiv.Perm V) (v : V) (h : H) :
    (identityBaseFiberMap q (v, h)).1 = q h v := rfl

theorem identityBaseFiberMap_snd {V H : Type*} [One H]
    (q : H → Equiv.Perm V) (v : V) (h : H) :
    (identityBaseFiberMap q (v, h)).2 = h := rfl

end MathlibPlus.GroupTheory.Claim41247
