import MathlibPlus.Basic

namespace MathlibPlus.Combinatorics

/-- Claim 30543: the normalized nonautomorphisms of the four-element cyclic
set are one double coset under pre- and postcomposition by inversion. -/
theorem normalized_c4_nonautomorphisms_one_double_coset_claim30543 :
    let inv : Equiv.Perm (ZMod 4) := Equiv.swap (1 : ZMod 4) 3
    let representative : Equiv.Perm (ZMod 4) := Equiv.swap (2 : ZMod 4) 3
    let normalized : Finset (Equiv.Perm (ZMod 4)) :=
      Finset.univ.filter (fun π => π 0 = 0)
    let automorphism : Equiv.Perm (ZMod 4) → Prop :=
      fun π => ∀ x y : ZMod 4, π (x + y) = π x + π y
    let nonautomorphisms : Finset (Equiv.Perm (ZMod 4)) :=
      normalized.filter (fun π => ¬automorphism π)
    let doubleCoset : Finset (Equiv.Perm (ZMod 4)) :=
      {representative, representative * inv, inv * representative,
        inv * representative * inv}
    nonautomorphisms = doubleCoset ∧ representative ∈ nonautomorphisms := by
  native_decide

end MathlibPlus.Combinatorics
