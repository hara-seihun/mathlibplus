import Mathlib

namespace MathlibPlus.Open.CIBinaryTimesC9AlternatingFlagCographs

abbrev CayleyGroup (r : ℕ) := (Fin r → ZMod 2) × ZMod 9

def alternatingSet {r m : ℕ}
    (D : Fin (Nat.succ m) → AddSubgroup (CayleyGroup r)) : Set (CayleyGroup r) :=
  {x | (x ∈ D ⟨0, Nat.zero_lt_succ m⟩ ∧ x ≠ 0) ∨
    ∃ j : Fin m,
      (j.val + 1) % 2 = 0 ∧
        x ∈ D ⟨j.val + 1, Nat.succ_lt_succ j.isLt⟩ ∧
          x ∉ D ⟨j.val, Nat.lt_trans j.isLt (Nat.lt_succ_self m)⟩}

def identityFree {r : ℕ} (T : Set (CayleyGroup r)) : Prop :=
  (0 : CayleyGroup r) ∉ T

def inverseClosed {r : ℕ} (T : Set (CayleyGroup r)) : Prop :=
  ∀ ⦃x : CayleyGroup r⦄, x ∈ T → -x ∈ T

def cayleyAdjacency {r : ℕ} (S : Set (CayleyGroup r))
    (x y : CayleyGroup r) : Prop :=
  x ≠ y ∧ y - x ∈ S

def cayleyGraphsIsomorphic {r : ℕ}
    (S T : Set (CayleyGroup r)) : Prop :=
  ∃ e : CayleyGroup r ≃ CayleyGroup r,
    ∀ x y : CayleyGroup r,
      (cayleyAdjacency S x y ↔ cayleyAdjacency T (e x) (e y))

def strictChain {r m : ℕ}
    (D : Fin (Nat.succ m) → AddSubgroup (CayleyGroup r)) : Prop :=
  D ⟨m, Nat.lt_succ_self m⟩ = ⊤ ∧
    ∀ j : Fin m,
      D ⟨j.val, Nat.lt_trans j.isLt (Nat.lt_succ_self m)⟩ <
        D ⟨j.val + 1, Nat.succ_lt_succ j.isLt⟩

def claim60162 : Prop :=
  ∀ r m : ℕ,
    ∀ D : Fin (Nat.succ m) → AddSubgroup (CayleyGroup r),
      strictChain D →
        let S := alternatingSet D
        S ⊆ (Set.univ : Set (CayleyGroup r)) \ {0} ∧
          inverseClosed S ∧
          ∀ T : Set (CayleyGroup r),
            identityFree T →
              inverseClosed T →
                cayleyGraphsIsomorphic S T →
                  ∃ α : CayleyGroup r ≃+ CayleyGroup r, α '' S = T

end MathlibPlus.Open.CIBinaryTimesC9AlternatingFlagCographs
