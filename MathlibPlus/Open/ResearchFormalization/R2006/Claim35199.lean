import Mathlib

namespace MathlibPlus.Open.ResearchFormalization.R2006.Claim35199

abbrev F2 := ZMod 2
abbrev Cube (n : ℕ) := Fin n → F2

def coordinateVector {n : ℕ} (k : Fin n) : Cube n :=
  Pi.single k 1

def coordinateCharacter {n : ℕ} (k : Fin n) : Cube n →ₗ[F2] F2 :=
  LinearMap.proj k

def vanishingCoordinates {n : ℕ} (s : Finset (Fin n)) : Submodule F2 (Cube n) :=
  s.inf fun k => LinearMap.ker (coordinateCharacter k)

def pairMap {n : ℕ} {W_i W_j : Type*}
    [AddCommGroup W_i] [Module F2 W_i]
    [AddCommGroup W_j] [Module F2 W_j]
    (F_i : Cube n →ₗ[F2] W_i) (F_j : Cube n →ₗ[F2] W_j) :
    Cube n →ₗ[F2] W_i × W_j :=
  F_i.prod F_j

def pairImage {n : ℕ} {W_i W_j : Type*}
    [AddCommGroup W_i] [Module F2 W_i]
    [AddCommGroup W_j] [Module F2 W_j]
    (F_i : Cube n →ₗ[F2] W_i) (F_j : Cube n →ₗ[F2] W_j)
    (s : Finset (Fin n)) : Submodule F2 (W_i × W_j) :=
  Submodule.map (pairMap F_i F_j) (vanishingCoordinates s)

/-- The binary-cube pair-image decomposition after deleting one further coordinate. -/
def claim35199_exactPairImageThirdDeletion : Prop :=
  ∀ (n : ℕ) (W_i W_j : Type*)
    [AddCommGroup W_i] [Module F2 W_i]
    [AddCommGroup W_j] [Module F2 W_j]
    (F_i : Cube n →ₗ[F2] W_i) (F_j : Cube n →ₗ[F2] W_j)
    (i j k : Fin n),
    i ≠ j → i ≠ k → j ≠ k →
    let base_ij := vanishingCoordinates {i, j}
    let base_ij_k := vanishingCoordinates {i, j, k}
    let e_k := coordinateVector k
    let M_ij := pairImage F_i F_j {i, j}
    let P_ij_k := pairImage F_i F_j {i, j, k}
    base_ij = base_ij_k ⊔ Submodule.span F2 {e_k} ∧
      Disjoint base_ij_k (Submodule.span F2 {e_k}) ∧
      M_ij = P_ij_k ⊔ Submodule.span F2 {pairMap F_i F_j e_k} ∧
      (Module.finrank F2 M_ij = Module.finrank F2 P_ij_k ∨
       Module.finrank F2 M_ij = Module.finrank F2 P_ij_k + 1)

end MathlibPlus.Open.ResearchFormalization.R2006.Claim35199
