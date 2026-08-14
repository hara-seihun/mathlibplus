import Mathlib
import MathlibPlus.LinearAlgebra.CyclicSameLineProfile

open scoped BigOperators

namespace MathlibPlus.Open.LinearAlgebra.CyclicSameLineConsequences

open MathlibPlus.LinearAlgebra.CyclicSameLineProfile

noncomputable section

private def edgeImage {d : ℕ} (M : Submodule (ZMod 3)
    (TernaryBase d → Plane)) (x y : TernaryBase d) : Set Plane :=
  {z | ∃ k : TernaryBase d → Plane, k ∈ M ∧ k y - k x = z}

private def diagonalLine (basis : Module.Basis (Fin 2) (ZMod 3) Plane) : Set Plane :=
  AddSubgroup.closure {basis 0 + basis 1}

/-- Claim 39756: outside the common order-three line, the pair-difference image
of the explicit cyclic same-line module is the whole plane. -/
def claim39756_pairDifferenceImageOffCommonLine : Prop :=
  ∀ (d : ℕ) (u : TernaryBase d), (hu : u ≠ 0) →
    ∀ (basis : Module.Basis (Fin 2) (ZMod 3) Plane)
      (h : TernaryBase d) (hh : h ∈ ternaryLine u) (hh0 : h ≠ 0),
      ∀ (x y : TernaryBase d), y - x ∉ ternaryLine u →
        edgeImage (profileModule u hu basis h hh hh0) x y = Set.univ

/-- Claim 39757: on a nonzero common-line edge, the explicit cyclic same-line
module has exactly the diagonal line as its pair-difference image. -/
def claim39757_commonLineEdgeImageDiagonal : Prop :=
  ∀ (d : ℕ) (u : TernaryBase d), (hu : u ≠ 0) →
    ∀ (basis : Module.Basis (Fin 2) (ZMod 3) Plane)
      (h : TernaryBase d) (hh : h ∈ ternaryLine u) (hh0 : h ≠ 0),
      ∀ (x y : TernaryBase d),
        y - x ∈ ternaryLine u → y - x ≠ 0 →
        edgeImage (profileModule u hu basis h hh hh0) x y =
          diagonalLine basis

private def translateProfile {d : ℕ} (z : TernaryBase d)
    (k : TernaryBase d → Plane) : TernaryBase d → Plane :=
  fun x => k (x + z)

private def translationInvariant {d : ℕ}
    (K : Submodule (ZMod 3) (TernaryBase d → Plane)) : Prop :=
  ∀ (z : TernaryBase d) (k : TernaryBase d → Plane),
    k ∈ K → translateProfile z k ∈ K

/-- Claim 39758: one nondiagonal common-line edge in a translation-invariant
kernel completes every ordered pair image. -/
def claim39758_nondiagonalEdgeCompletesPairImages : Prop :=
  ∀ (d : ℕ) (u : TernaryBase d), (hu : u ≠ 0) →
    ∀ (basis : Module.Basis (Fin 2) (ZMod 3) Plane)
      (h : TernaryBase d) (hh : h ∈ ternaryLine u) (hh0 : h ≠ 0),
      ∀ (K : Submodule (ZMod 3) (TernaryBase d → Plane)),
        translationInvariant K →
        profileModule u hu basis h hh hh0 ≤ K →
        (∃ (x₀ : TernaryBase d) (k : TernaryBase d → Plane),
          k ∈ K ∧ k (x₀ + u) - k x₀ ∉ diagonalLine basis) →
        ∀ (x y : TernaryBase d), x ≠ y →
          edgeImage K x y = Set.univ

end

end MathlibPlus.Open.LinearAlgebra.CyclicSameLineConsequences
