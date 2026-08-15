import Mathlib

noncomputable section
open scoped BigOperators
open Set MeasureTheory

namespace MathlibPlus.Open.ResearchFormalization.Batch

/-- The binary quotient-line construction. -/
def isHyperplane2 {r : ℕ} (H : Submodule (ZMod 2) (Fin r → ZMod 2)) : Prop :=
  ∃ ℓ : (Fin r → ZMod 2) →ₗ[ZMod 2] ZMod 2,
    ℓ ≠ 0 ∧ H = ℓ.ker

def hyperplaneFinset2 {r : ℕ}
    (H : Submodule (ZMod 2) (Fin r → ZMod 2)) : Finset (Fin r → ZMod 2) := by
  classical
  exact Finset.univ.filter (fun x => x ∈ H)

def quotientLine2 {r : ℕ}
    (t u : Fin r → ZMod 2) : Finset (Fin r → ZMod 2) :=
  {t, t + u}

def quotientSet2 {r : ℕ}
    (H : Submodule (ZMod 2) (Fin r → ZMod 2))
    (t u : Fin r → ZMod 2) : Finset (Fin r → ZMod 2) :=
  hyperplaneFinset2 H ∪ {t + u}

def translateFinset2 {r : ℕ}
    (S : Finset (Fin r → ZMod 2)) (v : Fin r → ZMod 2) :
    Finset (Fin r → ZMod 2) :=
  S.image (fun x => x + v)

def claim36549 : Prop :=
  ∀ (r : ℕ)
    (H : Submodule (ZMod 2) (Fin r → ZMod 2))
    (u : Fin r → ZMod 2),
    2 ≤ r → isHyperplane2 H → u ∉ H →
    let q : ℕ := 2 ^ r
    (hyperplaneFinset2 H).card = q / 2 ∧
      (∀ t : Fin r → ZMod 2, t ∈ H →
        let L := quotientLine2 t u
        let S := quotientSet2 H t u
        S.card = q / 2 + 1 ∧
          (∀ v, translateFinset2 S v = S → v = 0) ∧
          S ∩ translateFinset2 S u = L) ∧
      (∀ x : Fin r → ZMod 2, ∃! t : Fin r → ZMod 2,
        t ∈ H ∧ x ∈ quotientLine2 t u)
end MathlibPlus.Open.ResearchFormalization.Batch
