import Mathlib

open scoped BigOperators
open MeasureTheory

namespace MathlibPlus.Open.ResearchFormalization

def oddIndices (n : ℕ) : Finset (Fin n) :=
  Finset.univ.filter (fun i => Odd (i.1 + 1))

def evenIndices (n : ℕ) : Finset (Fin n) :=
  Finset.univ.filter (fun i => Even (i.1 + 1))

def strictlyTotallyPositive {n : ℕ} (B : Matrix (Fin n) (Fin n) ℝ) : Prop :=
  ∀ (k : ℕ) (r c : Fin k → Fin n),
    StrictMono r → StrictMono c →
      0 < Matrix.det (Matrix.submatrix B r c)

def claim2910 (n : ℕ) (B : Matrix (Fin n) (Fin n) ℝ)
    (H : Matrix (evenIndices n) (evenIndices n) ℝ) : Prop :=
  H =
    Matrix.submatrix B (fun i : evenIndices n => i.1) (fun j : evenIndices n => j.1) -
      Matrix.submatrix B (fun i : evenIndices n => i.1) (fun j : oddIndices n => j.1) *
        (1 + Matrix.submatrix B (fun i : oddIndices n => i.1) (fun j : oddIndices n => j.1))⁻¹ *
        Matrix.submatrix B (fun i : oddIndices n => i.1) (fun j : evenIndices n => j.1)

def claim2913 (n : ℕ) (B : Matrix (Fin n) (Fin n) ℝ)
    (H : Matrix (evenIndices n) (evenIndices n) ℝ) : Prop :=
  claim2910 n B H →
    IsUnit (1 + Matrix.submatrix B (fun i : oddIndices n => i.1)
      (fun j : oddIndices n => j.1)) →
      (∀ I : Finset (evenIndices n),
        Matrix.det (Matrix.submatrix H (fun i : I => i.1) (fun j : I => j.1)) =
          (∑ S : Finset (oddIndices n),
            let U :=
              S.map ⟨(fun i : oddIndices n => i.1),
                (fun a b h => Subtype.ext h)⟩ ∪
                I.map ⟨(fun i : evenIndices n => i.1),
                  (fun a b h => Subtype.ext h)⟩
            Matrix.det (Matrix.submatrix B (fun i : U => i.1) (fun j : U => j.1))) /
          Matrix.det (1 + Matrix.submatrix B (fun i : oddIndices n => i.1)
            (fun j : oddIndices n => j.1))) ∧
      (let I : Finset (evenIndices n) := ∅
       let numerator :=
         ∑ S : Finset (oddIndices n),
           let U :=
             S.map ⟨(fun i : oddIndices n => i.1),
               (fun a b h => Subtype.ext h)⟩ ∪
               I.map ⟨(fun i : evenIndices n => i.1),
                 (fun a b h => Subtype.ext h)⟩
           Matrix.det (Matrix.submatrix B (fun i : U => i.1) (fun j : U => j.1))
       let denominator :=
         Matrix.det (1 + Matrix.submatrix B (fun i : oddIndices n => i.1)
           (fun j : oddIndices n => j.1))
       Matrix.det (Matrix.submatrix H (fun i : I => i.1) (fun j : I => j.1)) = 1 ∧
         numerator / denominator = 1)

def claim2914 (n : ℕ) (B : Matrix (Fin n) (Fin n) ℝ) : Prop :=
  strictlyTotallyPositive B →
    (∀ S : Finset (Fin n),
      0 < Matrix.det (Matrix.submatrix B (fun i : S => i.1) (fun j : S => j.1))) ∧
    Matrix.det (1 + Matrix.submatrix B (fun i : oddIndices n => i.1)
      (fun j : oddIndices n => j.1)) =
      ∑ S : Finset (oddIndices n),
        Matrix.det (Matrix.submatrix B (fun i : S => i.1) (fun j : S => j.1)) ∧
    0 < Matrix.det (1 + Matrix.submatrix B (fun i : oddIndices n => i.1)
      (fun j : oddIndices n => j.1))

def claim2915 (n : ℕ) (B : Matrix (Fin n) (Fin n) ℝ)
    (H : Matrix (evenIndices n) (evenIndices n) ℝ) : Prop :=
  strictlyTotallyPositive B → claim2910 n B H →
    ∀ I : Finset (evenIndices n),
      0 < Matrix.det (Matrix.submatrix H (fun i : I => i.1) (fun j : I => j.1))

def claim2916 (n : ℕ) (B : Matrix (Fin n) (Fin n) ℝ)
    (H : Matrix (evenIndices n) (evenIndices n) ℝ) : Prop :=
  strictlyTotallyPositive B → claim2910 n B H →
    (let m := Fintype.card (evenIndices n)
     let a := fun k : ℕ =>
       ∑ I : Finset (evenIndices n),
         if I.card = k then
           Matrix.det (Matrix.submatrix H (fun i : I => i.1) (fun j : I => j.1))
         else 0
     a 0 = 1 ∧ ∀ k : ℕ, k ≤ m → 0 < a k)

def claim2917 (n : ℕ) (H : Matrix (evenIndices n) (evenIndices n) ℝ) : Prop :=
  ∀ z : ℝ,
    Matrix.det (1 - z • H) =
      ∑ k ∈ Finset.range (Fintype.card (evenIndices n) + 1),
        (-z) ^ k *
          (∑ I : Finset (evenIndices n),
            if I.card = k then
              Matrix.det (Matrix.submatrix H (fun i : I => i.1) (fun j : I => j.1))
            else 0)

def claim2918 (n : ℕ) (B : Matrix (Fin n) (Fin n) ℝ)
    (H : Matrix (evenIndices n) (evenIndices n) ℝ) : Prop :=
  strictlyTotallyPositive B → claim2910 n B H →
    (let denominator :=
       Matrix.det (1 + Matrix.submatrix B (fun i : oddIndices n => i.1)
         (fun j : oddIndices n => j.1))
     ∀ k : ℕ, k ≤ Fintype.card (evenIndices n) →
       (∑ I : Finset (evenIndices n),
          if I.card = k then
            Matrix.det (Matrix.submatrix H (fun i : I => i.1) (fun j : I => j.1))
          else 0) =
         (∑ I : Finset (evenIndices n),
           if I.card = k then
             ∑ S : Finset (oddIndices n),
               let U :=
                 S.map ⟨(fun i : oddIndices n => i.1),
                   (fun _ _ h => Subtype.ext h)⟩ ∪
                   I.map ⟨(fun i : evenIndices n => i.1),
                     (fun _ _ h => Subtype.ext h)⟩
               Matrix.det (Matrix.submatrix B (fun i : U => i.1) (fun j : U => j.1))
           else 0) / denominator)


end MathlibPlus.Open.ResearchFormalization
