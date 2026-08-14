import Mathlib

open scoped BigOperators
open Finset

namespace MathlibPlus.Open.LinearAlgebra

abbrev GradedColumn (α : Type*) (d : ℕ) := α × (Fin d → ℕ)

structure GradedSparseSystem (K α Row : Type*) (d : ℕ)
    [Field K] [Fintype α] where
  grade : GradedColumn α d → ℕ
  columns : ℕ → Finset (GradedColumn α d)
  rows : ℕ → Finset Row
  coefficient : ℕ → Row → GradedColumn α d → K
  positive_length : ∀ (c : GradedColumn α d) (i : Fin d), 0 < c.2 i
  column_grade : ∀ E c, c ∈ columns E ↔ grade c = E

noncomputable def rowSupport {K α Row : Type*} {d : ℕ}
    [Field K] [Fintype α]
    (S : GradedSparseSystem K α Row d) (E : ℕ) (r : Row) :
    Finset (GradedColumn α d) := by
  classical
  exact (S.columns E).filter (fun c => S.coefficient E r c ≠ 0)

def truncatedColumnSignature {α : Type*} {d : ℕ}
    (s : ℕ) (c : GradedColumn α d) : α × (Fin d → ℕ) :=
  (c.1, fun i => min (c.2 i) s)

noncomputable def signatureSupportAt {K α Row : Type*} {d : ℕ}
    [Field K] [Fintype α]
    (S : GradedSparseSystem K α Row d) (s E : ℕ) (r : Row) :
    Finset (α × (Fin d → ℕ)) := by
  classical
  exact (rowSupport S E r).image (truncatedColumnSignature s)

def replaceColumnLength {α : Type*} {d : ℕ}
    (c : GradedColumn α d) (i : Fin d) (length : ℕ) : GradedColumn α d :=
  (c.1, Function.update c.2 i length)

def supportSaturatedAt {K α Row : Type*} {d : ℕ}
    [Field K] [Fintype α]
    (S : GradedSparseSystem K α Row d) (s : ℕ) : Prop :=
  ∀ (E : ℕ) (r : Row) (c : GradedColumn α d) (i : Fin d),
    c ∈ S.columns E → s ≤ c.2 i →
      signatureSupportAt S s E r =
        signatureSupportAt S s (S.grade (replaceColumnLength c i s)) r

def representativeColumn {α : Type*} {d : ℕ}
    (s : ℕ) (c : GradedColumn α d) : Prop :=
  (∀ i : Fin d, 1 ≤ c.2 i ∧ c.2 i ≤ s) ∧
    ∃ i : Fin d, c.2 i = s

def exceptionalGrade {K α Row : Type*} {d : ℕ}
    [Field K] [Fintype α]
    (S : GradedSparseSystem K α Row d) (s E : ℕ) : Prop :=
  ∀ c ∈ S.columns E, ∀ i : Fin d, c.2 i < s

def fullColumnRank {K α Row : Type*} {d : ℕ}
    [Field K] [Fintype α]
    (S : GradedSparseSystem K α Row d) (E : ℕ) : Prop :=
  ∀ f : GradedColumn α d → K,
    (∀ r ∈ S.rows E,
      ∑ c ∈ S.columns E, S.coefficient E r c * f c = 0) →
    ∀ c ∈ S.columns E, f c = 0

/-- D-0106.7: once local row support is saturated at radius `s`, all grades
reduce to the finite exceptional grades and the representative box whose
positive length vector has at least one coordinate equal to `s`. -/
def supportSaturationFiniteCheck : Prop :=
  ∀ (K α Row : Type*) (d : ℕ)
    [Field K] [Fintype α]
    (S : GradedSparseSystem K α Row d) (s : ℕ),
    supportSaturatedAt S s →
    ((∀ E : ℕ, exceptionalGrade S s E → fullColumnRank S E) ∧
      (∀ c : GradedColumn α d, representativeColumn s c →
        fullColumnRank S (S.grade c))) →
    ∀ E : ℕ, fullColumnRank S E

end MathlibPlus.Open.LinearAlgebra
