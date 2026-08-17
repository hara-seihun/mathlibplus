import Mathlib

namespace MathlibPlus.Open.Research.FormalizationR0314.InteractionInvertibility19700

noncomputable section

open Classical
open scoped BigOperators

private abbrev PottsPoly (m : ℕ) :=
  MvPolynomial (Fin m ⊕ (Fin m ⊕ Unit)) ℤ

private abbrev PottsRat (m : ℕ) :=
  FractionRing (PottsPoly m)

private def zVariable {m : ℕ} (i : Fin m) : PottsPoly m :=
  MvPolynomial.X (Sum.inr (Sum.inl i))

private def ySpecializedInteraction {m : ℕ}
    (y : PottsPoly m) (e : Sym2 (Fin (m + 1))) : PottsPoly m :=
  if e = Sym2.mk 0 0 then 1
  else if h : ∃ i : Fin m, e = Sym2.mk (Fin.succ i) (Fin.succ i) then
    zVariable (Classical.choose h)
  else y

private def qPolynomial {m : ℕ} (s t : Fin (m + 1)) : PottsPoly m :=
  ySpecializedInteraction
    (MvPolynomial.X (Sum.inr (Sum.inr Unit.unit))) (Sym2.mk s t)

private def qAtYZero {m : ℕ} (s t : Fin (m + 1)) : PottsPoly m :=
  ySpecializedInteraction 0 (Sym2.mk s t)

private def qPolynomialMatrix (m : ℕ) :
    Matrix (Fin (m + 1)) (Fin (m + 1)) (PottsPoly m) :=
  fun s t => qPolynomial s t

private def qAtYZeroMatrix (m : ℕ) :
    Matrix (Fin (m + 1)) (Fin (m + 1)) (PottsPoly m) :=
  fun s t => qAtYZero s t

private def qRationalMatrix (m : ℕ) :
    Matrix (Fin (m + 1)) (Fin (m + 1)) (PottsRat m) :=
  fun s t => algebraMap (PottsPoly m) (PottsRat m) (qPolynomial s t)

private def rationalVectorProduct {m : ℕ}
    (Q : Matrix (Fin (m + 1)) (Fin (m + 1)) (PottsRat m))
    (M : Fin (m + 1) → PottsRat m) : Fin (m + 1) → PottsRat m :=
  fun s => ∑ t : Fin (m + 1), Q s t * M t

def genericInteractionMatrixInvertibility19700 : Prop :=
  ∀ (m : ℕ), 1 ≤ m →
    Matrix.det (qPolynomialMatrix m) ≠ 0 ∧
      Matrix.det (qAtYZeroMatrix m) =
        ∏ i : Fin m, zVariable i ∧
      ∃ R : Matrix (Fin (m + 1)) (Fin (m + 1)) (PottsRat m),
        R * qRationalMatrix m = 1 ∧
          qRationalMatrix m * R = 1 ∧
          ∀ (M Φ : Fin (m + 1) → PottsRat m),
            rationalVectorProduct (qRationalMatrix m) M = Φ →
              M = rationalVectorProduct R Φ

end

end MathlibPlus.Open.Research.FormalizationR0314.InteractionInvertibility19700
