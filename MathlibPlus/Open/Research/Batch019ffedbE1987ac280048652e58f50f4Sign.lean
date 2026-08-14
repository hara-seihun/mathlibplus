import Mathlib

namespace MathlibPlus.Open.Research.FormalizationSign

open scoped BigOperators

noncomputable section

def signCode (x : ℝ) : ℤ :=
  if x < 0 then -1 else if 0 < x then 1 else 0

def removeZeroSigns : List ℤ → List ℤ :=
  List.filter (fun s => s ≠ 0)

def signChangeCount : List ℤ → ℕ
  | [] => 0
  | [_] => 0
  | a :: b :: rest =>
      (if a * b < 0 then 1 else 0) + signChangeCount (b :: rest)

def supportSignChangeCount (p : Polynomial ℝ) (x : List ℝ) : ℕ :=
  signChangeCount
    (removeZeroSigns (x.map (fun a => signCode (p.eval a))))

def listOrthogonalPolynomial (n : ℕ) (x w : List ℝ) (p : Polynomial ℝ) : Prop :=
  x.length = w.length ∧
    ∀ q : Polynomial ℝ, q.degree < (n : WithBot ℕ) →
      (List.zipWith (fun a b => b * p.eval a * q.eval a) x w).sum = 0

def positiveDiscreteSupport (x w : List ℝ) : Prop :=
  x.Pairwise (fun a b => a < b) ∧ w.Forall (fun a => 0 < a)

def claim8945_signChangeLowerBoundForDiscreteOrthogonalPolynomials : Prop :=
  ∀ (n : ℕ) (x w : List ℝ) (p : Polynomial ℝ),
    n < x.length → positiveDiscreteSupport x w →
    p.Monic → p.natDegree = n →
    listOrthogonalPolynomial n x w p →
      n ≤ supportSignChangeCount p x

def claim8947_simpleRealZerosOfPositiveDiscreteOrthogonalPolynomial : Prop :=
  ∀ (n : ℕ) (x w : List ℝ) (p : Polynomial ℝ),
    n < x.length → positiveDiscreteSupport x w →
    p.Monic → p.natDegree = n →
    listOrthogonalPolynomial n x w p →
      ∃ y : Fin n → ℝ,
        p = ∏ j : Fin n, (Polynomial.X - Polynomial.C (y j)) ∧
        (∀ j, y j ∈ convexHull ℝ
          (Set.range (fun i : Fin x.length => x.get i))) ∧
        (∀ i j, i ≠ j → y i ≠ y j)

end
end MathlibPlus.Open.Research.FormalizationSign
