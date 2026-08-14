import Mathlib

namespace MathlibPlus.Open.ResearchFormalization.LineUnion

noncomputable def line (q k : ℕ) (x : Fin k → ZMod q)
    (A : Fin k → Finset (ZMod q)) (i : Fin k) :
    Finset (ZMod q × ZMod q) :=
  (A i).image (fun a => (a, -(x i) * a))

noncomputable def code (q k : ℕ) (x : Fin k → ZMod q)
    (A : Fin k → Finset (ZMod q)) : Finset (ZMod q × ZMod q) :=
  (Finset.univ : Finset (Fin k)).biUnion (line q k x A)

/-- The exact finite-field line-union construction and its stated count. -/
noncomputable def pairInjectiveFiniteFieldLineUnionCode
    (q k : ℕ) (hq : Nat.Prime q) (hk : 2 ≤ k) (hkq : k ≤ q)
    (x : Fin k → ZMod q) (A : Fin k → Finset (ZMod q)) : Prop :=
  (∀ i j : Fin k, i ≠ j → x i ≠ x j) ∧
  (∀ i : Fin k, 0 ∈ A i ∧ k - 1 ≤ (A i).card ∧ (A i).card ≤ q) ∧
  (∀ i j : Fin k, i ≠ j →
    line q k x A i ∩ line q k x A j = {(0, 0)}) ∧
  (code q k x A).card =
    1 + ∑ i : Fin k, ((A i).card - 1)

def coordinateProjection {q k : ℕ} (x : Fin k → ZMod q) (j : Fin k)
    (p : ZMod q × ZMod q) : ZMod q :=
  x j * p.1 + p.2

/-- Shannon entropy of the image of a uniformly distributed finite set. -/
noncomputable def uniformMapEntropy {α β : Type*}
    (A : Finset α) (f : α → β) : ℝ := by
  classical
  exact if h : A.Nonempty then
    -(Finset.sum (A.image f) (fun y =>
      (((A.filter (fun z => f z = y)).card : ℝ) / (A.card : ℝ)) *
        Real.log (((A.filter (fun z => f z = y)).card : ℝ) /
          (A.card : ℝ))))
    else 0

/-- Every two coordinate projections determine a point of the line-union code,
    with the corresponding finite-uniform entropy consequences. -/
noncomputable def everyPairCoordinatesInjective
    (q k : ℕ) (hq : Nat.Prime q) (hk : 2 ≤ k) (hkq : k ≤ q)
    (x : Fin k → ZMod q) (A : Fin k → Finset (ZMod q))
    (hcode : pairInjectiveFiniteFieldLineUnionCode q k hq hk hkq x A) : Prop :=
  ∀ j l : Fin k, j ≠ l →
    x j - x l ≠ 0 ∧
    Function.Bijective
      (fun p : ZMod q × ZMod q =>
        (coordinateProjection x j p, coordinateProjection x l p)) ∧
    let R := code q k x A
    uniformMapEntropy R (fun p => p) =
        uniformMapEntropy R
          (fun p => (coordinateProjection x j p, coordinateProjection x l p)) ∧
    uniformMapEntropy R (fun p => p) = Real.log (R.card) ∧
    uniformMapEntropy R
        (fun p => (coordinateProjection x j p, coordinateProjection x l p)) =
      Real.log (R.card) ∧
    uniformMapEntropy R (coordinateProjection x j) +
        uniformMapEntropy R (coordinateProjection x l) ≥ Real.log (R.card)

end MathlibPlus.Open.ResearchFormalization.LineUnion
