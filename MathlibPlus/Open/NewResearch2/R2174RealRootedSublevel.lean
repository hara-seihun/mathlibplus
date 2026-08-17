import Mathlib

namespace MathlibPlus.Open.NewResearch2.R2174

noncomputable section

open scoped BigOperators

/-- The monic product attached to an ordered list of real roots. -/
def rootProduct {n : ℕ} (t : Fin n → ℝ) : Polynomial ℝ :=
  ∏ i : Fin n, (Polynomial.X - Polynomial.C (t i))

def rootedPolynomialSetup {n : ℕ} (u v : ℝ) (P : Polynomial ℝ)
    (t : Fin n → ℝ) : Prop :=
  2 ≤ n ∧
    u ≤ v ∧
    P.Monic ∧
    P = rootProduct t ∧
    (∀ i : Fin n, u ≤ t i ∧ t i ≤ v) ∧
    (∀ i j : Fin n, i.val < j.val → t i < t j)

def firstIndex {n : ℕ} (h2 : 2 ≤ n) : Fin n :=
  ⟨0, Nat.zero_lt_of_lt h2⟩

def lastIndex {n : ℕ} (h2 : 2 ≤ n) : Fin n :=
  Fin.cast
    (Nat.sub_add_cancel (Nat.le_trans (Nat.succ_le_succ (Nat.zero_le 1)) h2))
    (Fin.last (n - 1))

def gapLeft {n : ℕ} (h2 : 2 ≤ n) (k : Fin (n - 1)) : Fin n :=
  Fin.cast
    (Nat.sub_add_cancel (Nat.le_trans (Nat.succ_le_succ (Nat.zero_le 1)) h2))
    k.castSucc

def gapRight {n : ℕ} (h2 : 2 ≤ n) (k : Fin (n - 1)) : Fin n :=
  Fin.cast
    (Nat.sub_add_cancel (Nat.le_trans (Nat.succ_le_succ (Nat.zero_le 1)) h2))
    k.succ

def rootWeight {n : ℕ} (P : Polynomial ℝ) (t : Fin n → ℝ) : ℝ :=
  ∑ i : Fin n, (|(Polynomial.derivative P).eval (t i)|)⁻¹

def gapR {n : ℕ} (h2 : 2 ≤ n) (t : Fin n → ℝ)
    (k : Fin (n - 1)) (x : ℝ) : ℝ :=
  ∏ j ∈ ((Finset.univ : Finset (Fin n)).erase (gapLeft h2 k)).erase
      (gapRight h2 k), |x - t j|

def gapP {n : ℕ} (h2 : 2 ≤ n) (P : Polynomial ℝ) (t : Fin n → ℝ)
    (k : Fin (n - 1)) : ℝ :=
  min |(Polynomial.derivative P).eval (t (gapLeft h2 k))|
    |(Polynomial.derivative P).eval (t (gapRight h2 k))|

def gapSublevelSet {n : ℕ} (h2 : 2 ≤ n) (P : Polynomial ℝ)
    (t : Fin n → ℝ) (k : Fin (n - 1)) (ε : ℝ) : Set ℝ :=
  Set.Ioo (t (gapLeft h2 k)) (t (gapRight h2 k)) ∩
    {x | |P.eval x| ≤ ε}

def leftExteriorSublevel {n : ℕ} (u : ℝ) (P : Polynomial ℝ)
    (t : Fin n → ℝ) (i : Fin n) (ε : ℝ) : Set ℝ :=
  Set.Icc u (t i) ∩ {x | |P.eval x| ≤ ε}

def rightExteriorSublevel {n : ℕ} (v : ℝ) (P : Polynomial ℝ)
    (t : Fin n → ℝ) (i : Fin n) (ε : ℝ) : Set ℝ :=
  Set.Icc (t i) v ∩ {x | |P.eval x| ≤ ε}

def intervalSublevel (u v : ℝ) (P : Polynomial ℝ)
    (ε : ℝ) : Set ℝ :=
  Set.Icc u v ∩ {x | |P.eval x| ≤ ε}

/-- Claim 40816: the concavity lower bound on one root gap, with the
un-normalized product `R_k` and the gap denominator appearing only in the
`p_k` lower bound. -/
def claim40816_gapLowerBound : Prop :=
  ∀ (n : ℕ) (u v : ℝ) (P : Polynomial ℝ) (t : Fin n → ℝ),
    ∀ hsetup : rootedPolynomialSetup u v P t,
      ∀ ε : ℝ, 0 < ε →
        ∀ k : Fin (n - 1),
          (∀ x : ℝ, x ∈ Set.Ioo (t (gapLeft hsetup.1 k))
                (t (gapRight hsetup.1 k)) →
            gapR hsetup.1 t k x ≥
                min (gapR hsetup.1 t k (t (gapLeft hsetup.1 k)))
                  (gapR hsetup.1 t k (t (gapRight hsetup.1 k))) ∧
              |P.eval x| ≥
                ((x - t (gapLeft hsetup.1 k)) *
                    (t (gapRight hsetup.1 k) - x) /
                  (t (gapRight hsetup.1 k) - t (gapLeft hsetup.1 k))) *
                    gapP hsetup.1 P t k ∧
              |P.eval x| ≥
                (1 / 2 : ℝ) * gapP hsetup.1 P t k *
                  min (x - t (gapLeft hsetup.1 k))
                    (t (gapRight hsetup.1 k) - x)) ∧
            MeasureTheory.volume (gapSublevelSet hsetup.1 P t k ε) ≤
              ENNReal.ofReal (4 * ε / gapP hsetup.1 P t k)

def claim40817_exteriorIntervalEstimate : Prop :=
  ∀ (n : ℕ) (u v : ℝ) (P : Polynomial ℝ) (t : Fin n → ℝ),
    ∀ hsetup : rootedPolynomialSetup u v P t,
      ∀ ε : ℝ, 0 < ε →
        let first := firstIndex hsetup.1
        let last := lastIndex hsetup.1
        (∀ x : ℝ, x ∈ Set.Icc u (t first) →
            |P.eval x| ≥ |(Polynomial.derivative P).eval (t first)| *
              (t first - x)) ∧
          (∀ x : ℝ, x ∈ Set.Icc (t last) v →
            |P.eval x| ≥ |(Polynomial.derivative P).eval (t last)| *
              (x - t last)) ∧
          MeasureTheory.volume (leftExteriorSublevel u P t first ε) ≤
            ENNReal.ofReal
              (ε / |(Polynomial.derivative P).eval (t first)|) ∧
          MeasureTheory.volume (rightExteriorSublevel v P t last ε) ≤
            ENNReal.ofReal
              (ε / |(Polynomial.derivative P).eval (t last)|) ∧
          (∑ k : Fin (n - 1),
              MeasureTheory.volume (gapSublevelSet hsetup.1 P t k ε)) ≤
            ENNReal.ofReal (8 * ε * rootWeight P t) ∧
          (MeasureTheory.volume (leftExteriorSublevel u P t first ε) +
              MeasureTheory.volume (rightExteriorSublevel v P t last ε)) ≤
            ENNReal.ofReal (ε * rootWeight P t) ∧
          MeasureTheory.volume (intervalSublevel u v P ε) ≤
            ENNReal.ofReal (9 * ε * rootWeight P t)

end

end MathlibPlus.Open.NewResearch2.R2174
