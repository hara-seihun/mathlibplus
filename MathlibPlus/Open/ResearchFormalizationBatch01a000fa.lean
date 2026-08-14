import Mathlib

namespace MathlibPlus.Open.ResearchFormalizationBatch01a000fa

def legCount (m n : ℕ) (i : Fin 3) : ℕ :=
  match i.val with
  | 0 => 3
  | 1 => m
  | _ => n

def legBase (m _n : ℕ) (i : Fin 3) : ℕ :=
  match i.val with
  | 0 => 4
  | 1 => 10
  | _ => 10 + 2 * m

def childId (m n : ℕ) (i : Fin 3) (j : Fin (legCount m n i)) : ℕ :=
  legBase m n i + 2 * j.val

def leafId (m n : ℕ) (i : Fin 3) (j : Fin (legCount m n i)) : ℕ :=
  childId m n i j + 1

abbrev TVertex (m n : ℕ) := Fin (10 + 2 * m + 2 * n)
abbrev TStarVertex (m n : ℕ) := Fin (12 + 2 * m + 2 * n)

def tEdge (m n : ℕ) (u v : TVertex m n) : Prop :=
  (u.val = 0 ∧ ∃ i : Fin 3, v.val = 1 + i.val) ∨
    (∃ i : Fin 3, u.val = 1 + i.val ∧
      ∃ j : Fin (legCount m n i), v.val = childId m n i j) ∨
    (∃ i : Fin 3, ∃ j : Fin (legCount m n i),
      u.val = childId m n i j ∧ v.val = leafId m n i j)

def tAdj (m n : ℕ) (u v : TVertex m n) : Prop :=
  tEdge m n u v ∨ tEdge m n v u


def tsEdge (m n : ℕ) (u v : TStarVertex m n) : Prop :=
  (u.val = 0 ∧ ∃ i : Fin 3, v.val = 1 + i.val) ∨
    (u.val = 1 ∧ v.val = 4) ∨
    (∃ d : Fin 3, u.val = 4 + d.val ∧ v.val = 4 + d.val + 1) ∨
    (∃ j : Fin 2, u.val = 1 ∧ v.val = 8 + 2 * j.val) ∨
    (∃ j : Fin 2, u.val = 8 + 2 * j.val ∧ v.val = 9 + 2 * j.val) ∨
    (∃ j : Fin m, u.val = 2 ∧ v.val = 12 + 2 * j.val) ∨
    (∃ j : Fin m, u.val = 12 + 2 * j.val ∧ v.val = 13 + 2 * j.val) ∨
    (∃ j : Fin n, u.val = 3 ∧ v.val = 12 + 2 * m + 2 * j.val) ∨
    (∃ j : Fin n, u.val = 12 + 2 * m + 2 * j.val ∧ v.val = 13 + 2 * m + 2 * j.val)

def tsAdj (m n : ℕ) (u v : TStarVertex m n) : Prop :=
  tsEdge m n u v ∨ tsEdge m n v u


def Independent {V : Type} [DecidableEq V]
    (adj : V → V → Prop) (A : Finset V) : Prop :=
  ∀ ⦃u v : V⦄, u ∈ A → v ∈ A → u ≠ v → ¬ adj u v


noncomputable def independencePolynomial {V : Type} [Fintype V] [DecidableEq V]
    (adj : V → V → Prop) : Polynomial ℕ := by
  classical
  exact ∑ A : Finset V,
    if Independent adj A then Polynomial.monomial A.card 1 else 0

noncomputable def independenceNumber {V : Type} [Fintype V] [DecidableEq V]
    (adj : V → V → Prop) : ℕ := by
  classical
  exact Nat.findGreatest
    (fun k => ∃ A : Finset V, A.card = k ∧ Independent adj A)
    (Fintype.card V)



def IsNatUnimodal (p : Polynomial ℕ) : Prop :=
  ∃ k : ℕ,
    (∀ j : ℕ, j < k → p.coeff j ≤ p.coeff (j + 1)) ∧
      ∀ j : ℕ, k ≤ j → p.coeff (j + 1) ≤ p.coeff j

def IsLogConcavePrefix (p : Polynomial ℕ) (last : ℕ) : Prop :=
  ∀ j : ℕ, 0 < j → j + 1 ≤ last →
    p.coeff (j - 1) * p.coeff (j + 1) ≤ p.coeff j * p.coeff j

def coefficientList (p : Polynomial ℕ) (length : ℕ) : List ℕ :=
  List.ofFn (fun i : Fin length => p.coeff i.val)

def HasUniqueMode (p : Polynomial ℕ) (k : ℕ) : Prop :=
  ∀ j : ℕ, j ≠ k → p.coeff j < p.coeff k

def IsTreeRelation {V : Type} (adj : V → V → Prop) : Prop :=
  ∃ G : SimpleGraph V, (∀ u v, G.Adj u v ↔ adj u v) ∧ G.IsTree

def tailCeiling (a : ℕ) : ℕ :=
  (2 * a - 1 + 2) / 3

def claim48339 : Prop :=
  ∀ m n : ℕ, 1 ≤ m → 1 ≤ n →
    Fintype.card (TVertex m n) = 2 * m + 2 * n + 10 ∧
      independenceNumber (V := TVertex m n) (tAdj m n) = m + n + 6 ∧
      Fintype.card (TStarVertex m n) = 2 * m + 2 * n + 12 ∧
      independenceNumber (V := TStarVertex m n) (tsAdj m n) = m + n + 7

def claim48340 : Prop :=
  ∀ m n : ℕ, 1 ≤ m → 1 ≤ n →
    IsNatUnimodal (independencePolynomial (V := TVertex m n) (tAdj m n)) ∧
      IsNatUnimodal (independencePolynomial (V := TStarVertex m n) (tsAdj m n))

def claim48341 : Prop :=
  ∀ m n : ℕ, 1 ≤ m → 1 ≤ n →
    IsLogConcavePrefix
      (independencePolynomial (V := TVertex m n) (tAdj m n))
      (m + n + 5)

def claim48342 : Prop :=
  ∀ m n : ℕ, 1 ≤ m → 1 ≤ n →
    IsLogConcavePrefix
      (independencePolynomial (V := TStarVertex m n) (tsAdj m n))
      (m + n + 5)

def claim48344 : Prop :=
  (∀ {V : Type} [Fintype V] [DecidableEq V]
      (adj : V → V → Prop) (a : ℕ),
      1 ≤ a → IsTreeRelation adj →
      independenceNumber adj = a →
      ∀ j : ℕ, tailCeiling a ≤ j → j < a →
        (independencePolynomial adj).coeff (j + 1) ≤
          (independencePolynomial adj).coeff j) ∧
    (∀ m n : ℕ, 1 ≤ m → 1 ≤ n →
      (independencePolynomial (V := TVertex m n) (tAdj m n)).coeff (m + n + 6) ≤
        (independencePolynomial (V := TVertex m n) (tAdj m n)).coeff (m + n + 5) ∧
      (independencePolynomial (V := TStarVertex m n) (tsAdj m n)).coeff (m + n + 7) ≤
        (independencePolynomial (V := TStarVertex m n) (tsAdj m n)).coeff (m + n + 6) ∧
      (independencePolynomial (V := TStarVertex m n) (tsAdj m n)).coeff (m + n + 6) ≤
        (independencePolynomial (V := TStarVertex m n) (tsAdj m n)).coeff (m + n + 5) ∧
      IsNatUnimodal (independencePolynomial (V := TVertex m n) (tAdj m n)) ∧
      IsNatUnimodal (independencePolynomial (V := TStarVertex m n) (tsAdj m n)))

def claim48345 : Prop :=
  let p := independencePolynomial (V := TVertex 4 4) (tAdj 4 4)
  let q := independencePolynomial (V := TStarVertex 3 4) (tsAdj 3 4)
  coefficientList p 15 =
      [1, 26, 300, 2040, 9142, 28551, 63933, 103736,
        121376, 100144, 55499, 18683, 2979, 51, 1] ∧
    p.natDegree = 14 ∧
    coefficientList q 15 =
      [1, 26, 300, 2037, 9089, 28147, 62183, 98968,
        112870, 90178, 48086, 15498, 2372, 48, 1] ∧
    q.natDegree = 14 ∧
    HasUniqueMode p 8 ∧ HasUniqueMode q 8 ∧
    51 ^ 2 < 2979 ∧ 48 ^ 2 < 2372 ∧
    IsNatUnimodal p ∧ IsNatUnimodal q

noncomputable def BooleanPoint (Ω : Type) :=
  {h : Ω → ℝ // ∀ x, h x = -1 ∨ h x = 1}

def dotProduct {Ω : Type} [Fintype Ω] (a h : Ω → ℝ) : ℝ :=
  ∑ x, a x * h x

def l1Norm {Ω : Type} [Fintype Ω] (b : Ω → ℝ) : ℝ :=
  ∑ x, |b x|

def RecessionDirection {Ω : Type} [Fintype Ω]
    (γ : ℝ) (b : Ω → ℝ) : Prop :=
  (∑ x, b x = 0) ∧
    ∀ h : BooleanPoint Ω, γ + dotProduct b h.1 ≤ 0

def TargetRange {Ω : Type} (g : Ω → ℝ) : Prop :=
  ∀ x, -1 ≤ g x ∧ g x ≤ 1

def ObjectiveNeutral {Ω : Type} [Fintype Ω]
    (γ : ℝ) (b g : Ω → ℝ) : Prop :=
  γ + dotProduct b g = 0

def claim48357 : Prop :=
  ∀ {Ω : Type} [Fintype Ω] (γ : ℝ) (b : Ω → ℝ),
    RecessionDirection γ b ↔
      (∑ x, b x = 0) ∧ γ + l1Norm b ≤ 0

def claim48359 : Prop :=
  (∀ {Ω : Type} [Fintype Ω] (γ : ℝ) (b g : Ω → ℝ),
      RecessionDirection γ b → TargetRange g →
      (ObjectiveNeutral γ b g ↔
        γ = -l1Norm b ∧ ∀ x, b x * g x = |b x|)) ∧
    (∀ {Ω : Type} [Fintype Ω] (γ : ℝ) (b g : Ω → ℝ),
      RecessionDirection γ b → TargetRange g → ObjectiveNeutral γ b g →
      b ≠ 0 →
      (∃ x, g x = 1) ∧ ∃ y, g y = -1) ∧
    (∀ {Ω : Type} [Fintype Ω] [DecidableEq Ω]
        (g : Ω → ℝ) (x y : Ω) (t : ℝ),
      x ≠ y → g x = 1 → g y = -1 → 0 < t →
      let b := fun z => if z = x then t else if z = y then -t else 0
      RecessionDirection (-2 * t) b ∧
        ObjectiveNeutral (-2 * t) b g)

noncomputable def h (a q s : ℝ) : ℝ :=
  Real.rpow s (-a) * Real.exp (-q / s) +
    Real.rpow s a * Real.exp (-q * s)

noncomputable def L (s : ℝ) (f : ℝ → ℝ) (q : ℝ) : ℝ :=
  deriv (fun z => deriv f z + s * f z) q +
    s⁻¹ * (deriv f q + s * f q)

noncomputable def rho (a q s : ℝ) : ℝ :=
  Real.rpow s (2 * a) * Real.exp (-q * (s - s⁻¹))

def claim48421 : Prop :=
  ∀ a q s : ℝ, 1 < s →
    L s (fun z => h a z s) q = 0 ∧
      ∀ z : ℝ, 1 < z → z < s →
        -L s (fun q' => h a q' z) q =
          ((s - z) * (s * z - 1) / (s * z)) * h (a + 1) q z

def claim48422 : Prop :=
  (∀ q s : ℝ, Real.pi ≤ q → 1 < s →
      s + s⁻¹ + 2 * deriv (fun q' => Real.log (h (5 / 4) q' s)) q =
        (s - s⁻¹) * (1 - rho (5 / 4) q s) / (1 + rho (5 / 4) q s)) ∧
    (∀ q s : ℝ, Real.pi ≤ q → 1 < s →
      2 * Real.log s < s - s⁻¹ ∧
        (5 / 4 : ℝ) < Real.pi ∧
        rho (5 / 4) q s < 1 ∧
        0 < (s - s⁻¹) * (1 - rho (5 / 4) q s) /
          (1 + rho (5 / 4) q s)) ∧
    (∀ (F R : ℝ → ℝ) (q s : ℝ), 1 < s → ContDiff ℝ 2 R →
      (∀ z : ℝ, R z = F z / h (5 / 4) z s) →
      L s (fun z => h (5 / 4) z s * R z) q =
        h (5 / 4) q s *
          (deriv (fun z => deriv R z) q +
            (s + s⁻¹ + 2 * deriv (fun z => Real.log (h (5 / 4) z s)) q) *
              deriv R q))

def claim48423 : Prop :=
  ∀ (c : ℝ) (f : ℝ → ℝ) (x : ℝ), ContDiff ℝ 1 f → 0 < x →
    deriv f (Real.pi * x ^ 2) + c * f (Real.pi * x ^ 2) =
      Real.exp (-Real.pi * c * x ^ 2) / (2 * Real.pi * x) *
        deriv (fun y => Real.exp (Real.pi * c * y ^ 2) *
          f (Real.pi * y ^ 2)) x

end MathlibPlus.Open.ResearchFormalizationBatch01a000fa
