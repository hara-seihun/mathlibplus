import Mathlib
import MathlibPlus.Combinatorics.StrongOrdering

open scoped BigOperators
open Classical

namespace MathlibPlus.Open.ResearchFormalization.BatchR3844R3706R3943

noncomputable section

/-- The real-rooted base factor in Claim 48220, interpreted over `ℂ` so that
"only negative real roots" quantifies over all complex roots. -/
def basePolynomial48220 (r : ℕ) : Polynomial ℂ :=
  (1 + Polynomial.X) ^ r * (1 + 3 * Polynomial.X + Polynomial.X ^ 2) ^ 4

def correctionPolynomial48220 : Polynomial ℚ :=
  Polynomial.X * (1 + 2 * Polynomial.X) ^ 4

/-- Claim 48220: the base has only negative real roots, and the correction is
exactly supported in ranks one through five with the displayed coefficients. -/
def claim48220_realRootedBaseFiniteRankCorrection : Prop :=
  (∀ r : ℕ, ∀ z : ℂ,
    (basePolynomial48220 r).eval z = 0 → z.im = 0 ∧ z.re < 0) ∧
    correctionPolynomial48220 =
      Polynomial.X + 8 * Polynomial.X ^ 2 + 24 * Polynomial.X ^ 3 +
        32 * Polynomial.X ^ 4 + 16 * Polynomial.X ^ 5 ∧
      (∀ k : ℕ, k = 0 ∨ 6 ≤ k →
        (correctionPolynomial48220.coeff k = 0))

namespace PrefixOrdering

private def simpleZeroSumCycle48372 {G : Type*} [AddMonoid G]
    (C : List G) : Prop :=
  C.sum = 0 ∧
    ∀ i j : ℕ,
      i < C.length → j < C.length → i ≠ j →
        (C.take i).sum ≠ (C.take j).sum

private def prefixVertices48372 {G : Type*} [AddMonoid G]
    (C : List G) : List G :=
  (List.range C.length).map (fun i => (C.take i).sum)

private def originalPrefixVertices48372 {G : Type*} [AddMonoid G]
    (B : List G) (a : ℕ) : List G :=
  (List.range (a + 1)).map (fun i => (B.take i).sum)

private def relativePrefixVertices48372 {G : Type*} [AddGroup G]
    (B : List G) (a : ℕ) : List G :=
  (List.range (B.length - a + 1)).map (fun k =>
    (B.take (a + k)).sum - (B.take a).sum)

/-- Claim 48372: at a valid cut the two explicitly appended sequences are
simple zero-sum cycles; their proper-prefix vertices are the original and
relative prefix lists, the latter are distinct with only its initial zero,
and their labels form the augmented multiset partition. -/
def claim48372_cutPrefixSimpleZeroSumCycles : Prop :=
  ∀ (G : Type*) [AddCommGroup G]
    (B : List G) (u v : G) (a : ℕ),
    B.Nodup →
    MathlibPlus.Combinatorics.strongOrdering B →
    MathlibPlus.Combinatorics.validOrdering B →
    a ≤ B.length →
    u ∉ B → v ∉ B → u ≠ v →
    u + v = -B.sum →
    (B.take a).sum = -u →
    let Cminus : List G := B.take a ++ [u]
    let Cplus : List G := B.drop a ++ [v]
    let rel : List G := relativePrefixVertices48372 B a
    simpleZeroSumCycle48372 Cminus ∧
      simpleZeroSumCycle48372 Cplus ∧
        prefixVertices48372 Cminus = originalPrefixVertices48372 B a ∧
          prefixVertices48372 Cplus = rel ∧
            rel.Pairwise (· ≠ ·) ∧
              (∀ x, x ∈ rel.tail → x ≠ 0) ∧
                List.Perm (Cminus ++ Cplus) (B ++ [u, v]) ∧
                  (∀ x, x ∈ Cminus → x ∉ Cplus)

end PrefixOrdering

namespace WeightedSplice

abbrev Cube (n : ℕ) := Fin n → Bool
abbrev Table (n : ℕ) := Cube n → ℝ

private def insertBit {n : ℕ} (i : Fin (n + 1)) (b : Bool)
    (x : Cube n) : Cube (n + 1) :=
  Fin.insertNth i b x

private def restrictTable {n : ℕ} (f : Table (n + 1))
    (i : Fin (n + 1)) (b : Bool) : Table n :=
  fun x => f (insertBit i b x)

private def removeCosts {n : ℕ} (c : Fin (n + 1) → ℕ)
    (i : Fin (n + 1)) : Fin n → ℕ :=
  fun j => c (i.succAbove j)

private def constantTable {n : ℕ} (f : Table n) : Prop :=
  ∀ x y : Cube n, f x = f y

private def tableMean {n : ℕ} (f : Table n) : ℝ :=
  (∑ x : Cube n, f x) / (Fintype.card (Cube n) : ℝ)

private def tableVariance {n : ℕ} (f : Table n) : ℝ :=
  ∑ x : Cube n, (f x - tableMean f) ^ 2 /
    (Fintype.card (Cube n) : ℝ)

noncomputable def weightedArea : (n : ℕ) → Table n → (Fin n → ℕ) → ℝ
  | 0, f, c => 0
  | n + 1, f, c =>
      if constantTable f then 0 else
        sInf {a : ℝ |
          ∃ i : Fin (n + 1),
            a = (c i : ℝ) * tableVariance f +
              (weightedArea n (restrictTable f i false) (removeCosts c i) +
                weightedArea n (restrictTable f i true) (removeCosts c i)) / 2}

noncomputable def weightedQCost : (n : ℕ) → Table n → (Fin n → ℕ) → ℝ
  | 0, f, c => 0
  | n + 1, f, c =>
      if constantTable f then 0 else
        sInf {q : ℝ |
          ∃ i : Fin (n + 1),
            q = (c i : ℝ) +
              (weightedQCost n (restrictTable f i false) (removeCosts c i) +
                weightedQCost n (restrictTable f i true) (removeCosts c i)) / 2}

private def qOptimalRoot {n : ℕ} (f : Table (n + 1))
    (c : Fin (n + 1) → ℕ) (i : Fin (n + 1)) : Prop :=
  (c i : ℝ) +
      (weightedQCost n (restrictTable f i false) (removeCosts c i) +
        weightedQCost n (restrictTable f i true) (removeCosts c i)) / 2 =
    weightedQCost (n + 1) f c

noncomputable def constrainedArea : (n : ℕ) → Table n → Table n →
    (Fin n → ℕ) → ℝ
  | 0, driver, target, c => weightedArea 0 target c
  | n + 1, driver, target, c =>
      if constantTable driver then weightedArea (n + 1) target c else
        sInf {a : ℝ |
          ∃ i : Fin (n + 1), qOptimalRoot driver c i ∧
            a = (c i : ℝ) * tableVariance target +
              (constrainedArea n (restrictTable driver i false)
                (restrictTable target i false) (removeCosts c i) +
                constrainedArea n (restrictTable driver i true)
                (restrictTable target i true) (removeCosts c i)) / 2}

private def boolMask48367 (m : ℕ) : Table 3 :=
  fun x => if Nat.testBit m (∑ i : Fin 3, if x i then 2 ^ i.val else 0)
    then 1 else -1

private def masks48367 : Fin 6 → Table 3 :=
  ![boolMask48367 203, boolMask48367 253, boolMask48367 110,
    boolMask48367 31, boolMask48367 159, boolMask48367 51]

private def weights48367 : Fin 6 → ℝ :=
  ![13 / 86, 7 / 86, 29 / 172, 35 / 172, 8 / 43, 9 / 43]

private def costs48367 : Fin 3 → ℕ :=
  ![6, 14, 15]

private def barycentre48367 : Table 3 :=
  fun x => ∑ j : Fin 6, weights48367 j * masks48367 j x

private def rowIndex48367 (x : Cube 3) : Fin 8 :=
  Fin.ofNat 8 (∑ i : Fin 3, if x i then 2 ^ i.val else 0)

private def targetRows48367 : Fin 8 → ℝ :=
  ![57 / 86, 36 / 43, 12 / 43, 25 / 43, 31 / 86, -7 / 86,
    -17 / 86, -7 / 43]

private def driver48367 : Table 3 := boolMask48367 203

private def forcedQ48367 (i : Fin 3) : ℝ :=
  (costs48367 i : ℝ) +
    (weightedQCost 2 (restrictTable driver48367 i false) (removeCosts costs48367 i) +
      weightedQCost 2 (restrictTable driver48367 i true) (removeCosts costs48367 i)) / 2

private def forcedArea48367 (i : Fin 3) : ℝ :=
  (costs48367 i : ℝ) * tableVariance (barycentre48367) +
    (constrainedArea 2 (restrictTable driver48367 i false)
      (restrictTable barycentre48367 i false) (removeCosts costs48367 i) +
      constrainedArea 2 (restrictTable driver48367 i true)
      (restrictTable barycentre48367 i true) (removeCosts costs48367 i)) / 2

/-- Claim 48367: the exact weighted three-coordinate Bellman carrier, its
barycentre, unique q-optimal root, minimum constrained area, and wrong-root
splice values are all retained in one proposition. -/
def claim48367_weightedForcedRootSpliceObstruction : Prop :=
  (∀ x : Cube 3, barycentre48367 x = targetRows48367 (rowIndex48367 x)) ∧
    weightedQCost 3 driver48367 costs48367 = 113 / 4 ∧
      (∀ i : Fin 3,
        qOptimalRoot driver48367 costs48367 i ↔ i = 1) ∧
        constrainedArea 3 driver48367 barycentre48367 costs48367 =
          942465 / 236672 ∧
          forcedQ48367 2 = 57 / 2 ∧
            forcedArea48367 2 = 166399 / 59168 ∧
              constrainedArea 3 driver48367 barycentre48367 costs48367 -
                  forcedArea48367 2 = 276869 / 236672 ∧
                constrainedArea 3 driver48367 barycentre48367 costs48367 -
                    forcedArea48367 2 >
                  2 * (forcedQ48367 2 -
                    weightedQCost 3 driver48367 costs48367) ∧
                  (constrainedArea 3 driver48367 barycentre48367 costs48367 -
                    forcedArea48367 2) /
                      (forcedQ48367 2 -
                        weightedQCost 3 driver48367 costs48367) =
                    276869 / 59168 ∧
                    276869 / 59168 > (4 : ℝ)

structure FactorValue where
  area : ℝ
  score : ℝ
  cross : ℝ
  pair : ℝ

private def restrictLaw48369 {n : ℕ} (atoms : Fin 6 → Table (n + 1))
    (i : Fin (n + 1)) (b : Bool) : Fin 6 → Table n :=
  fun j => restrictTable (atoms j) i b

noncomputable def factorValue : (n : ℕ) → Table n → Table n →
    (Fin 6 → Table n) → (Fin n → ℕ) → FactorValue
  | 0, driver, target, atoms, c =>
      if constantTable driver ∧ tableVariance target = 0 then
        ⟨0, 0, 0, 0⟩
      else ⟨0, 0, 0, 0⟩
  | n + 1, driver, target, atoms, c =>
      let active := ¬ constantTable driver
      let admissible : Fin (n + 1) → Prop := fun i =>
        if active then qOptimalRoot driver c i else True
      let candidate : Fin (n + 1) → FactorValue := fun i =>
        let minus := factorValue n (restrictTable driver i false)
          (restrictTable target i false) (restrictLaw48369 atoms i false)
          (removeCosts c i)
        let plus := factorValue n (restrictTable driver i true)
          (restrictTable target i true) (restrictLaw48369 atoms i true)
          (removeCosts c i)
        let av := ∑ j : Fin 6, weights48367 j * tableVariance (atoms j)
        let tv := tableVariance target
        let pn := 2 * (c i : ℝ) * (av - tv)
        let cn := (c i : ℝ) * (av - if active then 1 else 0)
        { area := (c i : ℝ) * tv + (minus.area + plus.area) / 2
          score := cn - pn + (minus.score + plus.score) / 2
          cross := cn + (minus.cross + plus.cross) / 2
          pair := pn + (minus.pair + plus.pair) / 2 }
      let amin : ℝ := sInf {a : ℝ | ∃ i, admissible i ∧ a = (candidate i).area}
      let smax : ℝ := sSup {s : ℝ |
        ∃ i, admissible i ∧ (candidate i).area = amin ∧ s = (candidate i).score}
      let cmax : ℝ := sSup {z : ℝ |
        ∃ i, admissible i ∧ (candidate i).area = amin ∧
          (candidate i).score = smax ∧ z = (candidate i).cross}
      let pmin : ℝ := sInf {p : ℝ |
        ∃ i, admissible i ∧ (candidate i).area = amin ∧
          (candidate i).score = smax ∧ (candidate i).cross = cmax ∧
          p = (candidate i).pair}
      { area := amin, score := smax, cross := cmax, pair := pmin }

private def lawX48369 : ℝ :=
  ∑ j : Fin 6, weights48367 j *
    (factorValue 3 (masks48367 j) barycentre48367 masks48367 costs48367).cross

private def lawP48369 : ℝ :=
  ∑ j : Fin 6, weights48367 j *
    (factorValue 3 (masks48367 j) barycentre48367 masks48367 costs48367).pair

/-- Claim 48369: the same exact weighted-law factor recursion has safe sharp
and factor-two sidecars, while Claim 48367 supplies the local obstruction. -/
def claim48369_safeLawSidecars : Prop :=
  lawX48369 - lawP48369 / 2 = -367194781 / 20353792 ∧
    lawX48369 - lawP48369 = -392639171 / 10176896 ∧
      lawX48369 - lawP48369 / 2 < 0 ∧ lawX48369 - lawP48369 < 0

end WeightedSplice

end
end MathlibPlus.Open.ResearchFormalization.BatchR3844R3706R3943
