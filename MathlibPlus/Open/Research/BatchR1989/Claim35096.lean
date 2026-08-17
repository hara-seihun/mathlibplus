import Mathlib

namespace MathlibPlus.Open.Research.BatchR1989Claim35096

noncomputable section
open scoped BigOperators

abbrev F2 := ZMod 2
abbrev Vector (n : ℕ) := Fin n → F2
abbrev W := Fin 3 → F2
abbrev Dual (n : ℕ) := Module.Dual F2 (Vector n)

-- The binary coordinate vector and coordinate functional used by the exact maps.
def basisVector {n : ℕ} (i : Fin n) : Vector n :=
  fun j => if j = i then 1 else 0

def coordinate {n : ℕ} (i : Fin n) : Vector n →ₗ[F2] F2 :=
  LinearMap.proj i

def threeLeFive : 3 ≤ 5 :=
  Nat.succ_le_succ (Nat.succ_le_succ (Nat.succ_le_succ (Nat.zero_le 2)))

def heavyIndex3 {n : ℕ} (h : 5 ≤ n) (i : Fin 3) : Fin n :=
  Fin.castLE h (Fin.castLE threeLeFive i)

def heavyIndex5 {n : ℕ} (h : 5 ≤ n) (i : Fin 5) : Fin n :=
  Fin.castLE h i

def heavyCoordinate3 {n : ℕ} (h : 5 ≤ n) : Vector n →ₗ[F2] F2 :=
  coordinate (heavyIndex5 h (3 : Fin 5))

def heavyCoordinate4 {n : ℕ} (h : 5 ≤ n) : Vector n →ₗ[F2] F2 :=
  coordinate (heavyIndex5 h (4 : Fin 5))

-- The first coordinate is x_j+x_k for the two indices different from i.
def heavyFirstMap {n : ℕ} (h : 5 ≤ n) (i : Fin 3) :
    Vector n →ₗ[F2] F2 :=
  ∑ j : Fin 3, if j = i then 0 else coordinate (heavyIndex3 h j)

def heavyMap {n : ℕ} (h : 5 ≤ n) (i : Fin 3) :
    Vector n →ₗ[F2] W :=
  LinearMap.pi (fun r =>
    Fin.cases (heavyFirstMap h i)
      (fun r' => Fin.cases (heavyCoordinate3 h)
        (fun _ => heavyCoordinate4 h) r') r)

def zCharacter {n : ℕ} (h : 5 ≤ n) : Dual n :=
  coordinate (heavyIndex3 h 0) + coordinate (heavyIndex3 h 1) +
    coordinate (heavyIndex3 h 2)

def pullbackU {n : ℕ} (h : 5 ≤ n) (i : Fin 3) : Submodule F2 (Dual n) :=
  LinearMap.range (heavyMap h i).dualMap

def pullbackA {n : ℕ} (h : 5 ≤ n) (i : Fin 3) : Submodule F2 (Dual n) :=
  pullbackU h i ⊔ Submodule.span F2 {coordinate (heavyIndex3 h i)}

def pullbackCenter {n : ℕ} (h : 5 ≤ n) : Submodule F2 (Dual n) :=
  Submodule.span F2 {zCharacter h, heavyCoordinate3 h, heavyCoordinate4 h}

abbrev PairFace {n : ℕ} (h : 5 ≤ n) (i j : Fin 3) :=
  {x : Vector n // x (heavyIndex3 h i) = 0 ∧ x (heavyIndex3 h j) = 0}

abbrev TripleFace {n : ℕ} (h : 5 ≤ n) (i j k : Fin 3) :=
  {x : Vector n // x (heavyIndex3 h i) = 0 ∧
    x (heavyIndex3 h j) = 0 ∧ x (heavyIndex3 h k) = 0}

def pairImage {n : ℕ} (h : 5 ≤ n) (i j : Fin 3) : Set (W × W) :=
  Set.range (fun x : PairFace h i j =>
    (heavyMap h i x.1, heavyMap h j x.1))

def tripleImage {n : ℕ} (h : 5 ≤ n) (i j k : Fin 3) :
    Set (W × W × W) :=
  Set.range (fun x : TripleFace h i j k =>
    (heavyMap h i x.1, heavyMap h j x.1, heavyMap h k x.1))

def pairProjection12 (T : Set (W × W × W)) : Set (W × W) :=
  {p | ∃ c : W, (p.1, p.2, c) ∈ T}

def pairSurjectiveTriple (T : Set (W × W × W)) (P : Set (W × W)) : Prop :=
  pairProjection12 T = P

def diagonalImage : Set (W × W) :=
  {p | p.1 = p.2}

def deficientSpace : Set W :=
  {w | w 0 = 0}

def deficientTripleImage : Set (W × W × W) :=
  {p | p.1 = p.2.1 ∧ p.2.1 = p.2.2 ∧ p.1 ∈ deficientSpace}

def distinctThree (i j k : Fin 3) : Prop :=
  i ≠ j ∧ i ≠ k ∧ j ≠ k

-- The displayed maps have the exact pairwise sunflower and deficient-triple data.
def exactSunflowerCounterexample {n : ℕ} (h : 5 ≤ n) : Prop :=
  (∀ i j : Fin 3, i ≠ j →
    pullbackA h i ⊓ pullbackA h j = pullbackCenter h) ∧
  (∀ i j : Fin 3, i ≠ j →
    pairImage h i j = diagonalImage) ∧
  (∀ i j k : Fin 3, distinctThree i j k →
    tripleImage h i j k = deficientTripleImage) ∧
  (∀ i j k : Fin 3, distinctThree i j k →
    ¬ pairSurjectiveTriple (tripleImage h i j k) (pairImage h i j))

-- Pairwise pullback-space sunflower data therefore does not force triple coherence.
def claim_35096 : Prop :=
  ∀ (n : ℕ) (h : 5 ≤ n), exactSunflowerCounterexample h

end
end MathlibPlus.Open.Research.BatchR1989Claim35096
