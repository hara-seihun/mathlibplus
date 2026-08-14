import Mathlib

namespace MathlibPlus.Open.ResearchFormalizationBatch_01a001a1_5e77_7d33_b91b_4aaf193b3ddf

/-!
The following coordinate definitions use `Fin p` for the coordinates indexed
by `1, ..., p`, so the coordinate with value `i` represents the displayed
coordinate `i + 1`.  The extra coordinates of `V` are `f_0` at `0` and
`f_*` at `p + 1`.
-/

abbrev U (p : ℕ) := Fin p → ZMod p
abbrev V (p : ℕ) := Fin (p + 2) → ZMod p
abbrev Ambient (p : ℕ) := U p × V p

def fZeroIndex (p : ℕ) : Fin (p + 2) := ⟨0, by omega⟩
def fOneIndex (p : ℕ) (hp : 5 ≤ p) : Fin (p + 2) := ⟨1, by omega⟩
def fTwoIndex (p : ℕ) (hp : 5 ≤ p) : Fin (p + 2) := ⟨2, by omega⟩
def fStarIndex (p : ℕ) : Fin (p + 2) := ⟨p + 1, by omega⟩
def uZeroIndex (p : ℕ) (hp : 5 ≤ p) : Fin p := ⟨0, by omega⟩
def uOneIndex (p : ℕ) (hp : 5 ≤ p) : Fin p := ⟨1, by omega⟩

def vIndex (p : ℕ) (i : Fin p) : Fin (p + 2) := ⟨i.1 + 1, by omega⟩

def uUnit (p : ℕ) (i : Fin p) : U p :=
  fun j => if j = i then 1 else 0

def vUnit (p : ℕ) (i : Fin p) : V p :=
  fun j => if j = vIndex p i then 1 else 0

def vZero (p : ℕ) : V p :=
  fun j => if j = fZeroIndex p then 1 else 0

def s (p : ℕ) : U p := ∑ i : Fin p, uUnit p i

def bigF (p : ℕ) : V p := vZero p + ∑ i : Fin p, vUnit p i

def dotProduct {n p : ℕ} (u v : Fin n → ZMod p) : ZMod p :=
  ∑ j : Fin n, u j * v j

/-- The three families of affine hyperplane rows in the displayed construction. -/
def A (p : ℕ) (i : Fin p) : Set (Ambient p) :=
  {z | z.1 = uUnit p i ∧
    dotProduct z.2 (vZero p + vUnit p i) = 0}

def B (p : ℕ) (i : Fin p) : Set (Ambient p) :=
  {z | z.1 = s p - uUnit p i ∧
    dotProduct z.2 (vUnit p i + bigF p) = 0}

def C (p : ℕ) (t : ZMod p) : Set (Ambient p) :=
  {z | z.1 = s p ∧ dotProduct z.2 (bigF p) = t}

def S (p : ℕ) (t : ZMod p) : Set (Ambient p) :=
  (⋃ i : Fin p, A p i ∪ B p i) ∪ C p t

def S0 (p : ℕ) : Set (Ambient p) := S p 0
def S1 (p : ℕ) : Set (Ambient p) := S p 1

/-- The rank assertion accompanying the `p`-parameterized row construction. -/
def claim58071 : Prop :=
  ∀ p : ℕ, ∀ h5 : 5 ≤ p, Odd p → ∀ hp : Nat.Prime p,
    letI : Fact (Nat.Prime p) := ⟨hp⟩
    Module.finrank (ZMod p) (Ambient p) = p + (p + 2) ∧
      p + (p + 2) = 2 * p + 2

/-- The first nonzero coordinate of `L(x)` is `2*x₂ + x₃ + ... + x_p`. -/
def lFirst (p : ℕ) (hp : 5 ≤ p) (x : U p) : ZMod p :=
  2 * x (uOneIndex p hp) +
    ∑ j : Fin p, if 2 ≤ j.1 then x j else 0

def L (p : ℕ) (hp : 5 ≤ p) (x : U p) : V p :=
  fun j =>
    if j = fZeroIndex p then 0
    else if j = fOneIndex p hp then lFirst p hp x
    else if j = fTwoIndex p hp then x (uZeroIndex p hp)
    else 0

def sigma (p : ℕ) (hp : 5 ≤ p) : Ambient p → Ambient p :=
  fun z => (z.1, z.2 + L p hp z.1)

def sigmaInv (p : ℕ) (hp : 5 ≤ p) : Ambient p → Ambient p :=
  fun z => (z.1, z.2 - L p hp z.1)

/-- The concrete shear is a linear bijection with the displayed inverse. -/
def claim58072 : Prop :=
  ∀ p : ℕ, ∀ h5 : 5 ≤ p, Odd p → ∀ hp : Nat.Prime p,
    letI : Fact (Nat.Prime p) := ⟨hp⟩
    let sigmaLocal := sigma p h5
    let sigmaInvLocal := sigmaInv p h5
    (∀ z z', sigmaLocal (z + z') = sigmaLocal z + sigmaLocal z') ∧
      (∀ (a : ZMod p) z, sigmaLocal (a • z) = a • sigmaLocal z) ∧
      (∀ z, sigmaInvLocal (sigmaLocal z) = z ∧ sigmaLocal (sigmaInvLocal z) = z) ∧
      (∀ z, (sigmaLocal z).2 (fStarIndex p) = z.2 (fStarIndex p))

def ell (p : ℕ) (hp : 5 ≤ p) (j : Fin (p + 2)) (x : U p) : ZMod p :=
  L p hp x j

def R (p : ℕ) (hp : 5 ≤ p) (x : U p) : ZMod p :=
  ∑ j : Fin (p + 2), if j.1 ≤ p then ell p hp j x else 0

def bPair (p : ℕ) (hp : 5 ≤ p) (i : Fin p) : ZMod p × ZMod p :=
  (ell p hp (vIndex p i) (s p - uUnit p i),
    R p hp (s p - uUnit p i))

/-- The coordinate and level computations for the two preserved row families. -/
def claim58073 : Prop :=
  ∀ p : ℕ, ∀ h5 : 5 ≤ p, Odd p → ∀ hp : Nat.Prime p,
    letI : Fact (Nat.Prime p) := ⟨hp⟩
    (∀ i : Fin p,
      ell p h5 (fZeroIndex p) (uUnit p i) +
          ell p h5 (vIndex p i) (uUnit p i) = 0) ∧
      (∀ i : Fin p,
        ell p h5 (vIndex p i) (s p - uUnit p i) +
            R p h5 (s p - uUnit p i) = 0) ∧
      (∀ i : Fin p,
        (i.1 = 0 → bPair p h5 i = ((0 : ZMod p), (0 : ZMod p))) ∧
          (i.1 = 1 → bPair p h5 i = ((1 : ZMod p), (-1 : ZMod p))) ∧
          (2 ≤ i.1 → bPair p h5 i = ((0 : ZMod p), (0 : ZMod p)))) ∧
      R p h5 (s p) = (1 : ZMod p)

/-- The pole-cancelled score and the exact half-line predicate used by Claim 1340. -/
noncomputable def primeCountingReal (x : ℝ) : ℝ :=
  (Nat.primeCounting ⌊x⌋₊ : ℝ)

noncomputable def primeCountingScore (x : ℝ) : ℝ :=
  Real.log x * (Real.log x - 1 - x / primeCountingReal x)

noncomputable def validFrom1340 (c : ℝ) (X : ℕ) : Prop :=
  ∀ x : ℝ, (X : ℝ) ≤ x →
    primeCountingReal x < x / (Real.log x - 1 - c / Real.log x)

noncomputable def leastIntegerStart1340 (c : ℝ) (N : ℕ) : Prop :=
  validFrom1340 c N ∧ ∀ n : ℕ, n < N → ¬ validFrom1340 c n

noncomputable def claim1340 : Prop :=
  let x0 : ℝ := 42575222481
  let aStar : ℝ := primeCountingScore x0
  let c : ℝ := 1.14900031
  validFrom1340 c 42575222481 ∧
    leastIntegerStart1340 c 42575222481 ∧
    c - aStar > (8.1478 : ℝ) / (10 : ℝ) ^ 10 ∧
    primeCountingScore (x0 - 1) - c > (1.2076 : ℝ) / (10 : ℝ) ^ 8

end MathlibPlus.Open.ResearchFormalizationBatch_01a001a1_5e77_7d33_b91b_4aaf193b3ddf
