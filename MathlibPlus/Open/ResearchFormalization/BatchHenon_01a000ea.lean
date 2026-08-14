import Mathlib

namespace MathlibPlus.Open.ResearchFormalization.BatchHenon

open scoped BigOperators

/-- The explicit coordinate realization of the coupled Hénon carrier. -/
abbrev HenonV (p r : ℕ) :=
  (Fin 3 → ZMod p) × (Fin 3 → ZMod p) × (Fin (r - 6) → ZMod p)

/-- The polynomial appearing in the coupled Hénon map. -/
def henonF {p : ℕ} (z : Fin 3 → ZMod p) : Fin 3 → ZMod p :=
  fun i => if i = 0 then z 0 ^ 2 + z 0 * z 1 * z 2
    else if i = 1 then z 1 ^ 2 else z 2 ^ 2

/-- The displayed coupled Hénon function. -/
def henonQFun {p r : ℕ} (v : HenonV p r) : HenonV p r :=
  (v.2.1, v.1 + henonF v.2.1, v.2.2)

def henonQInvFun {p r : ℕ} (v : HenonV p r) : HenonV p r :=
  (v.2.1 - henonF v.1, v.1, v.2.2)

/-- The displayed coupled Hénon permutation. -/
def henonQEquiv {p r : ℕ} : Equiv.Perm (HenonV p r) :=
  { toFun := henonQFun
    invFun := henonQInvFun
    left_inv := by
      rintro ⟨x, z, w⟩
      ext <;> simp [henonQFun, henonQInvFun]
    right_inv := by
      rintro ⟨x, z, w⟩
      ext <;> simp [henonQFun, henonQInvFun] }

/-- Translation by one carrier element, as a permutation. -/
def henonTranslation {p r : ℕ} (v : HenonV p r) : Equiv.Perm (HenonV p r) :=
  { toFun := fun u => u + v
    invFun := fun u => u - v
    left_inv := by intro u; ext <;> simp [sub_eq_add_neg, add_assoc]
    right_inv := by intro u; ext <;> simp [sub_eq_add_neg, add_assoc] }

def henonR (p r : ℕ) : Subgroup (Equiv.Perm (HenonV p r)) :=
  Subgroup.closure (Set.range (henonTranslation (p := p) (r := r)))

def henonTGenerator {p r : ℕ} (v : HenonV p r) : Equiv.Perm (HenonV p r) :=
  (henonQEquiv (p := p) (r := r)).symm * henonTranslation v * henonQEquiv

def henonT (p r : ℕ) : Subgroup (Equiv.Perm (HenonV p r)) :=
  Subgroup.closure (Set.range (henonTGenerator (p := p) (r := r)))

def henonJR {p r : ℕ} : Equiv.Perm (HenonV p r) :=
  { toFun := Neg.neg
    invFun := Neg.neg
    left_inv := by intro u; ext <;> simp
    right_inv := by intro u; ext <;> simp }

def henonJT {p r : ℕ} : Equiv.Perm (HenonV p r) :=
  (henonQEquiv (p := p) (r := r)).symm * henonJR * henonQEquiv

def henonY (p r : ℕ) : Subgroup (Equiv.Perm (HenonV p r)) :=
  Subgroup.closure
    (Set.range (henonTranslation (p := p) (r := r)) ∪
      Set.range (henonTGenerator (p := p) (r := r)) ∪
      {henonJR, henonJT})

/-- The binary two-closure of a permutation subgroup. -/
def binaryTwoClosure {α : Type} (K : Subgroup (Equiv.Perm α)) : Set (Equiv.Perm α) :=
  {q | ∀ u v, ∃ g : K, g.1 u = q u ∧ g.1 v = q v}

/-- Conjugacy of two ambient subgroups by an element of a specified subgroup. -/
def conjugateWithin {α : Type} (Y R T : Subgroup (Equiv.Perm α)) : Prop :=
  ∃ g : Y, ∀ h : Equiv.Perm α,
    h ∈ R ↔ g.1 * h * (g.1)⁻¹ ∈ T

def regularOn {α : Type} (K : Subgroup (Equiv.Perm α)) : Prop :=
  ∀ u v : α, ∃! g : K, g.1 u = v

/-- Claim 6021: the coupled Hénon permutation and its explicit polynomial. -/
def coupledHenonPermutation (p r : ℕ) (hp : Nat.Prime p) (hp5 : 5 ≤ p)
    (hr : 6 ≤ r) : Prop :=
  let V := HenonV p r
  let F : (Fin 3 → ZMod p) → (Fin 3 → ZMod p) := henonF
  let q : V → V := henonQFun
  (∀ z i, F z i = if i = 0 then z 0 ^ 2 + z 0 * z 1 * z 2
      else if i = 1 then z 1 ^ 2 else z 2 ^ 2) ∧
    (∀ x z w, q (x, z, w) = (z, x + F z, w)) ∧
    Function.Bijective q

/-- Claim 6023: the inversion-stable generated pair, with all conjugations explicit. -/
def inversionStableGeneratedPair (p r : ℕ) (hp : Nat.Prime p) (hp5 : 5 ≤ p)
    (hr : 6 ≤ r) : Prop :=
  let R := henonR p r
  let T := henonT p r
  let jR := henonJR (p := p) (r := r)
  let jT := henonJT (p := p) (r := r)
  let Y := henonY p r
  regularOn R ∧ regularOn T ∧
    T = Subgroup.closure (Set.range (henonTGenerator (p := p) (r := r))) ∧
    jT = (henonQEquiv (p := p) (r := r)).symm * jR * henonQEquiv ∧
    Y = Subgroup.closure
      (Set.range (henonTranslation (p := p) (r := r)) ∪
        Set.range (henonTGenerator (p := p) (r := r)) ∪ {jR, jT})

/-- A coordinate map has total polynomial degree at most two. -/
def quadraticCoordinateMap {p : ℕ}
    (P : (Fin 3 → ZMod p) → (Fin 3 → ZMod p)) : Prop :=
  ∃ polys : Fin 3 → MvPolynomial (Fin 3) (ZMod p),
    (∀ i, (polys i).totalDegree ≤ 2) ∧
      ∀ z i, P z i = MvPolynomial.eval z (polys i)

/-- Claim 6024: the asserted quadratic normal form for every generated element. -/
def quadraticNormalFormEveryGeneratedElement
    (p r : ℕ) (hp : Nat.Prime p) (hp5 : 5 ≤ p) (hr : 6 ≤ r) : Prop :=
  ∀ g : henonY p r, ∃ ε : ZMod p, (ε = 1 ∨ ε = -1) ∧
    ∃ a : (Fin 3 → ZMod p), ∃ c : (Fin (r - 6) → ZMod p),
      ∃ P : (Fin 3 → ZMod p) → (Fin 3 → ZMod p),
        quadraticCoordinateMap P ∧
          ∀ v : HenonV p r,
            g.1 v = (ε • v.1 + P v.2.1, ε • v.2.1 + a, ε • v.2.2 + c)

def henonE₁ {p : ℕ} : Fin 3 → ZMod p :=
  fun i => if i = 0 then 1 else 0

def henonD (p r : ℕ) : HenonV p r :=
  (0, 2 • henonE₁, 0)

def henonFourE₁ {p : ℕ} : Fin 3 → ZMod p :=
  fun i => if i = 0 then 4 else 0

def henonPointStabilizerZOrbit (p r : ℕ) : Set (Fin 3 → ZMod p) :=
  {u | ∃ g : henonY p r, g.1 0 = 0 ∧ u = (g.1 (henonD p r)).2.1}

/-- Claim 6026: the explicit point-stabilizer escape and its pair obstruction. -/
def explicitEscapeFromGeneratedTwoClosure
    (p r : ℕ) (hp : Nat.Prime p) (hp5 : 5 ≤ p) (hr : 6 ≤ r) : Prop :=
  henonPointStabilizerZOrbit p r = {2 • henonE₁, -(2 • henonE₁)} ∧
    (henonQEquiv (p := p) (r := r) (henonD p r)).2.1 = 4 • henonE₁ ∧
    (∀ g : henonY p r,
      g.1 0 = henonQEquiv (p := p) (r := r) (0 : HenonV p r) →
        g.1 (henonD p r) ≠ henonQEquiv (p := p) (r := r) (henonD p r)) ∧
    henonQEquiv (p := p) (r := r) ∉ binaryTwoClosure (henonY p r)

/-- Claim 6027: the uniform pair-level obstruction. -/
def uniformCoupledHenonPairLevelObstruction : Prop :=
  ∀ (p r : ℕ) (_hp : Nat.Prime p) (_hp5 : 5 ≤ p) (_hr : 6 ≤ r),
    ¬ conjugateWithin (henonY p r) (henonR p r) (henonT p r) ∧
      henonQEquiv (p := p) (r := r) ∉ binaryTwoClosure (henonY p r)

end MathlibPlus.Open.ResearchFormalization.BatchHenon
