import Mathlib

namespace MathlibPlus.Open.ResearchBatch.Henon

open scoped Pointwise

/-- A regular translation subgroup of a finite additive permutation space. -/
def regularTranslationCopy {V : Type*} [Fintype V] [AddGroup V]
    (R : Subgroup (Equiv.Perm V)) : Prop :=
  (∀ x y : V, ∃! h : R, (h : Equiv.Perm V) x = y) ∧
    ∀ h : R, ∃ a : V, ∀ v, (h : Equiv.Perm V) v = v + a

/-- Conjugacy of permutation subgroups. -/
def subgroupConjugate {V : Type*}
    (q : Equiv.Perm V) (R T : Subgroup (Equiv.Perm V)) : Prop :=
  ∀ h : Equiv.Perm V, h ∈ T ↔ ∃ k, k ∈ R ∧ h = q⁻¹ * k * q

/-- The orbit of a point under the point stabilizer of a permutation subgroup. -/
def pointStabilizerOrbit {V : Type*} [Zero V]
    (Y : Subgroup (Equiv.Perm V)) (d : V) : Set V :=
  {e | ∃ y : Y, (y : Equiv.Perm V) 0 = 0 ∧ (y : Equiv.Perm V) d = e}

/-- The coupled Hénon polynomial from the admitted family. -/
def henonF (p : ℕ) (z : Fin 3 → ZMod p) : Fin 3 → ZMod p :=
  ![z 0 ^ 2 + z 0 * z 1 * z 2, z 1 ^ 2, z 2 ^ 2]

def henonSwap {W : Type*} {p : ℕ}
    (x z : Fin 3 → ZMod p) (w : W) :
    (Fin 3 → ZMod p) × (Fin 3 → ZMod p) × W := (z, x, w)

/-- The nine-dimensional voltage span used in the point-stabilizer formula. -/
def voltageMaps (p : ℕ) : Set ((Fin 3 → ZMod p) → (Fin 3 → ZMod p)) :=
  { (fun z => ![z 2, 0, 0]),
    (fun z => ![z 1, 0, 0]),
    (fun z => ![z 1 * z 2, 0, 0]),
    (fun z => ![z 0, 0, 0]),
    (fun z => ![z 0 * z 2, 0, 0]),
    (fun z => ![z 0 * z 1, 0, 0]),
    (fun z => ![z 0 ^ 2, z 1 ^ 2, z 2 ^ 2]),
    (fun z => ![0, z 1, 0]),
    (fun z => ![0, 0, z 2]) }

def voltageSpace (p : ℕ) (z : Fin 3 → ZMod p) : Set (Fin 3 → ZMod p) :=
  {u | ∃ P : (Fin 3 → ZMod p) → (Fin 3 → ZMod p),
    P ∈ Submodule.span (ZMod p) (voltageMaps p) ∧ P z = u}

/--
The coupled Hénon family has the fixed linear swap shadow for every member of
its complete point-stabilizer orbital-fusion family.
-/
def claim59052_coupledHenonLinearShadow : Prop :=
  ∀ (p : ℕ) [Fact (Nat.Prime p)] {W : Type*}
    [AddCommGroup W] [Module (ZMod p) W] [Fintype W]
    [FiniteDimensional (ZMod p) W]
    (R T : Subgroup (Equiv.Perm ((Fin 3 → ZMod p) × (Fin 3 → ZMod p) × W)))
    (q jR jT : Equiv.Perm ((Fin 3 → ZMod p) × (Fin 3 → ZMod p) × W)),
    5 ≤ p →
    regularTranslationCopy R →
    (∀ x z w, q (x, z, w) = (z, x + henonF p z, w)) →
    subgroupConjugate q R T →
    (∀ x z w, jR (x, z, w) = (-x, -z, -w)) →
    jT = q⁻¹ * jR * q →
    let Y := Subgroup.closure
      ((R : Set (Equiv.Perm ((Fin 3 → ZMod p) × (Fin 3 → ZMod p) × W))) ∪
        (T : Set _) ∪ {jR, jT})
    ∀ S : Set ((Fin 3 → ZMod p) × (Fin 3 → ZMod p) × W),
      0 ∉ S →
      (∀ d, d ∈ S → pointStabilizerOrbit Y d ⊆ S) →
      S = -S ∧
      q '' S = (fun (x, z, w) => (z, x, w)) '' S

/--
The exact point-stabilizer orbit formula for the same family, including the
nine displayed voltage generators, the evenness `W_{-z}=W_z`, and the
containment of the coupled polynomial.
-/
def claim59053_exactPointStabilizerOrbitFormula : Prop :=
  ∀ (p : ℕ) [Fact (Nat.Prime p)] {W : Type*}
    [AddCommGroup W] [Module (ZMod p) W] [Fintype W]
    [FiniteDimensional (ZMod p) W]
    (R T : Subgroup (Equiv.Perm ((Fin 3 → ZMod p) × (Fin 3 → ZMod p) × W)))
    (q jR jT : Equiv.Perm ((Fin 3 → ZMod p) × (Fin 3 → ZMod p) × W)),
    5 ≤ p →
    regularTranslationCopy R →
    (∀ x z w, q (x, z, w) = (z, x + henonF p z, w)) →
    subgroupConjugate q R T →
    (∀ x z w, jR (x, z, w) = (-x, -z, -w)) →
    jT = q⁻¹ * jR * q →
    let Y := Subgroup.closure
      ((R : Set (Equiv.Perm ((Fin 3 → ZMod p) × (Fin 3 → ZMod p) × W))) ∪
        (T : Set _) ∪ {jR, jT})
    ∀ x₀ z₀ w₀,
      pointStabilizerOrbit Y (x₀, z₀, w₀) =
        {d | ∃ ε : ZMod p, (ε = 1 ∨ ε = -1) ∧
          ∃ u ∈ voltageSpace p z₀,
            d = (ε • x₀ + u, ε • z₀, ε • w₀)} ∧
      voltageSpace p (-z₀) = voltageSpace p z₀ ∧
      henonF p z₀ ∈ voltageSpace p z₀

/--
The orbit formula gives the global swap shadow for every union of the stated
orbital blocks.
-/
def claim59054_globalSwapShadow : Prop :=
  ∀ (p : ℕ) [Fact (Nat.Prime p)] {W : Type*}
    [AddCommGroup W] [Module (ZMod p) W] [Fintype W]
    [FiniteDimensional (ZMod p) W]
    (R T : Subgroup (Equiv.Perm ((Fin 3 → ZMod p) × (Fin 3 → ZMod p) × W)))
    (q jR jT : Equiv.Perm ((Fin 3 → ZMod p) × (Fin 3 → ZMod p) × W)),
    5 ≤ p →
    regularTranslationCopy R →
    (∀ x z w, q (x, z, w) = (z, x + henonF p z, w)) →
    subgroupConjugate q R T →
    (∀ x z w, jR (x, z, w) = (-x, -z, -w)) →
    jT = q⁻¹ * jR * q →
    let Y := Subgroup.closure
      ((R : Set (Equiv.Perm ((Fin 3 → ZMod p) × (Fin 3 → ZMod p) × W))) ∪
        (T : Set _) ∪ {jR, jT})
    (∀ d,
      q '' pointStabilizerOrbit Y d =
        (fun (x, z, w) => (z, x, w)) '' pointStabilizerOrbit Y d) ∧
    ∀ S : Set ((Fin 3 → ZMod p) × (Fin 3 → ZMod p) × W),
      0 ∉ S →
      (∀ d, d ∈ S → pointStabilizerOrbit Y d ⊆ S) →
      q '' S = (fun (x, z, w) => (z, x, w)) '' S

end MathlibPlus.Open.ResearchBatch.Henon
