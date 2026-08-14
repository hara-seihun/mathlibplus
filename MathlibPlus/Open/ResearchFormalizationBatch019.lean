import Mathlib

namespace MathlibPlus.Open.ResearchFormalizationBatch019

open scoped BigOperators

/-- The fixed (1,1,10) block orbit described in Claim 44693. -/
def fixedOrbit44693 {α : Type*} [Fintype α] [DecidableEq α]
    (M₁ M₂ M₃ : Finset α) (z : α) : Finset (Finset α) :=
  (M₁ ∪ M₂ ∪ M₃).powerset.filter fun S =>
    (S ∩ M₁).card = 1 ∧
      (S ∩ M₂).card = 1 ∧
      (S ∩ M₃).card = 10 ∧
      z ∉ S

def claim_44693 : Prop :=
  ∀ {α : Type*} [Fintype α] [DecidableEq α]
    (M₁ M₂ M₃ : Finset α) (z : α),
    M₁.card = 3 → M₂.card = 10 → M₃.card = 10 →
    Disjoint M₁ M₂ → Disjoint M₁ M₃ → Disjoint M₂ M₃ →
    z ∉ M₁ ∪ M₂ ∪ M₃ →
    let O := fixedOrbit44693 M₁ M₂ M₃ z
    O.card = 30 ∧
      ∀ ⦃S T : Finset α⦄,
        S ∈ O → T ∈ O → S ≠ T →
        ((S ∪ T) ∩ M₁).card = 2 ∨ ((S ∪ T) ∩ M₂).card = 2

/-- The binary clique cut and its all-one-half fractional point. -/
def claim_44695 : Prop :=
  (∀ (x : Fin 30 → ℝ),
      (∀ i, x i = 0 ∨ x i = 1) →
      (∀ i j, i ≠ j → x i + x j ≤ 1) →
      (∑ i : Fin 30, x i) ≤ 1) ∧
    (let x : Fin 30 → ℝ := fun _ => (1 / 2 : ℝ)
     (∑ i : Fin 30, x i = 15 ∧ ¬ ((∑ i : Fin 30, x i) ≤ 1)))

def moment44737 {R : Type*} [CommRing R]
    (m : ℕ) (x : Fin m → R) (y : R) (z : Fin m → R) (k : ℕ) : R :=
  (y - 1) ^ k + ∑ i : Fin m, x i * (x i * (y - z i)) ^ k

def claim_44737 : Prop :=
  ∀ (m : ℕ) {R : Type*} [CommRing R]
    (x : Fin m → R) (y : R) (z : Fin m → R),
    Matrix.det (fun i j : Fin (m + 2) =>
      moment44737 m x y z ((i : ℕ) + (j : ℕ))) = 0

abbrev Q8 := ZMod 4 × Bool

def q8Mul (x y : Q8) : Q8 :=
  (x.1 + (if x.2 then -y.1 else y.1) +
      (if x.2 && y.2 then (2 : ZMod 4) else 0),
    Bool.xor x.2 y.2)

def q8One : Q8 := (0, false)
def q8NegOne : Q8 := (2, false)

def q8Atom (i : Fin 3) : Finset Q8 :=
  match i.1 with
  | 0 => {(1, false), (3, false)}
  | 1 => {(0, true), (2, true)}
  | _ => {(1, true), (3, true)}

def q8Automorphism (f : Q8 ≃ Q8) : Prop :=
  ∀ x y, f (q8Mul x y) = q8Mul (f x) (f y)

def q8Inv (x : Q8) : Q8 :=
  (if x.2 then x.1 + 2 else -x.1, x.2)

def q8ConnectionSets : Finset (Finset Q8) := by
  classical
  exact Finset.univ.filter fun S =>
    q8One ∉ S ∧ ∀ x ∈ S, q8Inv x ∈ S

noncomputable def q8Autos : Finset (Q8 ≃ Q8) := by
  classical
  exact Finset.univ.filter q8Automorphism

noncomputable def q8Orbit (S : Finset Q8) : Finset (Finset Q8) := by
  classical
  exact Finset.image (fun f : Q8 ≃ Q8 => Finset.image f S) q8Autos

def q8Adj (S : Finset Q8) (x y : Q8) : Prop :=
  x ≠ y ∧ q8Inv (q8Mul (q8Inv x) y) ∈ S

def q8GraphIso (S T : Finset Q8) : Prop :=
  ∃ e : Q8 ≃ Q8, ∀ x y, q8Adj S x y ↔ q8Adj T (e x) (e y)

def claim_44713 : Prop :=
  (∀ f : Q8 ≃ Q8, q8Automorphism f → f q8NegOne = q8NegOne) ∧
    (∀ f : Q8 ≃ Q8, q8Automorphism f →
      ∃ σ : Equiv.Perm (Fin 3),
        ∀ i, Finset.image f (q8Atom i) = q8Atom (σ i)) ∧
    (∀ σ : Equiv.Perm (Fin 3),
      ∃ f : Q8 ≃ Q8,
        q8Automorphism f ∧
          ∀ i, Finset.image f (q8Atom i) = q8Atom (σ i))

def claim_44715 : Prop :=
  q8ConnectionSets.card = 16 ∧
    q8Autos.card = 24 ∧
    (∀ S T : Finset Q8,
      S ∈ q8ConnectionSets → T ∈ q8ConnectionSets →
      (T ∈ q8Orbit S ↔ q8GraphIso S T)) ∧
    (∃ reps : Fin 8 → Finset Q8,
      (∀ i, reps i ∈ q8ConnectionSets) ∧
      (∀ i j, i ≠ j → reps j ∉ q8Orbit (reps i)) ∧
      (∀ S, S ∈ q8ConnectionSets → ∃ i, S ∈ q8Orbit (reps i)) ∧
      (∀ i, (q8Orbit (reps i)).card = if (i : ℕ) < 4 then 1 else 3))

end MathlibPlus.Open.ResearchFormalizationBatch019
