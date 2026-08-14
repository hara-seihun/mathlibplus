import Mathlib

noncomputable section

namespace MathlibPlus.Open.ResearchFormalizationBatch

/-- Claim 59467: equality at one point and equality of derivatives elsewhere. -/
def claim59467 : Prop :=
  ∀ (f g : ℝ → ℝ) (a : ℝ),
    Differentiable ℝ f →
    Differentiable ℝ g →
    f a = g a →
    (∀ x : ℝ, x ≠ a → deriv f x = deriv g x) →
    f = g

/-- Claim 59470: the stated quantitative bound. -/
def claim59470 : Prop :=
  ∀ (Λ t y : ℝ),
    Λ ≤ t + y ^ 2 / 2 →
    t ≤ (1579 : ℝ) / 10000 →
    |y| ≤ (1 : ℝ) / 10 →
    Λ ≤ (1629 : ℝ) / 10000

abbrev F7 := ZMod 7

/-- The two signs in the first coordinate of the displayed semidirect product. -/
def Sign := {a : F7 // a = 1 ∨ a = -1}

abbrev H := Sign × (F7 × F7)

instance : Finite Sign :=
  Finite.of_injective (fun x : Sign => x.1) Subtype.val_injective
instance : DecidableEq Sign := Classical.decEq Sign
instance : Fintype Sign := Fintype.ofFinite Sign
instance : DecidableEq H := Classical.decEq H
instance : Fintype H := Fintype.ofFinite H

def posSign : Sign := ⟨1, Or.inl rfl⟩

def negSign : Sign := ⟨-1, Or.inr rfl⟩

def signMul (a b : Sign) : Sign :=
  ⟨a.1 * b.1, by
    rcases a.2 with ha | ha <;> rcases b.2 with hb | hb <;>
      simp [ha, hb]⟩

def hMul (x y : H) : H :=
  (signMul x.1 y.1,
    (x.2.1 + x.1.1 * y.2.1, x.2.2 + x.1.1 * y.2.2))

def hInv (x : H) : H :=
  (x.1, (-x.1.1 * x.2.1, -x.1.1 * x.2.2))

def hOne : H := (posSign, (0, 0))

def P (t : F7) : Finset H :=
  (Finset.univ : Finset F7).image
    (fun z : F7 => (negSign, (t + z ^ 2, 2 * z)))

def C (t : F7) : Finset H :=
  (Finset.univ : Finset F7).image
    (fun z : F7 => (posSign, (z, t)))

def S : Finset H := P 0 ∪ P 1 ∪ P 3 ∪ C 1 ∪ C (-1)

def theta (x : H) : H :=
  (x.1, (x.2.1 ^ 2 * (4 : F7) - x.2.2, x.1.1 * x.2.1))

def T : Finset H :=
  (Finset.univ : Finset H).filter (fun x => theta x ∈ S)

def inverseClosed {α : Type*} (inv : α → α) (A : Finset α) : Prop :=
  ∀ x, x ∈ A → inv x ∈ A

def hCayleyAdj (A : Finset H) (x y : H) : Prop :=
  hMul x (hInv y) ∈ A

def hCayleyIso (A B : Finset H) : Prop :=
  ∃ e : H → H,
    Function.Bijective e ∧
      ∀ x y, hCayleyAdj A x y ↔ hCayleyAdj B (e x) (e y)

def hAutomorphism (α : H → H) : Prop :=
  Function.Bijective α ∧ ∀ x y, α (hMul x y) = hMul (α x) (α y)

def hUndirectedCI : Prop :=
  ∀ A B : Finset H,
    inverseClosed hInv A →
    inverseClosed hInv B →
    hCayleyIso A B →
    ∃ α : H → H, hAutomorphism α ∧ A.image α = B

/-- Claim 59469: the explicit order-seven semidirect-product witness. -/
def claim59469 : Prop :=
  S.card = 35 ∧
  T.card = 35 ∧
  inverseClosed hInv S ∧
  inverseClosed hInv T ∧
  (Function.Bijective theta ∧
    ∀ x y, hCayleyAdj T x y ↔ hCayleyAdj S (theta x) (theta y)) ∧
  (¬ ∃ α : H → H, hAutomorphism α ∧ T.image α = S) ∧
  ¬ hUndirectedCI

/-- Adjacency in a Cayley graph for the finite-group statement. -/
def groupCayleyAdj {G : Type*} [Group G] [DecidableEq G]
    (A : Finset G) (x y : G) : Prop :=
  x * y⁻¹ ∈ A

def groupCayleyIso {G : Type*} [Group G] [DecidableEq G]
    (A B : Finset G) : Prop :=
  ∃ e : G → G,
    Function.Bijective e ∧
      ∀ x y, groupCayleyAdj A x y ↔ groupCayleyAdj B (e x) (e y)

def groupInverseClosed {G : Type*} [Group G] [DecidableEq G] (A : Finset G) : Prop :=
  ∀ x, x ∈ A → x⁻¹ ∈ A

def groupNoIdentity {G : Type*} [Group G] [DecidableEq G] (A : Finset G) : Prop :=
  ∀ x, x ∈ A → x ≠ 1

def groupAutomorphism {G : Type*} [Group G] (α : G → G) : Prop :=
  Function.Bijective α ∧ ∀ x y, α (x * y) = α x * α y

/-- Claim 59814: all groups of order at most seven are undirected CI-groups. -/
def claim59814 : Prop :=
  ∀ {G : Type*} [Group G] [Fintype G] [DecidableEq G],
    Fintype.card G ≤ 7 →
    ∀ S T : Finset G,
      groupInverseClosed S →
      groupInverseClosed T →
      groupNoIdentity S →
      groupNoIdentity T →
      groupCayleyIso S T →
      ∃ α : G → G, groupAutomorphism α ∧ S.image α = T

end MathlibPlus.Open.ResearchFormalizationBatch
