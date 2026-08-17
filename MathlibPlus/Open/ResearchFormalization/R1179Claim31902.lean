import Mathlib
import Mathlib.GroupTheory.SpecificGroups.Dihedral
import MathlibPlus.Open.Research.FormalizationBatch1113_1116

namespace MathlibPlus.Open.ResearchFormalization.R1179Claim31902

noncomputable section

private abbrev DihedralCoordinate (m : ℕ) := ZMod m × Bool
private abbrev Vertex (A : Type*) (m : ℕ) := A × DihedralGroup m
private abbrev SymmetricBase (A : Type*) (m : ℕ) :=
  ZMod m → Equiv.Perm A

private def dihedralCoordinate (m : ℕ) (g : DihedralGroup m) :
    DihedralCoordinate m :=
  MathlibPlus.Open.ResearchFormalizationBatch.dihedralCoordinateEquiv m g

private def matchingIndex (m : ℕ) (g : DihedralGroup m) : ZMod m :=
  match dihedralCoordinate m g with
  | (i, false) => i
  | (i, true) => 1 - i

private def rotation (m : ℕ) : DihedralGroup m :=
  DihedralGroup.r 1

private def reflection (m : ℕ) : DihedralGroup m :=
  DihedralGroup.sr 0

private def thickThinConnection {A : Type*} [Group A]
    (m : ℕ) : Set (Vertex A m) :=
  (Set.univ : Set A) ×ˢ {reflection m} ∪
    {(1, rotation m * reflection m)}

private def rightCayleyAdjacency {A : Type*} [Group A]
    (m : ℕ) (x y : Vertex A m) : Prop :=
  ∃ s : Vertex A m, s ∈ thickThinConnection m ∧ y = x * s

private def graphAutomorphism {A : Type*} [Group A]
    (m : ℕ) (e : Equiv.Perm (Vertex A m)) : Prop :=
  ∀ x y : Vertex A m,
    rightCayleyAdjacency m x y ↔
      rightCayleyAdjacency m (e x) (e y)

private def regularPermutationSubgroup {Ω : Type*}
    (T : Subgroup (Equiv.Perm Ω)) : Prop :=
  ∀ x y : Ω, ∃! t : T, t.1 x = y

private def baseFunction {A : Type*} [Group A]
    (m : ℕ) (b : SymmetricBase A m) : Vertex A m → Vertex A m :=
  fun x => (b (matchingIndex m x.2) x.1, x.2)

private def liesInSymmetricBase {A : Type*} [Group A]
    (m : ℕ) (P : Subgroup (Equiv.Perm (Vertex A m))) : Prop :=
  ∀ p : P, ∃ b : SymmetricBase A m,
    ∀ x : Vertex A m, p.1 x = baseFunction m b x

private def characteristicWithin
    {A : Type*} [Group A] (m : ℕ)
    (P T : Subgroup (Equiv.Perm (Vertex A m)))
    (hPT : P ≤ T) : Prop :=
  ∀ φ : T ≃* T,
    {x : Equiv.Perm (Vertex A m) |
        ∃ p : P, x = (φ ⟨p.1, hPT p.2⟩).1} =
      {x : Equiv.Perm (Vertex A m) | ∃ p : P, x = p.1}

private def hallPiFactor {A : Type*} [Fintype A]
    (P T : Subgroup (Equiv.Perm (Vertex A m))) : Prop :=
  Nat.card P ∣ Nat.card T ∧
    (∀ q : ℕ, Nat.Prime q → q ∣ Nat.card P →
      q ∣ Fintype.card A) ∧
    (∀ q : ℕ, Nat.Prime q → q ∣ Nat.card T / Nat.card P →
      ¬ q ∣ Fintype.card A)

private def fiberAction {A : Type*} [Group A]
    (P : Subgroup (Equiv.Perm (Vertex A m)))
    (i : ZMod m) (p : P) (a : A) : A :=
  (p.1 (a, DihedralGroup.r i)).1

private def coordinateFaithful {A : Type*} [Group A]
    (P : Subgroup (Equiv.Perm (Vertex A m))) (i : ZMod m) : Prop :=
  ∀ p : P, (∀ a : A, fiberAction P i p a = a) → p = 1

private def coordinateImage {A : Type*} [Group A]
    (P : Subgroup (Equiv.Perm (Vertex A m))) (i : ZMod m)
    (H : Subgroup (Equiv.Perm A)) : Prop :=
  (∀ h : H, ∃ p : P, ∀ a : A, h.1 a = fiberAction P i p a) ∧
    (∀ p : P, ∃ h : H, ∀ a : A, h.1 a = fiberAction P i p a)

private def coordinateRegular {A : Type*} [Group A] [Fintype A]
    (P : Subgroup (Equiv.Perm (Vertex A m))) (i : ZMod m) : Prop :=
  ∃ H : Subgroup (Equiv.Perm A),
    coordinateImage P i H ∧
      Nat.card H = Fintype.card A ∧
      (∀ h : H, ∀ a : A, h.1 a = a → h = 1) ∧
      (∀ a b : A, ∃! h : H, h.1 a = b)

/-- Claim 31902: in the exact alternating thick--thin Cayley family, every
    Hall coordinate projection is faithful and regular on its n-point fibre. -/
def allHallCoordinateProjectionsRegular_claim31902 : Prop :=
  ∀ (A : Type*) [Group A] [Fintype A] [Nontrivial A]
    (m : ℕ),
    3 ≤ m → Nat.Coprime (Fintype.card A) (2 * m) →
    ∀ (T P : Subgroup (Equiv.Perm (Vertex A m))),
      (∀ t : T, graphAutomorphism m t.1) →
      regularPermutationSubgroup T →
      Nonempty (T ≃* A × DihedralGroup m) →
      ∀ hPT : P ≤ T,
        Nonempty (P ≃* A) →
        hallPiFactor P T →
        characteristicWithin m P T hPT →
        liesInSymmetricBase m P →
        ∀ i : ZMod m,
        coordinateFaithful P i ∧ coordinateRegular P i

end

end MathlibPlus.Open.ResearchFormalization.R1179Claim31902
