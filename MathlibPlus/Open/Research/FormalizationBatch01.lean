import Mathlib

open scoped BigOperators

namespace MathlibPlus.Open.Research.FormalizationBatch01

/-! Exact open statements for the admitted research claims in this batch. -/

abbrev Fp (p : ℕ) := ZMod p

/-- The pointwise meaning of an odd map used by the transport constructions. -/
def OddMap {α β : Type*} [Neg α] [Neg β] (f : α → β) : Prop :=
  ∀ x, f (-x) = -f x

private def coordL1 (p : ℕ) (v : Fin 3 → Fp p) : Fin 3 → Fp p :=
  fun i => if i = (0 : Fin 3) then v 0 + v 1
    else if i = (1 : Fin 3) then v 1 + v 2
    else v 2

private def coordLm (p : ℕ) (v : Fin 3 → Fp p) : Fin 3 → Fp p :=
  fun i => if i = (0 : Fin 3) then v 0 + v 2
    else if i = (1 : Fin 3) then v 1
    else v 2

private def coordL2 (p : ℕ) (v : Fin 3 → Fp p) : Fin 3 → Fp p :=
  fun i => if i = (0 : Fin 3) then v 0
    else if i = (1 : Fin 3) then v 0 + v 1
    else v 2

private def coordH1 (p : ℕ) (c₁ : Fp p) (v : Fin 3 → Fp p) : Fin 3 → Fp p :=
  fun i => if i = (0 : Fin 3) then v 0 + c₁ * (v 1)^2 * (v 2)^(p - 2)
    else if i = (1 : Fin 3) then v 1
    else v 2

private def coordH2 (p : ℕ) (c₂ : Fp p) (v : Fin 3 → Fp p) : Fin 3 → Fp p :=
  fun i => if i = (0 : Fin 3) then v 0 + c₂ * (v 1)^(p - 2) * (v 2)^2
    else if i = (1 : Fin 3) then v 1
    else v 2

private def qMap (p : ℕ) (c₁ c₂ : Fp p) (v : Fin 3 → Fp p) : Fin 3 → Fp p :=
  coordL2 p (coordH2 p c₂ (coordLm p (coordH1 p c₁ (coordL1 p v))))

private def matrixL1 (p : ℕ) : Matrix (Fin 3) (Fin 3) (Fp p) :=
  fun i j => if i = (0 : Fin 3) then
      if j = (0 : Fin 3) ∨ j = (1 : Fin 3) then 1 else 0
    else if i = (1 : Fin 3) then
      if j = (1 : Fin 3) ∨ j = (2 : Fin 3) then 1 else 0
    else if j = (2 : Fin 3) then 1 else 0

private def matrixLm (p : ℕ) : Matrix (Fin 3) (Fin 3) (Fp p) :=
  fun i j => if i = (0 : Fin 3) then
      if j = (0 : Fin 3) ∨ j = (2 : Fin 3) then 1 else 0
    else if i = (1 : Fin 3) then
      if j = (1 : Fin 3) then 1 else 0
    else if j = (2 : Fin 3) then 1 else 0

private def matrixL2 (p : ℕ) : Matrix (Fin 3) (Fin 3) (Fp p) :=
  fun i j => if i = (0 : Fin 3) then
      if j = (0 : Fin 3) then 1 else 0
    else if i = (1 : Fin 3) then
      if j = (0 : Fin 3) ∨ j = (1 : Fin 3) then 1 else 0
    else if j = (2 : Fin 3) then 1 else 0

/-- Claim 56679: the displayed two-layer map is an odd pointed permutation. -/
def claim56679 : Prop :=
  ∀ (p : ℕ), Nat.Prime p → Odd p → ∀ c₁ c₂ : Fp p,
    Matrix.det (matrixL1 p) = 1 ∧
    Matrix.det (matrixLm p) = 1 ∧
    Matrix.det (matrixL2 p) = 1 ∧
    Function.Bijective (coordL1 p) ∧ OddMap (coordL1 p) ∧
    Function.Bijective (coordLm p) ∧ OddMap (coordLm p) ∧
    Function.Bijective (coordL2 p) ∧ OddMap (coordL2 p) ∧
    Function.Bijective (coordH1 p c₁) ∧ OddMap (coordH1 p c₁) ∧
    Function.Bijective (coordH2 p c₂) ∧ OddMap (coordH2 p c₂) ∧
    2 + (p - 2) = p ∧
    (p - 2) + 2 = p ∧
    Function.Bijective (qMap p c₁ c₂) ∧
    qMap p c₁ c₂ 0 = 0 ∧
    OddMap (qMap p c₁ c₂)

/-- Nonabelian simplicity, stated without hiding the group-theoretic hypotheses. -/
def NonabelianSimple (G : Type*) [Group G] : Prop :=
  Nontrivial G ∧ IsSimpleGroup G ∧ ∃ a b : G, a * b ≠ b * a

/-- A finite partition of an index set, written explicitly as sets. -/
def IsFinitePartition {I : Type*} (P : Set (Set I)) : Prop :=
  P.Finite ∧
    (∀ C ∈ P, C.Nonempty) ∧
    (∀ C ∈ P, ∀ D ∈ P, C ≠ D → Disjoint C D) ∧
    ⋃₀ P = Set.univ

/-- The element of a diagonal strip supported on `C` and carrying `s`. -/
noncomputable def diagonalStripElement {I : Type*} {S : I → Type*}
    [∀ i, Group (S i)] (C : Set I) (r : I)
    (α : ∀ i, i ∈ C → (S r ≃* S i)) (s : S r) : ∀ i, S i := by
  classical
  exact fun i => if hi : i ∈ C then α i hi s else 1

/-- Claim 56667: every finite subdirect product of nonabelian finite simple
factors is a product of disjoint full diagonal strips. -/
def claim56667 {I : Type*} [Finite I] (S : I → Type*)
    [∀ i, Group (S i)] (M : Subgroup (∀ i, S i)) : Prop :=
  (∀ i, Finite (S i) ∧ NonabelianSimple (S i)) ∧
    (∀ i (s : S i), ∃ x : (∀ i, S i), x ∈ M ∧ x i = s) →
    ∃ P : Set (Set I),
      IsFinitePartition P ∧
      ∃ r : ∀ C : {C // C ∈ P}, I,
        (∀ C, r C ∈ C.1) ∧
        ∃ α : ∀ (C : {C // C ∈ P}) (i : I), i ∈ C.1 → (S (r C) ≃* S i),
          M.carrier =
            {x | ∃ s : ∀ C : {C // C ∈ P}, S (r C),
              ∀ i, ∃ C : {C // C ∈ P},
                ∃ hi : i ∈ C.1, x i = α C i hi (s C)}

abbrev V₆ := Fin 6 → ZMod 5

/-- The canonical mathematical key represented by the RREF of a pair: its
row-span 2-space. -/
def twoSpaceKey (a b : V₆) : Submodule (ZMod 5) V₆ :=
  Submodule.span (ZMod 5) ({a, b} : Set V₆)

def pairGeneratesTwoSpace (S : Finset V₆) (W : Submodule (ZMod 5) V₆) : Prop :=
  ∃ a ∈ S, ∃ b ∈ S,
    LinearIndependent (ZMod 5) ![a, b] ∧ W = twoSpaceKey a b

noncomputable def twoSpaceIntersectionCard (S : Finset V₆) (W : Submodule (ZMod 5) V₆) : ℕ := by
  classical
  letI := Fintype.ofFinite V₆
  exact Fintype.card {x : W // (x : V₆) ∈ S}

noncomputable def twoSpaceProfile (S : Finset V₆) (r : ℕ) : ℕ := by
  classical
  letI := Fintype.ofFinite V₆
  letI := Fintype.ofFinite (Submodule (ZMod 5) V₆)
  exact Fintype.card {W : Submodule (ZMod 5) V₆ //
    pairGeneratesTwoSpace S W ∧ twoSpaceIntersectionCard S W = r}

def mapFinsetLinearEquiv (g : V₆ ≃ₗ[ZMod 5] V₆) (S : Finset V₆) : Finset V₆ :=
  S.map g.toEmbedding

/-- Claim 56688: the RREF/span key and its intersection histogram are invariant
under every element of `GL(6,5)`. -/
def claim56688 : Prop :=
  ∀ (S : Finset V₆) (g : V₆ ≃ₗ[ZMod 5] V₆) (r : ℕ),
    twoSpaceProfile (mapFinsetLinearEquiv g S) r = twoSpaceProfile S r

end MathlibPlus.Open.Research.FormalizationBatch01
