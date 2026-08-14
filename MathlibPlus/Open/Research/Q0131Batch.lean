import Mathlib

namespace MathlibPlus.Open.Research.Q0131

/-- The k-subsets of a ground set of size 2k. -/
def KSubset (k : ℕ) := {s : Finset (Fin (2 * k)) // s.card = k}

/-- A k-subset obtained by deleting a member of a (k+1)-subset. -/
def deleteSubset (k : ℕ) (A : Finset (Fin (2 * k))) (hA : A.card = k + 1)
    (a : Fin (2 * k)) (ha : a ∈ A) : KSubset k :=
  ⟨A.erase a, by
    have h := Finset.card_erase_of_mem ha
    omega⟩

/-- A coloring of the Boolean middle layer by k+1 colors. -/
def ColorTable (k : ℕ) := KSubset k → Fin (k + 1)

noncomputable instance instDecidableEqKSubset (k : ℕ) : DecidableEq (KSubset k) :=
  Classical.decEq _

noncomputable instance instFintypeKSubset (k : ℕ) : Fintype (KSubset k) := by
  letI : Finite (KSubset k) :=
    Finite.of_injective (fun s : KSubset k => s.1) Subtype.val_injective
  exact Fintype.ofFinite _

/-- The deletion of a has color r, with the membership proof kept explicit. -/
def deletionHasColor (k : ℕ) (c : ColorTable k) (A : Finset (Fin (2 * k)))
    (hA : A.card = k + 1) (a : Fin (2 * k)) (r : Fin (k + 1)) : Prop :=
  ∃ ha : a ∈ A, c (deleteSubset k A hA a ha) = r

/-- Claim 16785: the perfect-rainbow condition on every deletion clique. -/
def perfectRainbow (k : ℕ) (c : ColorTable k) : Prop :=
  ∀ (A : Finset (Fin (2 * k))), ∀ hA : A.card = k + 1,
    ∀ r : Fin (k + 1), ∃! a : Fin (2 * k), deletionHasColor k c A hA a r

/-- Adjacency in the Johnson graph J(2k,k). -/
def johnsonAdjacent (k : ℕ) (S T : KSubset k) : Prop :=
  S ≠ T ∧ (S.1 ∩ T.1).card = k - 1

/-- Proper coloring of the Johnson graph with m available colors. -/
def properJohnsonColoring (k m : ℕ) (c : KSubset k → Fin m) : Prop :=
  ∀ ⦃S T : KSubset k⦄, johnsonAdjacent k S T → c S ≠ c T

/-- Claim 16787: perfect rainbows and proper (k+1)-colorings coincide. -/
def claim16787 (k : ℕ) : Prop :=
  ∀ c : ColorTable k,
    perfectRainbow k c ↔ properJohnsonColoring k (k + 1) c

/-- The deletion clique determined by a (k+1)-subset. -/
noncomputable def deletionClique (k : ℕ) (A : Finset (Fin (2 * k))) (hA : A.card = k + 1) :
    Finset (KSubset k) :=
  A.attach.image (fun a => deleteSubset k A hA a.1 a.2)

/-- Pairwise-clique predicate for the Johnson graph. -/
def isJohnsonClique (k : ℕ) (C : Finset (KSubset k)) : Prop :=
  ∀ ⦃S T : KSubset k⦄, S ∈ C → T ∈ C → S ≠ T → johnsonAdjacent k S T

/-- Colorability by m colors. -/
def johnsonColorable (k m : ℕ) : Prop :=
  ∃ c : KSubset k → Fin m, properJohnsonColoring k m c

/-- The usual minimum number of colors of the finite Johnson graph. -/
noncomputable def johnsonChromaticNumber (k : ℕ) : ℕ := by
  classical
  exact Nat.find (show ∃ m : ℕ, johnsonColorable k m from by
    let e : KSubset k ≃ Fin (Fintype.card (KSubset k)) := Fintype.equivFin (KSubset k)
    refine ⟨Fintype.card (KSubset k), e, ?_⟩
    intro S T hAdj hEq
    exact hAdj.1 (e.injective hEq))

/-- Claim 16788: deletion cliques give the lower bound, with equality exactly at a perfect coloring. -/
def claim16788 (k : ℕ) : Prop :=
  (∀ (A : Finset (Fin (2 * k))), ∀ hA : A.card = k + 1,
      isJohnsonClique k (deletionClique k A hA) ∧
        (deletionClique k A hA).card = k + 1) ∧
    johnsonChromaticNumber k ≥ k + 1 ∧
    (johnsonChromaticNumber k = k + 1 ↔
      ∃ c : ColorTable k, perfectRainbow k c)

/-- Claim 16789: the stated small cases. -/
def claim16789 : Prop :=
  (∃ c : ColorTable 2, perfectRainbow 2 c) ∧
    ∀ k : ℕ, 3 ≤ k → k ≤ 8 → ¬ ∃ c : ColorTable k, perfectRainbow k c

/-- Subsets of a finite type with a prescribed cardinality. -/
def SubsetOfCard (α : Type*) [DecidableEq α] (n : ℕ) := {s : Finset α // s.card = n}

/-- A t-(v,b,1) Steiner system, represented by its finite block family. -/
def steinerSystem (t b v : ℕ)
    (B : Finset (SubsetOfCard (Fin v) b)) : Prop :=
  ∀ T : SubsetOfCard (Fin v) t,
    (B.filter (fun block => T.1 ⊆ block.1)).card = 1

/-- The color class of a color table. -/
noncomputable def colorClass (k : ℕ) (c : ColorTable k) (r : Fin (k + 1)) : Finset (KSubset k) := by
  classical
  exact Finset.univ.filter (fun S => c S = r)

/-- A large set of k+1 Steiner systems, including its partition and independence. -/
def largeSet (k : ℕ) (classes : Fin (k + 1) → Finset (KSubset k)) : Prop :=
  (∀ r : Fin (k + 1), steinerSystem (k - 1) k (2 * k) (classes r)) ∧
    (∀ S : KSubset k, ∃! r : Fin (k + 1), S ∈ classes r) ∧
    (∀ (r : Fin (k + 1)) ⦃S T : KSubset k⦄,
      S ∈ classes r → T ∈ classes r → ¬ johnsonAdjacent k S T)

/-- Claim 16790: the coloring/large-set equivalence. -/
def claim16790 (k : ℕ) : Prop :=
  (∀ c : ColorTable k,
      properJohnsonColoring k (k + 1) c ↔
        largeSet k (fun r => colorClass k c r)) ∧
    (∀ classes : Fin (k + 1) → Finset (KSubset k),
      largeSet k classes →
        ∃ c : ColorTable k,
          properJohnsonColoring k (k + 1) c ∧
            ∀ r : Fin (k + 1), colorClass k c r = classes r)

/-- Claim 16791: the necessary divisibility family. -/
def claim16791 : Prop :=
  ∀ k : ℕ,
    (∃ c : ColorTable k, perfectRainbow k c) →
      ∀ t : ℕ, 1 ≤ t → t ≤ k → t ∣ Nat.choose (k + t) (t - 1)

/-- The elementary arithmetic meaning of composite used in Claim 16792. -/
def isComposite (n : ℕ) : Prop :=
  ∃ a b : ℕ, 2 ≤ a ∧ 2 ≤ b ∧ a * b = n

/-- Claim 16792: the composite-palette obstruction. -/
def claim16792 : Prop :=
  ∀ k : ℕ, 2 < k → isComposite (k + 1) →
    (¬ ∃ c : ColorTable k, perfectRainbow k c) ∧
      johnsonChromaticNumber k > k + 1

/-- Claim 16798: the two stated Steiner systems do not exist. -/
def claim16798 : Prop :=
  (¬ ∃ B : Finset (SubsetOfCard (Fin 15) 5), steinerSystem 4 5 15 B) ∧
    ¬ ∃ B : Finset (SubsetOfCard (Fin 17) 5), steinerSystem 4 5 17 B

/-- Claim 16799: the two reductions and their equivalent chromatic lower bounds. -/
def claim16799 : Prop :=
  (∀ c : ColorTable 10, perfectRainbow 10 c →
      ∃ B : Finset (SubsetOfCard (Fin 15) 5), steinerSystem 4 5 15 B) ∧
    (∀ c : ColorTable 12, perfectRainbow 12 c →
      ∃ B : Finset (SubsetOfCard (Fin 17) 5), steinerSystem 4 5 17 B) ∧
    (¬ ∃ c : ColorTable 10, perfectRainbow 10 c) ∧
    (¬ ∃ c : ColorTable 12, perfectRainbow 12 c) ∧
    johnsonChromaticNumber 10 ≥ 12 ∧
    johnsonChromaticNumber 12 ≥ 14

/-- A permutation preserves a block family when it maps exactly its blocks to blocks. -/
def preservesBlocks {b v : ℕ}
    (B : Finset (SubsetOfCard (Fin v) b)) (σ : Equiv.Perm (Fin v)) : Prop :=
  ∀ X : SubsetOfCard (Fin v) b,
    X ∈ B ↔ ∃ Y : SubsetOfCard (Fin v) b,
      Y ∈ B ∧ Y.1 = X.1.map σ.toEmbedding

noncomputable def automorphismOrder {b v : ℕ}
    (B : Finset (SubsetOfCard (Fin v) b)) : ℕ := by
  classical
  exact (Finset.univ.filter (fun σ : Equiv.Perm (Fin v) => preservesBlocks B σ)).card

/-- Claim 16801: the allowed orders of the full automorphism group. -/
def claim16801 : Prop :=
  ∀ B : Finset (SubsetOfCard (Fin 21) 5),
    steinerSystem 4 5 21 B →
      automorphismOrder B ∈ ({1, 2, 3, 4, 5, 6, 7, 10} : Finset ℕ)

/-- Boolean variables for the exact finite encoding. -/
def BooleanAssignment (k : ℕ) := KSubset k → Fin (k + 1) → Bool

/-- The Boolean constraints stated in Claim 16809. -/
def booleanPerfectEncoding (k : ℕ) (x : BooleanAssignment k) : Prop := by
  classical
  exact
    (∀ S : KSubset k, (Finset.univ.filter (fun r => x S r)).card = 1) ∧
      (∀ (A : Finset (Fin (2 * k))), ∀ hA : A.card = k + 1,
        ∀ r : Fin (k + 1),
          (Finset.univ.filter (fun a =>
            if ha : a ∈ A then x (deleteSubset k A hA a ha) r else false)).card = 1)

/-- The color-table assignment associated to a coloring. -/
def colorTableAssignment (k : ℕ) (c : ColorTable k) : BooleanAssignment k :=
  fun S r => decide (c S = r)

/-- Claim 16809: the Boolean encoding has exactly the perfect color tables as solutions. -/
def claim16809 : Prop :=
  ∀ k : ℕ, ∀ x : BooleanAssignment k, booleanPerfectEncoding k x ↔
    ∃ c : ColorTable k, perfectRainbow k c ∧ x = colorTableAssignment k c

end MathlibPlus.Open.Research.Q0131
