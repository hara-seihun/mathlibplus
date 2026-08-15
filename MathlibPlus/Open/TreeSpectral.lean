import Mathlib

open scoped BigOperators

namespace MathlibPlus.Open.TreeSpectral

noncomputable section

/-- A finite unrooted tree with a fixed `n`-element vertex set. -/
def TreeGraph (n : ℕ) := {G : SimpleGraph (Fin n) // G.IsTree}

def TreeGraphSetoid (n : ℕ) : Setoid (TreeGraph n) where
  r A B := Nonempty (A.1 ≃g B.1)
  iseqv := by
    refine ⟨?_, ?_, ?_⟩
    · intro A
      exact ⟨SimpleGraph.Iso.refl⟩
    · intro A B h
      exact h.map SimpleGraph.Iso.symm
    · intro A B C hAB hBC
      rcases hAB with ⟨f⟩
      rcases hBC with ⟨g⟩
      exact ⟨SimpleGraph.Iso.comp g f⟩

def TreeClass (n : ℕ) := Quotient (TreeGraphSetoid n)

instance treeGraphFinite (n : ℕ) : Finite (TreeGraph n) :=
  Finite.of_injective Subtype.val Subtype.val_injective

noncomputable instance treeGraphFintype (n : ℕ) : Fintype (TreeGraph n) :=
  Fintype.ofFinite _

noncomputable instance treeClassFintype (n : ℕ) : Fintype (TreeClass n) := by
  classical
  exact Quotient.fintype (TreeGraphSetoid n)

/-- The rational span of the isomorphism classes of `n`-vertex unrooted trees. -/
abbrev TreeSpace (n : ℕ) := TreeClass n →₀ ℚ

def GraphIso {α β : Type*} (G : SimpleGraph α) (H : SimpleGraph β) : Prop :=
  Nonempty (G ≃g H)

def IsLeaf {n : ℕ} (G : SimpleGraph (Fin n)) (v : Fin n) : Prop := by
  classical
  exact Fintype.card {w : Fin n // G.Adj v w} = 1

/-- Add a new leaf, represented by `Fin.last n`, at an existing vertex. -/
def graftGraph {n : ℕ} (G : SimpleGraph (Fin n)) (v : Fin n) : SimpleGraph (Fin (n + 1)) :=
  SimpleGraph.fromRel (fun x y =>
    if hxy : x.val < n ∧ y.val < n then
      G.Adj ⟨x.val, hxy.1⟩ ⟨y.val, hxy.2⟩
    else
      x = Fin.last n ∧ y = Fin.castSucc v)

/-- The basis action of leaf deletion, with one contribution for each leaf occurrence. -/
def leafDeletionBasis (n : ℕ) (q : TreeClass n) : TreeSpace (n - 1) := by
  classical
  let T := Quotient.out q
  exact ∑ ℓ : Fin n, ∑ u : TreeClass (n - 1),
    Finsupp.single u
      (if IsLeaf T.1 ℓ ∧
          GraphIso (T.1.induce {x : Fin n | x ≠ ℓ}) (Quotient.out u).1 then
        1 else 0)

/-- The basis action of grafting, retaining occurrence multiplicity. -/
def graftBasis (n : ℕ) (q : TreeClass n) : TreeSpace (n + 1) := by
  classical
  let T := Quotient.out q
  exact ∑ v : Fin n, ∑ u : TreeClass (n + 1),
    Finsupp.single u
      (if GraphIso (graftGraph T.1 v) (Quotient.out u).1 then 1 else 0)

def linearExtension {α β : Type*} [Fintype α] [AddCommGroup β] [Module ℚ β]
    (f : α → β) : (α →₀ ℚ) →ₗ[ℚ] β :=
  { toFun := fun x => ∑ a : α, (x a) • f a
    map_add' := by
      intro x y
      simp [Finsupp.add_apply, add_smul, Finset.sum_add_distrib]
    map_smul' := by
      intro c x
      simp [Finsupp.smul_apply, smul_eq_mul, smul_smul, Finset.smul_sum]
  }

def leafDeletion (n : ℕ) : TreeSpace n →ₗ[ℚ] TreeSpace (n - 1) :=
  linearExtension (leafDeletionBasis n)

def graft (n : ℕ) : TreeSpace n →ₗ[ℚ] TreeSpace (n + 1) :=
  linearExtension (graftBasis n)

def transportTreeSpace {a b : ℕ} (h : a = b) : TreeSpace a →ₗ[ℚ] TreeSpace b := by
  subst h
  exact LinearMap.id

/-- The `G L` operator in a positive top degree. -/
def glOperator (n : ℕ) (hn : 0 < n) : TreeSpace n →ₗ[ℚ] TreeSpace n :=
  (transportTreeSpace (Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr (Nat.ne_of_gt hn)))).comp
    ((graft (n - 1)).comp (leafDeletion n))

def graftPow : (m k : ℕ) → TreeSpace m →ₗ[ℚ] TreeSpace (m + k)
  | m, 0 => LinearMap.id
  | m, k + 1 => (graft (m + k)).comp (graftPow m k)

def tower (n k : ℕ) (hkn : k ≤ n) : Submodule ℚ (TreeSpace n) :=
  Submodule.map
    ((transportTreeSpace (Nat.sub_add_cancel hkn)).comp (graftPow (n - k) k))
    (LinearMap.ker (leafDeletion (n - k)))

def spectralLabel (n k : ℕ) : ℚ :=
  ((k * (n - k) + Nat.choose k 2 : ℕ) : ℚ)

/-- At a fixed top degree, stable grafting towers are the labelled `GL` eigenspaces. -/
def towerSummandsAreGLEigenspaces : Prop :=
  ∀ (n k : ℕ) (hTop : 2 ≤ n) (hDepth : k ≤ n) (hBottom : 2 ≤ n - k),
    tower n k hDepth =
        Module.End.eigenspace (glOperator n (by omega)) (spectralLabel n k) ∧
      ∀ (j : ℕ), j ≤ n → 2 ≤ n - j → k ≠ j →
        spectralLabel n k ≠ spectralLabel n j

end
end MathlibPlus.Open.TreeSpectral
