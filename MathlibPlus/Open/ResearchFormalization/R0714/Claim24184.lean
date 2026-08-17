import Mathlib
import MathlibPlus.Combinatorics.Claim44521

namespace MathlibPlus.Open.ResearchFormalization.R0714

noncomputable section

abbrev GraphType (n : ℕ) :=
  MathlibPlus.Combinatorics.Claim44521.finiteSimpleGraphType n

noncomputable def graphTypeOf {n : ℕ} (G : SimpleGraph (Fin n)) : GraphType n :=
  MathlibPlus.Combinatorics.Claim44521.graphTypeOf n G

noncomputable def graphRepresentative {n : ℕ} (F : GraphType n) :
    SimpleGraph (Fin n) :=
  Quotient.out F

def graphIso {V W : Type*} (G : SimpleGraph V) (H : SimpleGraph W) : Prop :=
  Nonempty (G ≃g H)

def deleteVertex {n : ℕ} (G : SimpleGraph (Fin (n + 1)))
    (v : Fin (n + 1)) : SimpleGraph {x : Fin (n + 1) // x ≠ v} :=
  G.induce {x : Fin (n + 1) | x ≠ v}

def oneCard (n : ℕ) (F : GraphType n)
    (G : GraphType (n + 1)) : ℕ :=
  Nat.card {v : Fin (n + 1) //
    graphIso (deleteVertex (graphRepresentative G) v)
      (graphRepresentative F)}

noncomputable def twoCard (n : ℕ) (K : GraphType (n - 1))
    (G : GraphType (n + 1)) : ℕ :=
  Nat.card {S : Finset (Fin (n + 1)) //
    S.card = 2 ∧
      graphIso
        ((graphRepresentative G).induce
          {v : Fin (n + 1) | v ∉ S})
        (graphRepresentative K)}

noncomputable def extensionFiberSet (n : ℕ) (F : GraphType n) :
    Set (GraphType (n + 1)) :=
  {G | 0 < oneCard n F G}

abbrev ExtensionFiber (n : ℕ) (F : GraphType n) :=
  {G : GraphType (n + 1) // G ∈ extensionFiberSet n F}

noncomputable def mixedMatrix (n : ℕ) (F : GraphType n) :
    Matrix (GraphType (n - 1) × GraphType n) (ExtensionFiber n F) ℚ :=
  fun KP G =>
    (twoCard n KP.1 G.1 : ℚ) * (oneCard n KP.2 G.1 : ℚ)

def fullColumnRank {m k : Type*} [Fintype k]
    (M : Matrix m k ℚ) : Prop :=
  Matrix.rank M = Fintype.card k

noncomputable def edgePlusIsolatedGraph : SimpleGraph (Fin 3) :=
  SimpleGraph.fromRel (fun v w : Fin 3 =>
    (v = 0 ∧ w = 1) ∨ (v = 1 ∧ w = 0))

noncomputable def emptyTwo : GraphType 2 :=
  graphTypeOf ((⊤ : SimpleGraph (Fin 2))ᶜ)

noncomputable def completeTwo : GraphType 2 :=
  graphTypeOf (⊤ : SimpleGraph (Fin 2))

noncomputable def emptyThree : GraphType 3 :=
  graphTypeOf (⊥ : SimpleGraph (Fin 3))

noncomputable def edgePlusIsolatedThree : GraphType 3 :=
  graphTypeOf edgePlusIsolatedGraph

noncomputable def pathThree : GraphType 3 :=
  graphTypeOf (SimpleGraph.pathGraph 3)

noncomputable def singleton : GraphType 1 :=
  graphTypeOf (⊥ : SimpleGraph (Fin 1))

def orderTwoRows : Fin 2 → GraphType 1 × GraphType 2 :=
  ![(singleton, emptyTwo), (singleton, completeTwo)]

def edgelessColumns : Fin 3 → GraphType 3 :=
  ![emptyThree, edgePlusIsolatedThree, pathThree]

def edgelessMixedDisplay : Matrix (Fin 2) (Fin 3) ℚ :=
  !![9, 6, 3; 0, 3, 6]

def generatedKernel {k : Type*} [Fintype k]
    (M : Matrix (Fin 2) k ℚ) (v : k → ℚ) : Prop :=
  v ≠ 0 ∧ ∀ w, Matrix.mulVec M w = 0 ↔ ∃ c : ℚ, w = c • v

noncomputable def exactMixedDefect (F : GraphType 2)
    (columns : Fin 3 → GraphType 3)
    (display : Matrix (Fin 2) (Fin 3) ℚ) : Prop :=
  Function.Bijective orderTwoRows ∧
    ∃ h : ∀ j : Fin 3, columns j ∈ extensionFiberSet 2 F,
      Function.Bijective
          (fun j : Fin 3 =>
            (⟨columns j, h j⟩ : ExtensionFiber 2 F)) ∧
        (∀ i j,
          mixedMatrix 2 F (orderTwoRows i)
              (⟨columns j, h j⟩ : ExtensionFiber 2 F) = display i j) ∧
        Matrix.rank display = 2 ∧
        generatedKernel display (![1, -2, 1])

/-- Claim 24184: the mixed matrix on the actual edgeless `K̄₂` extension
fibre, with its three named graph-type columns, has the displayed rank defect. -/
def claim24184 : Prop :=
  letI : Fintype (ExtensionFiber 2 emptyTwo) := Fintype.ofFinite _
  exactMixedDefect emptyTwo edgelessColumns edgelessMixedDisplay

end
end MathlibPlus.Open.ResearchFormalization.R0714
