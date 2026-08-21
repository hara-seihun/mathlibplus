-- UNVERIFIED (native-decide): submitted but not kernel-verified, so it is not built and MathlibPlus.lean does not import it. See unverified.txt.
import Mathlib

open scoped BigOperators

namespace MathlibPlus.Open.OrderSevenScalarKernel

abbrev Vertex := Fin 7

abbrev Edge := {p : Vertex × Vertex // p.1 < p.2}

namespace Edge

def left (e : Edge) : Vertex := e.1.1

def right (e : Edge) : Vertex := e.1.2

end Edge

/-- The edge joining the two displayed natural-number vertices. -/
def edgeN (a b : Nat) (hab : a < b) (hb : b < 7) : Edge :=
  ⟨(⟨a, Nat.lt_trans hab hb⟩, ⟨b, hb⟩), by simpa using hab⟩

def adjacent (E : Finset Edge) (u v : Vertex) : Prop :=
  ∃ e ∈ E, (e.left = u ∧ e.right = v) ∨ (e.left = v ∧ e.right = u)

/-- A finite simple graph on seven vertices is connected when every proper
nonempty vertex cut is crossed by an edge. -/
def connected (E : Finset Edge) : Prop :=
  ∀ S : Finset Vertex, S.Nonempty → S ≠ Finset.univ →
    ∃ e ∈ E,
      (e.left ∈ S ∧ e.right ∉ S) ∨ (e.right ∈ S ∧ e.left ∉ S)

instance connectedDecidable (E : Finset Edge) : Decidable (connected E) := by
  unfold connected
  infer_instance

def isTree (E : Finset Edge) : Prop :=
  E.card = 6 ∧ connected E

instance isTreeDecidable (E : Finset Edge) : Decidable (isTree E) := by
  unfold isTree
  infer_instance

abbrev Tree7 := {E : Finset Edge // isTree E}

def treeIsomorphic (T U : Tree7) : Prop :=
  ∃ e : Vertex ≃ Vertex, ∀ u v : Vertex,
    adjacent T.1 u v ↔ adjacent U.1 (e u) (e v)

def treeSetoid : Setoid Tree7 where
  r := treeIsomorphic
  iseqv := by
    constructor
    · intro T
      exact ⟨Equiv.refl _, by simp⟩
    · rintro T U ⟨e, h⟩
      refine ⟨e.symm, ?_⟩
      intro u v
      simpa using (h (e.symm u) (e.symm v)).symm
    · rintro T U V ⟨e, h⟩ ⟨f, k⟩
      refine ⟨e.trans f, ?_⟩
      intro u v
      simpa only [Equiv.trans_apply] using
        (h u v).trans (k (e u) (e v))

instance : Setoid Tree7 := treeSetoid

abbrev TreeClass7 := Quotient (inferInstance : Setoid Tree7)

noncomputable instance : Fintype TreeClass7 := Fintype.ofFinite TreeClass7

def classOf (T : Tree7) : TreeClass7 := Quotient.mk' T

abbrev IntegerPartition7 :=
  {p : Fin 7 → Fin 8 // ∑ i : Fin 7, (i.val + 1) * (p i).val = 7}

abbrev VertexPartition := Finset (Finset Vertex)

def isVertexPartition (P : VertexPartition) : Prop :=
  (∀ B ∈ P, B.Nonempty) ∧
  (∀ B ∈ P, ∀ C ∈ P, B ≠ C → Disjoint B C) ∧
  (∀ v : Vertex, ∃ B ∈ P, v ∈ B)

/-- The induced selected-edge graph on a block is connected, expressed by
its finite cut condition. -/
def connectedWithin (S : Finset Edge) (B : Finset Vertex) : Prop :=
  ∀ A : Finset Vertex, A ⊆ B → A.Nonempty → A ≠ B →
    ∃ e ∈ S,
      (e.left ∈ A ∧ e.right ∈ B ∧ e.right ∉ A) ∨
      (e.right ∈ A ∧ e.left ∈ B ∧ e.left ∉ A)

def isComponentPartition (S : Finset Edge) (P : VertexPartition) : Prop :=
  isVertexPartition P ∧
  (∀ B ∈ P, connectedWithin S B) ∧
  (∀ e ∈ S, ∃ B ∈ P, e.left ∈ B ∧ e.right ∈ B)

def hasComponentOrders (S : Finset Edge) (part : IntegerPartition7) : Prop :=
  ∃ P : VertexPartition, isComponentPartition S P ∧
    ∀ i : Fin 7,
      (P.filter (fun B => B.card = i.val + 1)).card = (part.1 i).val

noncomputable def coefficient (E : Finset Edge) (part : IntegerPartition7) : ℤ := by
  classical
  exact ((Finset.univ.filter
    (fun S : Finset Edge => S ⊆ E ∧ hasComponentOrders S part)).card : ℤ)

noncomputable def U (T : Tree7) : IntegerPartition7 → ℤ :=
  coefficient T.1

/-- The coefficient vector on an isomorphism class, evaluated on a chosen
quotient representative; the coefficient construction is invariant under
isomorphism. -/
noncomputable def UClass (X : TreeClass7) : IntegerPartition7 → ℤ :=
  U (Quotient.out X)

/-- The tree consisting of three paths from the common vertex 0.  For the
three displayed order-seven triples below, the branches use consecutive
vertices 1 through 6. -/
def pathEdge (offset length x y : Nat) : Prop :=
  (0 < length ∧ x = 0 ∧ y = offset + 1) ∨
    ∃ i : Fin (length - 1),
      x = offset + 1 + i.val ∧ y = offset + 2 + i.val

instance pathEdgeDecidable (offset length x y : Nat) : Decidable (pathEdge offset length x y) := by
  unfold pathEdge
  infer_instance

def spEdge (a b c x y : Nat) : Prop :=
  pathEdge 0 a x y ∨ pathEdge a b x y ∨ pathEdge (a + b) c x y

instance spEdgeDecidable (a b c x y : Nat) : Decidable (spEdge a b c x y) := by
  unfold spEdge
  infer_instance

def Sp (a b c : Nat) : Finset Edge :=
  Finset.univ.filter (fun e => spEdge a b c e.left.val e.right.val)

def Sp411 : Tree7 :=
  ⟨Sp 4 1 1, by native_decide⟩

def Sp222 : Tree7 :=
  ⟨Sp 2 2 2, by native_decide⟩

def Sp321 : Tree7 :=
  ⟨Sp 3 2 1, by native_decide⟩

def AEdges : Finset Edge :=
  {edgeN 0 1 (by decide) (by decide),
   edgeN 0 2 (by decide) (by decide),
   edgeN 0 3 (by decide) (by decide),
   edgeN 0 4 (by decide) (by decide),
   edgeN 1 5 (by decide) (by decide),
   edgeN 2 6 (by decide) (by decide)}

def BEdges : Finset Edge :=
  {edgeN 0 1 (by decide) (by decide),
   edgeN 0 3 (by decide) (by decide),
   edgeN 0 4 (by decide) (by decide),
   edgeN 1 2 (by decide) (by decide),
   edgeN 2 5 (by decide) (by decide),
   edgeN 2 6 (by decide) (by decide)}

def CEdges : Finset Edge :=
  {edgeN 0 1 (by decide) (by decide),
   edgeN 0 3 (by decide) (by decide),
   edgeN 0 4 (by decide) (by decide),
   edgeN 0 5 (by decide) (by decide),
   edgeN 1 2 (by decide) (by decide),
   edgeN 2 6 (by decide) (by decide)}

def DEdges : Finset Edge :=
  {edgeN 0 1 (by decide) (by decide),
   edgeN 0 3 (by decide) (by decide),
   edgeN 0 4 (by decide) (by decide),
   edgeN 1 2 (by decide) (by decide),
   edgeN 1 5 (by decide) (by decide),
   edgeN 2 6 (by decide) (by decide)}

def A : Tree7 := ⟨AEdges, by native_decide⟩
def B : Tree7 := ⟨BEdges, by native_decide⟩
def C : Tree7 := ⟨CEdges, by native_decide⟩
def D : Tree7 := ⟨DEdges, by native_decide⟩

noncomputable def rSp : TreeClass7 → ℤ := by
  classical
  exact fun X =>
    (if X = classOf Sp411 then 1 else 0) +
    (if X = classOf Sp222 then 1 else 0) -
    2 * (if X = classOf Sp321 then 1 else 0)

noncomputable def rABCD : TreeClass7 → ℤ := by
  classical
  exact fun X =>
    (if X = classOf A then 1 else 0) +
    (if X = classOf B then 1 else 0) -
    (if X = classOf C then 1 else 0) -
    (if X = classOf D then 1 else 0)

noncomputable def identityMap :
    (TreeClass7 → ℤ) →ₗ[ℤ] (IntegerPartition7 → ℤ) :=
  { toFun := fun z => ∑ X, z X • UClass X
    map_add' := by
      intro z w
      ext part
      simp [Finset.sum_add_distrib, add_smul]
    map_smul' := by
      intro a z
      ext part
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
      simpa [mul_assoc] using
        (Finset.mul_sum (s := Finset.univ)
          (f := fun x => z x * UClass x part) a).symm }

noncomputable def identityModule : Submodule ℤ (TreeClass7 → ℤ) :=
  LinearMap.ker identityMap

noncomputable def basisVectors : Fin 2 → TreeClass7 → ℤ := ![rSp, rABCD]

def hasDisplayedBasis : Prop :=
  ∃ b : Module.Basis (Fin 2) ℤ identityModule,
    ∀ i : Fin 2,
      ((b i : identityModule) : TreeClass7 → ℤ) = basisVectors i

def uInvariant : Prop :=
  ∀ T₁ T₂ : Tree7, treeIsomorphic T₁ T₂ → U T₁ = U T₂

def claim59637 : Prop :=
  Fintype.card TreeClass7 = 11 ∧
  uInvariant ∧
  Function.Injective UClass ∧
  Module.Free ℤ identityModule ∧
  hasDisplayedBasis

end MathlibPlus.Open.OrderSevenScalarKernel
