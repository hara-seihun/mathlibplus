import Mathlib

namespace MathlibPlus.Open.Research.FormalizationBatch.FiniteDihedralCayley91

noncomputable section

/-- The additive group of the two-dimensional vector space over `F₃`, viewed
multiplicatively so it can be the normal factor of a semidirect product. -/
abbrev F3Vector := Multiplicative (ZMod 3 × ZMod 3)

/-- A concrete copy of `C₂`. -/
inductive C2
  | e
  | s
  deriving DecidableEq

instance : Fintype C2 := ⟨{.e, .s}, by intro x; cases x <;> simp⟩

instance : Mul C2 where
  mul
    | .e, b => b
    | .s, .e => .s
    | .s, .s => .e

instance : One C2 := ⟨.e⟩

instance : Inv C2 where
  inv
    | .e => .e
    | .s => .s

instance : Group C2 where
  mul_assoc a b c := by cases a <;> cases b <;> cases c <;> rfl
  one_mul a := by cases a <;> rfl
  mul_one a := by cases a <;> rfl
  inv_mul_cancel a := by cases a <;> rfl

/-- The inversion automorphism of `F₃²`. -/
def inversionAut : MulAut F3Vector :=
  AddEquiv.toMultiplicative (AddEquiv.neg (ZMod 3 × ZMod 3))

lemma inversionAut_sq : inversionAut * inversionAut = 1 := by
  ext x <;> simp [inversionAut]

/-- The `C₂` action on `F₃²` by identity and inversion. -/
def inversionAction : C2 →* MulAut F3Vector where
  toFun
    | .e => 1
    | .s => inversionAut
  map_one' := rfl
  map_mul' := by
    intro a b
    cases a <;> cases b <;> simp [inversionAut_sq]

/-- `F₃² ⋊ C₂` with the inversion action. -/
abbrev R := F3Vector ⋊[inversionAction] C2

/-- Inverse-closed connection sets not containing the identity. -/
def InverseClosed (S : Finset R) : Prop :=
  ∀ x, x ∈ S → x⁻¹ ∈ S

def ConnectionSet := {S : Finset R // 1 ∉ S ∧ InverseClosed S}

/-- The Cayley graph with right differences in the connection set. -/
def cayleyGraph (S : ConnectionSet) : SimpleGraph R where
  Adj x y := x ≠ y ∧ x⁻¹ * y ∈ S.1
  symm := ⟨by
    intro x y h
    refine ⟨Ne.symm h.1, ?_⟩
    simpa using S.2.2 (x⁻¹ * y) h.2⟩
  loopless := ⟨by
    intro x h
    exact h.1 rfl⟩

/-- The valency of a Cayley graph, measured at the identity. -/
def valency (S : ConnectionSet) : Nat :=
  Nat.card {y : R // (cayleyGraph S).Adj (1 : R) y}

def ConnectedConnectionSet :=
  {S : ConnectionSet // (cayleyGraph S).Connected}

/-- Isomorphism of the simple graphs associated to two connection sets. -/
def GraphIsomorphic (S T : ConnectionSet) : Prop :=
  ∃ e : R ≃ R,
    ∀ x y, (cayleyGraph S).Adj x y ↔ (cayleyGraph T).Adj (e x) (e y)

def connectedGraphSetoid : Setoid ConnectedConnectionSet where
  r S T := GraphIsomorphic S.1 T.1
  iseqv := by
    constructor
    · intro S
      exact ⟨Equiv.refl R, by simp⟩
    · intro S T h
      rcases h with ⟨e, he⟩
      refine ⟨e.symm, ?_⟩
      intro x y
      simpa using (he (e.symm x) (e.symm y)).symm
    · intro S T U hST hTU
      rcases hST with ⟨e, he⟩
      rcases hTU with ⟨f, hf⟩
      refine ⟨e.trans f, ?_⟩
      intro x y
      simpa [Equiv.trans_apply] using (he x y).trans (hf (e x) (e y))

abbrev ConnectedGraphClass := Quotient connectedGraphSetoid

def ValencyConnectionSet (k : Nat) :=
  {S : ConnectedConnectionSet // valency S.1 = k}

def valencyGraphSetoid (k : Nat) : Setoid (ValencyConnectionSet k) where
  r S T := GraphIsomorphic S.1.1 T.1.1
  iseqv := by
    constructor
    · intro S
      exact ⟨Equiv.refl R, by simp⟩
    · intro S T h
      rcases h with ⟨e, he⟩
      refine ⟨e.symm, ?_⟩
      intro x y
      simpa using (he (e.symm x) (e.symm y)).symm
    · intro S T U hST hTU
      rcases hST with ⟨e, he⟩
      rcases hTU with ⟨f, hf⟩
      refine ⟨e.trans f, ?_⟩
      intro x y
      simpa [Equiv.trans_apply] using (he x y).trans (hf (e x) (e y))

abbrev ValencyGraphClass (k : Nat) := Quotient (valencyGraphSetoid k)

/-- The action of a group automorphism on a connection set. -/
def mapConnection (α : MulAut R) (S : ConnectionSet) : ConnectionSet :=
  ⟨S.1.image α, by
    constructor
    · intro h
      rcases Finset.mem_image.mp h with ⟨x, hx, hα⟩
      have hx1 : x = 1 := by
        apply α.injective
        simpa using hα
      exact S.2.1 (hx1 ▸ hx)
    · intro x hx
      rcases Finset.mem_image.mp hx with ⟨y, hy, rfl⟩
      exact Finset.mem_image.mpr ⟨y⁻¹, S.2.2 y hy, by simp⟩⟩

def AutOrbit (S T : ConnectionSet) : Prop :=
  ∃ α : MulAut R, mapConnection α S = T

/-- The connection-set fiber over a connected unlabeled graph. -/
def ConnectedFiber (S : ConnectedConnectionSet) :=
  {T : ConnectedConnectionSet // GraphIsomorphic T.1 S.1}

def connectedFiberSize (S : ConnectedConnectionSet) : Nat :=
  Nat.card (ConnectedFiber S)

def FiberSizeConnectionSet (m : Nat) :=
  {S : ConnectedConnectionSet // connectedFiberSize S = m}

def fiberSizeGraphSetoid (m : Nat) : Setoid (FiberSizeConnectionSet m) where
  r S T := GraphIsomorphic S.1.1 T.1.1
  iseqv := by
    constructor
    · intro S
      exact ⟨Equiv.refl R, by simp⟩
    · intro S T h
      rcases h with ⟨e, he⟩
      refine ⟨e.symm, ?_⟩
      intro x y
      simpa using (he (e.symm x) (e.symm y)).symm
    · intro S T U hST hTU
      rcases hST with ⟨e, he⟩
      rcases hTU with ⟨f, hf⟩
      refine ⟨e.trans f, ?_⟩
      intro x y
      simpa [Equiv.trans_apply] using (he x y).trans (hf (e x) (e y))

abbrev FiberSizeGraphClass (m : Nat) := Quotient (fiberSizeGraphSetoid m)

def fiberSizeSupport : Finset Nat :=
  {1, 4, 6, 9, 12, 36, 54, 72, 108, 216}

/-- Exact admitted claim: the connected Cayley-graph census and its
connection-set fibers for `F₃² ⋊ C₂`. -/
def finiteDihedralCayley91 : Prop :=
  Nat.card ConnectionSet = 8192 ∧
  Nat.card ConnectedGraphClass = 91 ∧
  Nat.card (ValencyGraphClass 0) = 0 ∧
  Nat.card (ValencyGraphClass 1) = 0 ∧
  Nat.card (ValencyGraphClass 2) = 0 ∧
  Nat.card (ValencyGraphClass 3) = 1 ∧
  Nat.card (ValencyGraphClass 4) = 3 ∧
  Nat.card (ValencyGraphClass 5) = 6 ∧
  Nat.card (ValencyGraphClass 6) = 8 ∧
  Nat.card (ValencyGraphClass 7) = 10 ∧
  Nat.card (ValencyGraphClass 8) = 12 ∧
  Nat.card (ValencyGraphClass 9) = 13 ∧
  Nat.card (ValencyGraphClass 10) = 10 ∧
  Nat.card (ValencyGraphClass 11) = 9 ∧
  Nat.card (ValencyGraphClass 12) = 7 ∧
  Nat.card (ValencyGraphClass 13) = 5 ∧
  Nat.card (ValencyGraphClass 14) = 3 ∧
  Nat.card (ValencyGraphClass 15) = 2 ∧
  Nat.card (ValencyGraphClass 16) = 1 ∧
  Nat.card (ValencyGraphClass 17) = 1 ∧
  (∀ k : Nat, 17 < k → Nat.card (ValencyGraphClass k) = 0) ∧
  Nat.card ConnectedConnectionSet = 8035 ∧
  (∀ S T : ConnectionSet, GraphIsomorphic S T ↔ AutOrbit S T) ∧
  (∀ m : Nat, m ∉ fiberSizeSupport → Nat.card (FiberSizeGraphClass m) = 0) ∧
  Nat.card (FiberSizeGraphClass 1) = 2 ∧
  Nat.card (FiberSizeGraphClass 4) = 2 ∧
  Nat.card (FiberSizeGraphClass 6) = 1 ∧
  Nat.card (FiberSizeGraphClass 9) = 3 ∧
  Nat.card (FiberSizeGraphClass 12) = 6 ∧
  Nat.card (FiberSizeGraphClass 36) = 17 ∧
  Nat.card (FiberSizeGraphClass 54) = 10 ∧
  Nat.card (FiberSizeGraphClass 72) = 16 ∧
  Nat.card (FiberSizeGraphClass 108) = 16 ∧
  Nat.card (FiberSizeGraphClass 216) = 18

end

end MathlibPlus.Open.Research.FormalizationBatch.FiniteDihedralCayley91
