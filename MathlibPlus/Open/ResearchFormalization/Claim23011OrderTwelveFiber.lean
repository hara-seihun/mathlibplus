import Mathlib

open Classical

namespace MathlibPlus.Open.ResearchFormalization.Claim23011

noncomputable section

abbrev DihedralTwelve := ZMod 6 × ZMod 2

def dihedralTwelveMul (u v : DihedralTwelve) : DihedralTwelve :=
  (u.1 + (if u.2 = 0 then v.1 else -v.1), u.2 + v.2)

def dihedralTwelveIdentity : DihedralTwelve := (0, 0)

def degreeFiveConnection (s : DihedralTwelve) : Prop :=
  s = (0, 1) ∨
    s = (1, 0) ∨
    s = (1, 1) ∨
    s = (3, 1) ∨
    s = (5, 0)

def dihedralTwelveWitness : SimpleGraph DihedralTwelve :=
  SimpleGraph.fromRel (fun u v =>
    ∃ s, degreeFiveConnection s ∧ dihedralTwelveMul u s = v)

def deletedGraph {V : Type*} (G : SimpleGraph V) (v : V) :
    SimpleGraph {u // u ≠ v} :=
  G.comap Subtype.val

def extensionGraph {V : Type*} (G : SimpleGraph V) (mask : V → Bool) :
    SimpleGraph (V ⊕ Fin 1) :=
  SimpleGraph.fromRel (fun u v =>
    match u, v with
    | Sum.inl a, Sum.inl b => G.Adj a b
    | Sum.inl a, Sum.inr _ => mask a = true
    | Sum.inr _, Sum.inl a => mask a = true
    | Sum.inr _, Sum.inr _ => False)

def extensionIndex {V : Type*} [Fintype V] (mask : V → Bool) :
    Fin (Fintype.card (V → Bool)) :=
  Fintype.equivFin (V → Bool) mask

def extensionEquivalent {V : Type*} [Fintype V]
    (G : SimpleGraph V) (left right : V → Bool) : Prop :=
  Nonempty (extensionGraph G left ≃g extensionGraph G right)

def canonicalExtensionMask {V : Type*} [Fintype V]
    (G : SimpleGraph V) (mask : V → Bool) : Prop :=
  ∀ other : V → Bool,
    extensionIndex other < extensionIndex mask →
      ¬ extensionEquivalent G other mask

noncomputable def extensionFiberCount {V : Type*} [Fintype V]
    (G : SimpleGraph V) : ℕ :=
  Nat.card {mask : V → Bool // canonicalExtensionMask G mask}

def cycleSquareTwelve : SimpleGraph (Fin 12) :=
  SimpleGraph.fromRel (fun u v =>
    (u.val + 1) % 12 = v.val ∨ (u.val + 2) % 12 = v.val)

def graphAutomorphism {V : Type*} (G : SimpleGraph V)
    (f : Equiv.Perm V) : Prop :=
  ∀ u v, G.Adj (f u) (f v) ↔ G.Adj u v

def asymmetricGraph {V : Type*} (G : SimpleGraph V) : Prop :=
  ¬ ∃ f : Equiv.Perm V,
    f ≠ Equiv.refl V ∧ graphAutomorphism G f

def vertexTransitiveGraph {V : Type*} (G : SimpleGraph V) : Prop :=
  ∀ u v : V, ∃ f : Equiv.Perm V,
    graphAutomorphism G f ∧ f u = v

def orderTwelveDih12ExtensionFiberFalsifier : Prop :=
  vertexTransitiveGraph dihedralTwelveWitness ∧
    asymmetricGraph (deletedGraph dihedralTwelveWitness dihedralTwelveIdentity) ∧
    extensionFiberCount
        (deletedGraph dihedralTwelveWitness dihedralTwelveIdentity) = 2046 ∧
    extensionFiberCount
        (deletedGraph cycleSquareTwelve (0 : Fin 12)) ≤ 1056 ∧
    (2046 : ℕ) > 1056

end

end MathlibPlus.Open.ResearchFormalization.Claim23011
