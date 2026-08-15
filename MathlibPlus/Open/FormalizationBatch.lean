import Mathlib

open scoped BigOperators

namespace MathlibPlus.Open.FormalizationBatch

/-! The finite endpoint convention used below indexes an `n + 1` by `Fin (n + 1)`.
    The final coordinate is `Fin.last n`, and `reverseIndex n r` is its `r`th
    coordinate when read from the endpoint backwards. -/

def reverseIndex (n : ℕ) (r : Fin (n + 1)) : Fin (n + 1) :=
  ⟨n - r.1, Nat.lt_succ_of_le (Nat.sub_le n r.1)⟩

def IsFiniteIrreducibleJacobi
    (n : ℕ) (J : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) : Prop :=
  (∀ i j, J i j = J j i) ∧
    (∀ i j, 1 < Nat.dist i.1 j.1 → J i j = 0) ∧
      (∀ i : Fin n, 0 < J i.castSucc i.succ)

def finiteSupportEndpointChristoffelReciprocity : Prop :=
  ∀ (n : ℕ) (J : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ),
    IsFiniteIrreducibleJacobi n J →
      ∀ (x : ℝ) (v : Fin (n + 1) → ℝ),
        J.mulVec v = x • v →
          (∑ k : Fin (n + 1), v k ^ 2) = 1 →
            let endpoint : Fin (n + 1) := Fin.last n
            let ν := |v endpoint| ^ 2
            let ψ : Fin (n + 1) → ℝ :=
              fun r => v (reverseIndex n r) / v endpoint
            let K := ∑ r : Fin (n + 1), ψ r ^ 2
            ν * K = 1

/-! A simple labeled graph on a finite vertex type is its Boolean adjacency bit
    on each two-element subset. -/

def Edge (V : Type*) [DecidableEq V] := {e : Finset V // e.card = 2}

def edgeImage {V : Type*} [DecidableEq V]
    (σ : Equiv.Perm V) (e : Edge V) : Edge V :=
  ⟨e.1.map σ.toEmbedding, by simpa using e.2⟩

def PointedLocalPermutations (V : Type*) [DecidableEq V] :=
  {π : V → Equiv.Perm V // ∀ i : V, π i i = i}

def GammaVertex (V : Type*) [DecidableEq V] := Sum (Edge V) (Edge V)

def ConstraintIndex (V : Type*) [DecidableEq V] :=
  Σ i : V, {e : Edge V // i ∉ e.1}

def gammaLeft {V : Type*} [DecidableEq V]
    (q : ConstraintIndex V) : GammaVertex V :=
  Sum.inl q.2.1

def gammaRight {V : Type*} [DecidableEq V]
    (π : PointedLocalPermutations V) (q : ConstraintIndex V) : GammaVertex V :=
  Sum.inr (edgeImage (π.1 q.1) q.2.1)

def GammaAdjacent {V : Type*} [DecidableEq V]
    (π : PointedLocalPermutations V) (u v : GammaVertex V) : Prop :=
  ∃ q : ConstraintIndex V,
    (u = gammaLeft q ∧ v = gammaRight π q) ∨
      (u = gammaRight π q ∧ v = gammaLeft q)

def GammaConnected {V : Type*} [DecidableEq V]
    (π : PointedLocalPermutations V) (u v : GammaVertex V) : Prop :=
  Relation.ReflTransGen (GammaAdjacent π) u v

def IsGammaComponentColoring {V : Type*} [DecidableEq V]
    (π : PointedLocalPermutations V) (c : GammaVertex V → Bool) : Prop :=
  ∀ u v, GammaConnected π u v → c u = c v

def SimpleLabeledGraph (V : Type*) [DecidableEq V] := Edge V → Bool

def RealizesPrescribedCardIsomorphisms {V : Type*} [DecidableEq V]
    (π : PointedLocalPermutations V)
    (A B : SimpleLabeledGraph V) : Prop :=
  ∀ (i : V) (e : Edge V), i ∉ e.1 → A e = B (edgeImage (π.1 i) e)

def componentColoringProjection {V : Type*} [DecidableEq V]
    (π : PointedLocalPermutations V) (c : GammaVertex V → Bool) :
    SimpleLabeledGraph V × SimpleLabeledGraph V :=
  (fun e => c (Sum.inl e), fun e => c (Sum.inr e))

def compatibleGraphPairsAreExactlyComponentColorings : Prop :=
  ∀ (V : Type*) [Fintype V] [DecidableEq V]
    (π : PointedLocalPermutations V),
    (∀ c : GammaVertex V → Bool,
        IsGammaComponentColoring π c →
          RealizesPrescribedCardIsomorphisms π
            (componentColoringProjection π c).1
            (componentColoringProjection π c).2) ∧
      Function.Injective
        (fun c : {c : GammaVertex V → Bool // IsGammaComponentColoring π c} =>
          componentColoringProjection π c.1) ∧
        (∀ p : SimpleLabeledGraph V × SimpleLabeledGraph V,
          RealizesPrescribedCardIsomorphisms π p.1 p.2 →
            ∃ c : GammaVertex V → Bool,
              IsGammaComponentColoring π c ∧
                componentColoringProjection π c = p)

end MathlibPlus.Open.FormalizationBatch
