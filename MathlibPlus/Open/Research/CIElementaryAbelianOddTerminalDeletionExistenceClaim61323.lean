import Mathlib

namespace MathlibPlus.Open.Research.CIElementaryAbelianOddTerminalDeletionExistenceClaim61323

noncomputable section

abbrev Fp (p : ℕ) := ZMod p
abbrev Vector (p r : ℕ) := Fin r → Fp p

/-- Identity-free connection sets on the additive elementary-abelian carrier. -/
def identityFree {p r : ℕ} (S : Set (Vector p r)) : Prop :=
  (0 : Vector p r) ∉ S

/-- Inverse-closure for an ordinary undirected connection set. -/
def inverseClosed {p r : ℕ} (S : Set (Vector p r)) : Prop :=
  ∀ ⦃x : Vector p r⦄, x ∈ S → -x ∈ S

/-- The loopless additive Cayley adjacency relation. -/
def cayleyAdjacent {p r : ℕ} (S : Set (Vector p r))
    (x y : Vector p r) : Prop :=
  x ≠ y ∧ y - x ∈ S

/-- An arbitrary vertex permutation carrying one ordinary Cayley graph to another. -/
def cayleyGraphIsomorphism {p r : ℕ}
    (S T : Set (Vector p r)) : Prop :=
  ∃ f : Vector p r → Vector p r,
    Function.Bijective f ∧
      ∀ x y,
        cayleyAdjacent S x y ↔
          cayleyAdjacent T (f x) (f y)

/-- Connectedness of an ordinary Cayley graph. -/
def connectedCayley {p r : ℕ} (S : Set (Vector p r)) : Prop :=
  ∀ x y : Vector p r,
    Relation.ReflTransGen (cayleyAdjacent S) x y

/-- Pointed oddness of a permutation of the additive carrier. -/
def oddPermutation {p r : ℕ} (q : Vector p r → Vector p r) : Prop :=
  q 0 = 0 ∧
    Function.Bijective q ∧
      ∀ x : Vector p r, q (-x) = -q x

/-- The pointed odd permutation is also the Cayley-graph isomorphism. -/
def pointedOddCayleyIsomorphism {p r : ℕ}
    (q : Vector p r → Vector p r) (S T : Set (Vector p r)) : Prop :=
  oddPermutation q ∧
    ∀ x y,
      cayleyAdjacent S x y ↔
        cayleyAdjacent T (q x) (q y)

/-- The ordinary undirected Cayley-CI property of `C_p^r`. -/
def ordinaryUndirectedCI (p r : ℕ) : Prop :=
  ∀ S T : Set (Vector p r),
    identityFree S →
    inverseClosed S →
    identityFree T →
    inverseClosed T →
    cayleyGraphIsomorphism S T →
    ∃ e : Vector p r ≃+ Vector p r,
      Set.image (fun x => e x) S = T

/-- A pointed ordinary-undirected defect with the required group-automorphism
obstruction. -/
def ordinaryUndirectedCayleyCIDefect {p r : ℕ}
    (S T : Set (Vector p r)) (q : Vector p r → Vector p r) : Prop :=
  identityFree S ∧
    inverseClosed S ∧
      identityFree T ∧
        inverseClosed T ∧
          pointedOddCayleyIsomorphism q S T ∧
            ¬ ∃ e : Vector p r ≃+ Vector p r,
              Set.image (fun x => e x) S = T

/-- Claim 61323: for every prime `p >= 11`, the terminal deleted-ridge
construction gives a connected identity-free inverse-closed pointed odd
Cayley defect at rank `(p + 9) / 2`, and its padded witnesses give the same
ordinary-undirected non-CI conclusion at every larger rank. -/
def claim61323 : Prop :=
  ∀ p : ℕ, Nat.Prime p → 11 ≤ p →
    let r₀ : ℕ := (p + 9) / 2
    (¬ ordinaryUndirectedCI p r₀ ∧
      ∃ S₀ S₁ : Set (Vector p r₀),
        ∃ q : Vector p r₀ → Vector p r₀,
          connectedCayley S₀ ∧
            connectedCayley S₁ ∧
              ordinaryUndirectedCayleyCIDefect S₀ S₁ q) ∧
    ∀ r : ℕ, r₀ ≤ r →
      ¬ ordinaryUndirectedCI p r ∧
        ∃ S₀ S₁ : Set (Vector p r),
          ∃ q : Vector p r → Vector p r,
            connectedCayley S₀ ∧
              connectedCayley S₁ ∧
                ordinaryUndirectedCayleyCIDefect S₀ S₁ q

end

end MathlibPlus.Open.Research.CIElementaryAbelianOddTerminalDeletionExistenceClaim61323
