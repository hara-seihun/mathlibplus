import Mathlib

namespace MathlibPlus.Open.ResearchFormalization.R1250.Claim30597

abbrev C9 := ZMod 9

abbrev BinaryC9 (r : ℕ) := (Fin r → ZMod 2) × C9

/-- The pure base permutation `f(v,c)=(v,σ(c))`. -/
def pureBaseMap {V : Type*} (σ : Equiv.Perm C9) :
    V × C9 → V × C9 :=
  fun x => (x.1, σ x.2)

/-- The product relative derivative at `g=(w,t)`, after the elementary
abelian-two coordinate is cancelled. -/
def productRelativeDerivative {V : Type*}
    (σ : Equiv.Perm C9) (g x : V × C9) : V × C9 :=
  (x.1, σ.symm (σ (x.2 + g.2) - σ g.2))

/-- Inverse-closedness on an additive product. -/
def inverseClosed {V : Type*} [AddGroup V]
    (S : Set (V × C9)) : Prop :=
  ∀ ⦃x : V × C9⦄, x ∈ S → -x ∈ S

/-- Invariance under every normalized product relative derivative. -/
def derivativeInvariant {V : Type*}
    (σ : Equiv.Perm C9) (S : Set (V × C9)) : Prop :=
  ∀ g x : V × C9,
    x ∈ S ↔ productRelativeDerivative σ g x ∈ S

/-- Identity-free inverse-closed connection sets for the additive carrier. -/
def identityFreeInverseClosed {G : Type*} [AddGroup G]
    (S : Set G) : Prop :=
  (0 : G) ∉ S ∧ ∀ ⦃x : G⦄, x ∈ S → -x ∈ S

/-- An ordinary undirected Cayley-isomorphism relation witnessed by the
specified pure base map. -/
def pureBaseGraphWitness {V : Type*} [AddCommGroup V]
    (σ : Equiv.Perm C9) (S : Set (V × C9)) : Prop :=
  ∀ x y : V × C9,
    (x ≠ y ∧ y - x ∈ S) ↔
      (pureBaseMap σ x ≠ pureBaseMap σ y ∧
        pureBaseMap σ y - pureBaseMap σ x ∈ pureBaseMap σ '' S)

/-- A pure normalized base-permutation witness to failure of ordinary
undirected CI on `C₂^r × C₉`. -/
def pureNormalizedOrdinaryCIFailure (r : ℕ) : Prop :=
  ∃ (σ : Equiv.Perm C9) (S : Set (BinaryC9 r)),
    σ 0 = 0 ∧
      identityFreeInverseClosed S ∧
        identityFreeInverseClosed (pureBaseMap σ '' S) ∧
          pureBaseGraphWitness σ S ∧
            ¬ ∃ α : BinaryC9 r ≃+ BinaryC9 r,
              Set.image α S = pureBaseMap σ '' S

/-- Claim 30597: for every finite elementary abelian `2`-group factor, a
normalized pure `C₉`-base permutation satisfying the stated inverse and
relative-derivative conditions has one common unit multiplier shadow; hence
it cannot be an ordinary undirected CI failure witness at any rank. -/
def claim30597 : Prop :=
  (∀ (V : Type*) [Fintype V] [AddCommGroup V]
      (hV : ∀ v : V, v + v = 0)
      (σ : Equiv.Perm C9),
      σ 0 = 0 →
        ∀ S : Set (V × C9),
          inverseClosed S →
            derivativeInvariant σ S →
              inverseClosed (pureBaseMap σ '' S) →
                ∃ u : C9ˣ,
                  pureBaseMap σ '' S =
                    Set.image
                      (fun x => (x.1, (u : C9) * x.2)) S) ∧
    ∀ r : ℕ, ¬ pureNormalizedOrdinaryCIFailure r

end MathlibPlus.Open.ResearchFormalization.R1250.Claim30597
