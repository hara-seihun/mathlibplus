import Mathlib

namespace MathlibPlus.Open.Cayley

/-- A connection set is inverse-closed when it contains the additive inverse of
    each of its elements. -/
def inverseClosed {G : Type*} [AddGroup G] (S : Set G) : Prop :=
  ∀ ⦃x : G⦄, x ∈ S → -x ∈ S

/-- An abstract isomorphism between simple graphs. -/
def graphIsomorphism {V W : Type*} (G : SimpleGraph V) (H : SimpleGraph W) : Prop :=
  ∃ e : V ≃ W, ∀ x y, G.Adj x y ↔ H.Adj (e x) (e y)

/-- The simple Cayley graph of an inverse-closed additive connection set. -/
def cayleyGraph {G : Type*} [AddGroup G] (S : Set G)
    (hS : inverseClosed S) : SimpleGraph G where
  Adj x y := x ≠ y ∧ y - x ∈ S
  symm := ⟨by
    intro x y h
    refine ⟨Ne.symm h.1, ?_⟩
    simpa [sub_eq_add_neg, add_comm] using hS h.2
  ⟩
  loopless := ⟨by
    intro x h
    exact h.1 rfl
  ⟩

abbrev C2Pow (r : ℕ) := Fin r → ZMod 2
abbrev C2PowTimesC9 (r : ℕ) := C2Pow r × ZMod 9

def C9Subgroup (r : ℕ) : Set (C2PowTimesC9 r) :=
  {g | g.1 = 0}

/-- Every inverse-closed Cayley graph containing the full complement of
    `{0} × C₉` is an ordinary undirected CI-graph. -/
def c2PowTimesC9_undirectedCI : Prop :=
  ∀ (r : ℕ) (S : Set (C2PowTimesC9 r)),
    S ⊆ ({0} : Set (C2PowTimesC9 r))ᶜ →
    ∀ (hS : inverseClosed S),
      (Set.univ \ C9Subgroup r) ⊆ S →
      ∀ (T : Set (C2PowTimesC9 r)),
        T ⊆ ({0} : Set (C2PowTimesC9 r))ᶜ →
        ∀ (hT : inverseClosed T),
          graphIsomorphism (cayleyGraph S hS) (cayleyGraph T hT) →
          ∃ α : C2PowTimesC9 r ≃+ C2PowTimesC9 r, Set.image α S = T

end MathlibPlus.Open.Cayley
