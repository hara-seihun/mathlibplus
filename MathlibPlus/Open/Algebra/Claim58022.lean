import Mathlib

namespace MathlibPlus.Open.Algebra

/--
The mixed-difference fibre statement from admitted claim 58022.  The reduced
homogeneous decomposition is represented by its degree-one-through-degree-`p`
components indexed by `Fin p`; the index `m` has degree `m.val + 1`.  The
homogeneity equations and the exact decomposition are hypotheses, rather than
an implicit reconstruction of a polynomial-map API.
-/
def mixedDifferenceMiddleLayers_claim58022 : Prop :=
  ∀ (p : ℕ) [Fact p.Prime], 5 ≤ p →
    ∀ (A B : Type*)
      [AddCommGroup A] [AddCommGroup B]
      [Module (ZMod p) A] [Module (ZMod p) B]
      [FiniteDimensional (ZMod p) A] [FiniteDimensional (ZMod p) B],
    ∀ (F : B → A) (Fcomp : Fin p → B → A),
      F 0 = 0 →
      (∀ x, F x = ∑ m : Fin p, Fcomp m x) →
      (∀ (m : Fin p) (c : ZMod p) (x : B),
        Fcomp m (c • x) = c ^ (m.val + 1) • Fcomp m x) →
      (∀ (d : B) (m : Fin p),
        2 ≤ m.val + 1 → m.val + 1 ≤ p - 1 →
        Fcomp m d ∈
          Submodule.span (ZMod p)
            (Set.range (fun x : B => F (x + d) - F x - F d))) ∧
      (∀ d : B,
        F d -
            (Fcomp ⟨0, Nat.Prime.pos (Fact.out : Nat.Prime p)⟩ d +
              Fcomp ⟨p - 1,
                Nat.sub_lt (Nat.Prime.pos (Fact.out : Nat.Prime p)) (by decide)⟩ d) ∈
          Submodule.span (ZMod p)
            (Set.range (fun x : B => F (x + d) - F x - F d)))

end MathlibPlus.Open.Algebra
