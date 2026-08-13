import MathlibPlus.GroupTheory.TwoClosure

namespace MathlibPlus.Open.GroupTheory

/--
Claim 31540.  Let `G` have a unique subgroup of prime order `p`.  If two
regular copies of `G` act on the same finite point set, the ambient subgroup's
preservation of the first copy's `U`-orbit relation forces the second copy's
`U`-orbit relation to coincide with it.

The displayed multiplicative equivalences are the source's explicit
identifications of the abstract `G` and its subgroup `U` with each regular
copy; in particular, the target copy's prime subgroup is not an extra
hypothesis.
-/
def invariantPrimeBlockAlignment_claim31540 : Prop :=
  ∀ (G : Type*) [Fintype G] [Group G]
    (Ω : Type*) [Fintype Ω] (p : ℕ)
    (U_G : Subgroup G),
    Nat.Prime p →
    Nat.card U_G = p →
    (∀ V : Subgroup G, Nat.card V = p → V = U_G) →
    ∀ (R K : Subgroup (Equiv.Perm Ω)) (e_R : G ≃* R),
      R ≤ K →
      (∀ x y : Ω, ∃! r : R, r.1 x = y) →
      (∀ k : K, ∀ x y : Ω,
        (∃ u : U_G, (e_R u).1.1 x = y) ↔
          (∃ u : U_G, (e_R u).1.1 (k.1 x) = k.1 y)) →
      ∀ (T : Subgroup (Equiv.Perm Ω)) (e_T : G ≃* T),
        T ≤ K →
        (∀ x y : Ω, ∃! t : T, t.1 x = y) →
        ∀ x y : Ω,
          (∃ u : U_G, (e_T u).1.1 x = y) ↔
            (∃ u : U_G, (e_R u).1.1 x = y)

end MathlibPlus.Open.GroupTheory
