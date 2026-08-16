import Mathlib

namespace MathlibPlus.Open.Combinatorics.Claim47032

/--
The exact incidence conclusion in admitted claim 47032. A finite family is
represented by a `Finset` of finite subsets; inclusion-minimality is written
out rather than imported from a separate family API.
-/
def minimalMajorityIncidence_claim47032 : Prop :=
  ∀ {α : Type*} [DecidableEq α]
    (𝓕 : Finset (Finset α)) (C : Finset α),
    C.Nonempty → C ⊆ 𝓕.biUnion (fun s => s) →
      (∀ ⦃A B : Finset α⦄, A ∈ 𝓕 → B ∈ 𝓕 → A ∪ B ∈ 𝓕) →
      (∀ M ∈ 𝓕, M.Nonempty →
        (∀ N ∈ 𝓕, N.Nonempty → N ⊆ M → M ⊆ N) →
          2 * (M ∩ C).card > C.card) →
      ∃ c ∈ C,
        2 * (𝓕.filter (fun M => c ∈ M)).card ≥ 𝓕.card

end MathlibPlus.Open.Combinatorics.Claim47032
