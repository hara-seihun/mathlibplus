import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card

namespace MathlibPlus.Open.Combinatorics

/-- The majority-density statement for minimal nonempty members from claim 47033.
A minimal member is minimal among the nonempty members of the finite family under
inclusion.  Half-frequency is expressed without division by
`2 * frequency ≥ family.card`. -/
def minimalMemberMajorityDensity_claim47033 : Prop :=
  ∀ (q : ℕ) (C : Finset ℕ) (𝓕 : Finset (Finset ℕ)),
    1 ≤ q →
    C.card = 2 * q - 1 →
    (∀ s ∈ 𝓕, ∀ t ∈ 𝓕, s ∪ t ∈ 𝓕) →
    (∀ M ∈ 𝓕, M.Nonempty →
      (∀ N ∈ 𝓕, N.Nonempty → N ⊆ M → N = M) →
        q ≤ (M ∩ C).card) →
    ∃ c ∈ C, 2 * (𝓕.filter (fun s => c ∈ s)).card ≥ 𝓕.card

end MathlibPlus.Open.Combinatorics
