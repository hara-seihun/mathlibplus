import Mathlib

namespace MathlibPlus.Open.ResearchFormalization.R0671

noncomputable def maximumIndex {q M : ℕ} (hq : 0 < q)
    (i : Fin q → Fin M) : Fin M :=
  letI : Nonempty (Fin q) := ⟨⟨0, hq⟩⟩
  Finset.max' (Finset.univ.image i) (Finset.univ_nonempty.image i)

def strictPrefix {q M : ℕ} {A : Type*} [AddCommMonoid A]
    (a : Fin q → Fin M → A) (j : Fin q) (n : Fin M) : A :=
  ∑ m ∈ Finset.univ.filter (fun m : Fin M => m < n), a j m

def inclusivePrefix {q M : ℕ} {A : Type*} [AddCommMonoid A]
    (a : Fin q → Fin M → A) (j : Fin q) (n : Fin M) : A :=
  ∑ m ∈ Finset.univ.filter (fun m : Fin M => m ≤ n), a j m

def claim26594 : Prop :=
  ∀ {𝕜 : Type*} [Field 𝕜] {A : Type*} [CommSemiring A]
    [Algebra 𝕜 A] [Algebra 𝕜 ℂ],
    ∀ (q M : ℕ), (hq : 0 < q) → (hM : 0 < M) →
    ∀ (a : Fin q → Fin M → A) (L : Fin M → (A →ₗ[𝕜] ℂ)),
      (∑ i : Fin q → Fin M,
          L (maximumIndex hq i) (∏ j, a j (i j))) =
        ∑ n : Fin M, ∑ j : Fin q,
          L n
            (a j n *
              (∏ k ∈ Finset.univ.filter (fun k : Fin q => k < j),
                strictPrefix a k n) *
              (∏ k ∈ Finset.univ.filter (fun k : Fin q => j < k),
                inclusivePrefix a k n))

end MathlibPlus.Open.ResearchFormalization.R0671
