import Mathlib

namespace MathlibPlus.GraphTheory

/-- A red/blue complete-graph coloring on `Fin n` has a red edge or a blue
clique of size `t`.  The red graph is `G`, and its complement is blue. -/
def ramseyTwoProperty (t n : ℕ) : Prop :=
  ∀ G : SimpleGraph (Fin n), ¬ G.CliqueFree 2 ∨ ¬ Gᶜ.CliqueFree t

lemma ramseyTwoProperty_of_le {t n : ℕ} (h : t ≤ n) :
    ramseyTwoProperty t n := by
  intro G
  by_cases hG : G = ⊥
  · right
    rw [hG]
    simp only [compl_bot]
    apply SimpleGraph.IsContained.not_cliqueFree
    have f : Fin t ↪ Fin n := ⟨Fin.castLE h, Fin.castLE_injective h⟩
    have e : (⊤ : SimpleGraph (Fin t)) ↪g (⊤ : SimpleGraph (Fin n)) := by
      simpa only [← SimpleGraph.completeGraph_eq_top] using
        (SimpleGraph.Embedding.completeGraph f)
    exact e.isContained
  · left
    intro hfree
    apply hG
    exact SimpleGraph.cliqueFree_two.mp hfree

lemma not_ramseyTwoProperty_of_lt {t n : ℕ} (h : n < t) :
    ¬ ramseyTwoProperty t n := by
  intro hp
  have h1 : (⊥ : SimpleGraph (Fin n)).CliqueFree 2 :=
    SimpleGraph.cliqueFree_bot (by norm_num)
  have h2 : ((⊥ : SimpleGraph (Fin n))ᶜ).CliqueFree t := by
    rw [compl_bot]
    exact SimpleGraph.cliqueFree_of_card_lt (by simpa using h)
  exact (hp ⊥).elim (fun hn => hn h1) (fun hn => hn h2)

lemma ramseyTwoProperty_iff {t n : ℕ} :
    ramseyTwoProperty t n ↔ t ≤ n := by
  constructor
  · intro h
    by_contra hn
    exact not_ramseyTwoProperty_of_lt (Nat.lt_of_not_ge hn) h
  · exact ramseyTwoProperty_of_le

noncomputable def ramseyNumber_R2 (t : ℕ) : ℕ := by
  classical
  exact Nat.find (show ∃ n, ramseyTwoProperty t n from
    ⟨t, ramseyTwoProperty_of_le le_rfl⟩)

theorem ramseyNumber_R2_eq (t : ℕ) : ramseyNumber_R2 t = t := by
  classical
  unfold ramseyNumber_R2
  apply Nat.le_antisymm
  · exact Nat.find_min' _ (ramseyTwoProperty_of_le le_rfl)
  · exact ramseyTwoProperty_iff.mp (Nat.find_spec _)

end MathlibPlus.GraphTheory
