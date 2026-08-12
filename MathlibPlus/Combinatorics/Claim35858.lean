import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Image

namespace MathlibPlus.Combinatorics.Claim35858

/-!
# Residual links of a three-sunflower-free uniform family

For a finite family of finite sets, a three-sunflower is represented by three
pairwise distinct members whose three pairwise intersections agree.  The
`qLink` below is the image of the source members containing the fixed core `T`
under deletion of `T`.  Thus its members are the residual petals, and
three pairwise disjoint residual members reconstruct a three-sunflower with
core `T`.
-/

private def threeSunflowerFree {α : Type*} [DecidableEq α]
    (G : Finset (Finset α)) : Prop :=
  ∀ A ∈ G, ∀ B ∈ G, ∀ C ∈ G,
    A ≠ B → A ≠ C → B ≠ C →
    ¬ (A ∩ B = A ∩ C ∧ A ∩ B = B ∩ C)

private def qLink {α : Type*} [DecidableEq α]
    (G : Finset (Finset α)) (T : Finset α) : Finset (Finset α) :=
  (G.filter (fun A => T ⊆ A)).image (fun A => A \ T)

private lemma inter_sdiff_inter_eq {α : Type*} [DecidableEq α]
    {A B T P Q : Finset α}
    (hTA : T ⊆ A) (hTB : T ⊆ B)
    (hP : P = A \ T) (hQ : Q = B \ T) :
    A ∩ B = T ∪ (P ∩ Q) := by
  subst P
  subst Q
  ext x
  constructor
  · intro hx
    by_cases hxT : x ∈ T
    · exact Finset.mem_union_left _ hxT
    · apply Finset.mem_union.mpr
      exact Or.inr (Finset.mem_inter.mpr ⟨
        Finset.mem_sdiff.mpr ⟨(Finset.mem_inter.mp hx).1, hxT⟩,
        Finset.mem_sdiff.mpr ⟨(Finset.mem_inter.mp hx).2, hxT⟩⟩)
  · intro hx
    rcases Finset.mem_union.mp hx with hxT | hxPQ
    · exact Finset.mem_inter.mpr ⟨hTA hxT, hTB hxT⟩
    · exact Finset.mem_inter.mpr ⟨
        (Finset.mem_sdiff.mp (Finset.mem_inter.mp hxPQ).1).1,
        (Finset.mem_sdiff.mp (Finset.mem_inter.mp hxPQ).2).1⟩

private lemma card_sdiff_eq_sub {α : Type*} [Fintype α] [DecidableEq α]
    {A T : Finset α} {r q : ℕ}
    (hT : T ⊆ A) (hA : A.card = r) (hTc : T.card = q) :
    (A \ T).card = r - q := by
  have hcard : (T ∩ A).card = T.card := by
    rw [Finset.inter_eq_left.mpr hT]
  rw [Finset.card_sdiff, hcard, hA, hTc]

/-- Claim 35858, with the residual-link and matching conventions made explicit. -/
theorem linkInheritance_claim35858
    {α : Type*} [Fintype α] [DecidableEq α]
    (G : Finset (Finset α)) (r q : ℕ) (T : Finset α)
    (_hq : 1 ≤ q)
    (hUniform : ∀ A ∈ G, A.card = r)
    (hFree : threeSunflowerFree G)
    (hTc : T.card = q)
    (_hPositive : (qLink G T).Nonempty) :
    (∀ P ∈ qLink G T, P.card = r - q) ∧
    threeSunflowerFree (qLink G T) ∧
    (∀ P ∈ qLink G T, ∀ Q ∈ qLink G T, ∀ R ∈ qLink G T,
      P ≠ Q → P ≠ R → Q ≠ R →
      P ∩ Q = ∅ → P ∩ R = ∅ → Q ∩ R = ∅ → False) := by
  have hcard : ∀ P ∈ qLink G T, P.card = r - q := by
    intro P hP
    rcases Finset.mem_image.mp hP with ⟨A, hAG, rfl⟩
    exact card_sdiff_eq_sub (Finset.mem_filter.mp hAG).2
      (hUniform A (Finset.mem_filter.mp hAG).1) hTc
  have hsource_of_link : ∀ P ∈ qLink G T, ∃ A ∈ G, T ⊆ A ∧ A \ T = P := by
    intro P hP
    rcases Finset.mem_image.mp hP with ⟨A, hAG, hAP⟩
    exact ⟨A, (Finset.mem_filter.mp hAG).1, (Finset.mem_filter.mp hAG).2, hAP⟩
  have hlink_free : threeSunflowerFree (qLink G T) := by
    intro P hP Q hQ R hR hPQ hPR hQR hs
    rcases hsource_of_link P hP with ⟨A, hAG, hTA, hAP⟩
    rcases hsource_of_link Q hQ with ⟨B, hBG, hTB, hBQ⟩
    rcases hsource_of_link R hR with ⟨C, hCG, hTC, hCR⟩
    apply hFree A hAG B hBG C hCG
    · intro h
      apply hPQ
      calc
        P = A \ T := hAP.symm
        _ = B \ T := by rw [h]
        _ = Q := hBQ
    · intro h
      apply hPR
      calc
        P = A \ T := hAP.symm
        _ = C \ T := by rw [h]
        _ = R := hCR
    · intro h
      apply hQR
      calc
        Q = B \ T := hBQ.symm
        _ = C \ T := by rw [h]
        _ = R := hCR
    · have hAB : A ∩ B = T ∪ (P ∩ Q) :=
        inter_sdiff_inter_eq hTA hTB hAP.symm hBQ.symm
      have hAC : A ∩ C = T ∪ (P ∩ R) :=
        inter_sdiff_inter_eq hTA hTC hAP.symm hCR.symm
      have hBC : B ∩ C = T ∪ (Q ∩ R) :=
        inter_sdiff_inter_eq hTB hTC hBQ.symm hCR.symm
      constructor
      · rw [hAB, hAC, hs.1]
      · rw [hAB, hBC, hs.2]
  refine ⟨hcard, hlink_free, ?_⟩
  intro P hP Q hQ R hR hPQ hPR hQR hdisPQ hdisPR hdisQR
  rcases hsource_of_link P hP with ⟨A, hAG, hTA, hAP⟩
  rcases hsource_of_link Q hQ with ⟨B, hBG, hTB, hBQ⟩
  rcases hsource_of_link R hR with ⟨C, hCG, hTC, hCR⟩
  have hAB : A ∩ B = T ∪ (P ∩ Q) :=
    inter_sdiff_inter_eq hTA hTB hAP.symm hBQ.symm
  have hAC : A ∩ C = T ∪ (P ∩ R) :=
    inter_sdiff_inter_eq hTA hTC hAP.symm hCR.symm
  have hBC : B ∩ C = T ∪ (Q ∩ R) :=
    inter_sdiff_inter_eq hTB hTC hBQ.symm hCR.symm
  have hAB' : A ∩ B = T := by simpa [hdisPQ] using hAB
  have hAC' : A ∩ C = T := by simpa [hdisPR] using hAC
  have hBC' : B ∩ C = T := by simpa [hdisQR] using hBC
  exfalso
  apply hFree A hAG B hBG C hCG
  · intro h
    apply hPQ
    calc
      P = A \ T := hAP.symm
      _ = B \ T := by rw [h]
      _ = Q := hBQ
  · intro h
    apply hPR
    calc
      P = A \ T := hAP.symm
      _ = C \ T := by rw [h]
      _ = R := hCR
  · intro h
    apply hQR
    calc
      Q = B \ T := hBQ.symm
      _ = C \ T := by rw [h]
      _ = R := hCR
  · constructor
    · exact hAB'.trans hAC'.symm
    · exact hAB'.trans hBC'.symm

end MathlibPlus.Combinatorics.Claim35858
