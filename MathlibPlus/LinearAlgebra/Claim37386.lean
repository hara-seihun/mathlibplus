import Mathlib

namespace MathlibPlus.LinearAlgebra.Claim37386

/--
The kernel of `1 + S` for the cyclic eight-coordinate shift consists exactly
of the alternating vectors.  This is the exact linear-algebra core of claim
37386; the source's finite-field notation is represented by the `ZMod q`
coordinate carrier.
-/
theorem alternatingKernel_claim37386
    {q : ℕ} (_hq : Odd q) (x : Fin 8 → ZMod q) :
    (∀ i : Fin 8,
      x i + x ⟨(i.val + 1) % 8, by omega⟩ = 0) ↔
      ∃ c : ZMod q, ∀ i : Fin 8,
        x i = if i.val % 2 = 0 then c else -c := by
  constructor
  · intro h
    have h0 := h ⟨0, by decide⟩
    have h1 := h ⟨1, by decide⟩
    have h2 := h ⟨2, by decide⟩
    have h3 := h ⟨3, by decide⟩
    have h4 := h ⟨4, by decide⟩
    have h5 := h ⟨5, by decide⟩
    have h6 := h ⟨6, by decide⟩
    have h7 := h ⟨7, by decide⟩
    simp at h0 h1 h2 h3 h4 h5 h6 h7
    have hx1 : x 1 = -x 0 := by linear_combination h0
    have hx2 : x 2 = x 0 := by linear_combination h1 - h0
    have hx3 : x 3 = -x 0 := by linear_combination h2 - h1 + h0
    have hx4 : x 4 = x 0 := by linear_combination h3 - h2 + h1 - h0
    have hx5 : x 5 = -x 0 := by linear_combination h4 - h3 + h2 - h1 + h0
    have hx6 : x 6 = x 0 := by linear_combination h5 - h4 + h3 - h2 + h1 - h0
    have hx7 : x 7 = -x 0 := by
      linear_combination h6 - h5 + h4 - h3 + h2 - h1 + h0
    refine ⟨x 0, ?_⟩
    intro i
    fin_cases i <;> simp [hx1, hx2, hx3, hx4, hx5, hx6, hx7]
  · rintro ⟨c, hc⟩ i
    have hi := hc i
    have hn := hc ⟨(i.val + 1) % 8, by omega⟩
    rw [hi, hn]
    by_cases he : i.val % 2 = 0
    · have hnext : ((i.val + 1) % 8) % 2 = 1 := by omega
      simp [he, hnext]
    · have hnext : ((i.val + 1) % 8) % 2 = 0 := by omega
      simp [he, hnext]

end MathlibPlus.LinearAlgebra.Claim37386
