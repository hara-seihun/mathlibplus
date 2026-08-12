import Mathlib

namespace MathlibPlus.Combinatorics

/--
Claim 6845.  A cut of `[a,b)` is identified with the ordered two-part
composition obtained by subtracting its left endpoint from the first part
and its right endpoint from the second part.
-/
theorem cutsAsOrderedTwoPartCompositions_claim6845 (a b : ℕ) (hab : a < b) :
    Function.Bijective
      (let f : {i : ℕ // i ∈ Set.Ico a b} →
          {pq : ℕ × ℕ // pq.1 + pq.2 = b - a - 1} := fun i =>
        ⟨(i.1 - a, b - 1 - i.1), by
          have hi := i.property
          simp only [Set.mem_Ico] at hi
          omega⟩
       f) := by
  let f : {i : ℕ // i ∈ Set.Ico a b} →
      {pq : ℕ × ℕ // pq.1 + pq.2 = b - a - 1} := fun i =>
    ⟨(i.1 - a, b - 1 - i.1), by
      have hi := i.property
      simp only [Set.mem_Ico] at hi
      omega⟩
  change Function.Bijective f
  constructor
  · intro i j hij
    apply Subtype.ext
    have hfst := congrArg (fun pq => pq.1) (congrArg Subtype.val hij)
    simp [f] at hfst
    have hi := i.property
    have hj := j.property
    simp only [Set.mem_Ico] at hi hj
    omega
  · rintro ⟨⟨p, q⟩, hpq⟩
    let i : {i : ℕ // i ∈ Set.Ico a b} :=
      ⟨a + p, by
        simp only [Set.mem_Ico]
        omega⟩
    refine ⟨i, ?_⟩
    apply Subtype.ext
    simp [f, i]
    omega

end MathlibPlus.Combinatorics
