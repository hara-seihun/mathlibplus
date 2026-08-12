import Mathlib

namespace MathlibPlus.Algebra.Claim30413

/-- Claim 30413: for an odd prime `p`, the two quadratic shears of
`(ZMod p)²` are permutations.  The inverse shears are written explicitly,
so this does not rely on cancellation properties of the quadratic. -/
theorem quadraticShears_bijective
    (p : ℕ) (_hp : p.Prime) (_hodd : Odd p) :
    Function.Bijective
        (fun v : ZMod p × ZMod p =>
          (v.1, v.2 + v.1 * (v.1 - 1) * (2 : ZMod p)⁻¹)) ∧
      Function.Bijective
        (fun v : ZMod p × ZMod p =>
          (v.1 + v.2 * (v.2 - 1) * (2 : ZMod p)⁻¹, v.2)) := by
  let q : ZMod p → ZMod p := fun x => x * (x - 1) * (2 : ZMod p)⁻¹
  let fv : ZMod p × ZMod p → ZMod p × ZMod p :=
    fun v => (v.1, v.2 + q v.1)
  let fh : ZMod p × ZMod p → ZMod p × ZMod p :=
    fun v => (v.1 + q v.2, v.2)
  change Function.Bijective fv ∧ Function.Bijective fh
  have hv_left : Function.LeftInverse
      (fun v : ZMod p × ZMod p => (v.1, v.2 - q v.1)) fv := by
    intro v
    rcases v with ⟨x, y⟩
    simp [fv]
  have hv_right : Function.RightInverse
      (fun v : ZMod p × ZMod p => (v.1, v.2 - q v.1)) fv := by
    intro v
    rcases v with ⟨x, y⟩
    simp [fv]
  have hh_left : Function.LeftInverse
      (fun v : ZMod p × ZMod p => (v.1 - q v.2, v.2)) fh := by
    intro v
    rcases v with ⟨x, y⟩
    simp [fh]
  have hh_right : Function.RightInverse
      (fun v : ZMod p × ZMod p => (v.1 - q v.2, v.2)) fh := by
    intro v
    rcases v with ⟨x, y⟩
    simp [fh]
  constructor
  · constructor
    · exact hv_left.injective
    · intro v
      exact ⟨(v.1, v.2 - q v.1), hv_right v⟩
  · constructor
    · exact hh_left.injective
    · intro v
      exact ⟨(v.1 - q v.2, v.2), hh_right v⟩

end MathlibPlus.Algebra.Claim30413
