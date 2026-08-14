import Mathlib

namespace MathlibPlus.Open.ProjectsResearch

/--
The two support projectors in the stated weight basis, written as their
coordinate matrices on the basis indexed by `(i,j)`.  The diagonal entries
are exactly the rank-one projectors in the claim.
-/
def alignmentSupportProjectors : Prop :=
  ∀ r : ℕ,
    let I := Fin (r + 1) × Fin (r + 1)
    let Qplus : Matrix I I ℂ :=
      Matrix.diagonal (fun ij : I => if ij.1 = ij.2 then 1 else 0)
    let Qminus : Matrix I I ℂ :=
      Matrix.diagonal
        (fun ij : I => if ij.1.val + ij.2.val = r then 1 else 0)
    Matrix.rank Qplus = r + 1 ∧ Matrix.rank Qminus = r + 1

/--
The torus traces of the two support projectors and the zero-weight
anti-diagonal, in the same weight-basis coordinates as the claim.
-/
def alignmentTraces : Prop :=
  ∀ r : ℕ,
    let I := Fin (r + 1) × Fin (r + 1)
    let exponent : Fin (r + 1) → ℤ :=
      fun i => (r : ℤ) - 2 * (i.val : ℤ)
    let character : ℂ → ℂ :=
      fun z => ∑ i : Fin (r + 1), z ^ exponent i
    let Qplus : Matrix I I ℂ :=
      Matrix.diagonal (fun ij : I => if ij.1 = ij.2 then 1 else 0)
    let Qminus : Matrix I I ℂ :=
      Matrix.diagonal
        (fun ij : I => if ij.1.val + ij.2.val = r then 1 else 0)
    ∀ (y α : ℂ), y ≠ 0 → α ≠ 0 →
      let torus : Matrix I I ℂ :=
        Matrix.diagonal
          (fun ij : I => y ^ exponent ij.1 * α ^ exponent ij.2)
      Matrix.trace (Qplus * torus) = character (y * α) ∧
        Matrix.trace (Qminus * torus) = character (y / α) ∧
        (∀ ij : I,
          exponent ij.1 + exponent ij.2 = 0 ↔
            ij.1.val + ij.2.val = r) ∧
        Fintype.card
            {ij : I // exponent ij.1 + exponent ij.2 = 0} = r + 1

end MathlibPlus.Open.ProjectsResearch
