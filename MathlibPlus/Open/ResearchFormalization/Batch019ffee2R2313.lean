import Mathlib

namespace MathlibPlus.Open.ResearchFormalization.Batch019ffee2R2313

inductive RootedTree : Type
  | node : List RootedTree → RootedTree

def order : RootedTree → Nat
  | .node branches => 1 + (branches.map order).sum

abbrev Coeff := MvPolynomial (Fin 2) (ZMod 2)
abbrev Poly := Polynomial Coeff

noncomputable def tPoly : Poly := Polynomial.C (MvPolynomial.X 0)
noncomputable def uPoly : Poly := Polynomial.C (MvPolynomial.X 1)
noncomputable def sPoly : Poly := Polynomial.X

noncomputable def treePolynomial : RootedTree → Poly
  | .node branches =>
      uPoly * sPoly ^ (order (.node branches) - 1) +
        tPoly * (branches.map treePolynomial).prod
termination_by tree => order tree
  decreasing_by
    rename_i x hx
    induction branches generalizing x with
    | nil => simp_all
    | cons branch rest ih =>
        simp only [List.mem_cons] at hx
        rcases hx with rfl | hx
        · simp [order]
          omega
        · have hlt := ih x hx
          simp [order] at hlt ⊢
          omega

def C4 : RootedTree := .node [.node [], .node [.node []]]
def D4 : RootedTree := .node [.node [.node [.node []]]]

noncomputable def frac (p : Coeff) : FractionRing Coeff :=
  algebraMap Coeff (FractionRing Coeff) p

noncomputable def constantRatio : FractionRing Coeff :=
  frac (Polynomial.eval 0 (treePolynomial C4)) *
    (frac (Polynomial.eval 0 (treePolynomial D4)))⁻¹

noncomputable def expectedRatio : FractionRing Coeff :=
  (frac (MvPolynomial.X 0 + MvPolynomial.X 1)) *
    (frac (MvPolynomial.X 0))⁻¹

/-- The four-vertex rooted-pair witness and its exact polynomial assertions. -/
noncomputable def claim43962 : Prop :=
  C4 ≠ D4 ∧
  sPoly ^ (4 - 1) ∣
    (Polynomial.derivative (treePolynomial C4) * treePolynomial D4 +
      treePolynomial C4 * Polynomial.derivative (treePolynomial D4)) ∧
  constantRatio = expectedRatio ∧
  ¬ ∃ z : FractionRing Coeff, z * z = expectedRatio

end MathlibPlus.Open.ResearchFormalization.Batch019ffee2R2313
