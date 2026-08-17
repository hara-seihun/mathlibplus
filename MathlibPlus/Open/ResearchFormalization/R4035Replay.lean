import Mathlib

namespace MathlibPlus.Open.ResearchFormalization.R4035Replay

noncomputable section

private abbrev V := Fin 3
private abbrev P := MvPolynomial V ℤ

private def a : V := 0
private def s : V := 1
private def t : V := 2
private def filtration : V → ℕ := ![2, 1, 0]

private def physicalEdge (u v : V) : Prop :=
  (u = a ∧ v = s) ∨ (u = a ∧ v = t)

private def physicalEdgeSet : Finset (V × V) :=
  {(a, s), (a, t)}

private def reachability (u v : V) : Prop :=
  Relation.ReflTransGen physicalEdge u v

private def xa : P := MvPolynomial.X a
private def xs : P := MvPolynomial.X s
private def xt : P := MvPolynomial.X t
private def gs : P := xa - xs
private def gt : P := xa - xt
private def gst : P := xs - xt
private def reducedG1 : P := xa - xt
private def reducedG2 : P := xs - xt

private def m0 : V →₀ ℕ := Finsupp.single a 1
private def m1 : V →₀ ℕ := Finsupp.single s 1
private def m2 : V →₀ ℕ := Finsupp.single t 1

private def lexGreater (u v : V →₀ ℕ) : Prop :=
  (u a > v a) ∨
    (u a = v a ∧ u s > v s) ∨
      (u a = v a ∧ u s = v s ∧ u t > v t)

private def physicalIdeal : Ideal P :=
  Ideal.span ({gs, gt} : Set P)

private def reducedIdeal : Ideal P :=
  Ideal.span ({reducedG1, reducedG2} : Set P)

/-- Claim 52081: the exact three-state physical replay and its signed ideal,
S-polynomial, replacement-basis, and reachability facts. -/
def claim52081_replay : Prop :=
  filtration a > filtration s ∧
    filtration s > filtration t ∧
      (∀ u v : V, physicalEdge u v ↔ (u, v) ∈ physicalEdgeSet) ∧
        ¬ (∃ v : V, physicalEdge s v) ∧
          ¬ reachability s t ∧
            gst = -gs + gt ∧
              gst ∈ physicalIdeal ∧
                gs - gt = xt - xs ∧
                  gst = - (gs - gt) ∧
                    physicalIdeal = reducedIdeal ∧
                      (xa - xs = reducedG1 - reducedG2) ∧
                        MvPolynomial.support gs = {m0, m1} ∧
                          MvPolynomial.support gt = {m0, m2} ∧
                            MvPolynomial.support reducedG1 = {m0, m2} ∧
                              MvPolynomial.support reducedG2 = {m1, m2} ∧
                                lexGreater m0 m1 ∧
                                  lexGreater m0 m2 ∧
                                    lexGreater m1 m2 ∧
                                      m0 ≠ m1 ∧ m0 ≠ m2 ∧ m1 ≠ m2 ∧
                                        ¬ m0 ≤ m2 ∧ ¬ m1 ≤ m2

end

end MathlibPlus.Open.ResearchFormalization.R4035Replay
