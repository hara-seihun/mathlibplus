import Mathlib

namespace MathlibPlus.Open.Research.RootedTrees

abbrev finiteTree (V : Type*) [Fintype V] :=
  {T : SimpleGraph V // T.IsTree}

noncomputable def rootedConnectedSubtreeBoundaryPolynomial
    {V : Type*} [Fintype V] [DecidableEq V]
    (T : finiteTree V) (r : V) : Polynomial (Polynomial ℚ) := by
  classical
  exact ∑ H : Finset V,
    if r ∈ H ∧ (SimpleGraph.induce (H : Set V) T.1).Connected then
      (Polynomial.X : Polynomial (Polynomial ℚ)) ^
          (T.1.edgeFinset.filter (fun e => ∀ x, Sym2.Mem x e → x ∈ H)).card *
        Polynomial.C ((Polynomial.X : Polynomial ℚ) ^
          (T.1.edgeFinset.filter (fun e =>
            (∃ x, Sym2.Mem x e ∧ x ∈ H) ∧
            (∃ x, Sym2.Mem x e ∧ x ∉ H))).card)
    else 0

noncomputable def rootedAtom
    {V : Type*} [Fintype V] [DecidableEq V]
    (T : finiteTree V) (r : V) : Polynomial (Polynomial ℚ) :=
  Polynomial.C (Polynomial.X : Polynomial ℚ) +
    Polynomial.X * rootedConnectedSubtreeBoundaryPolynomial T r

def rootedAtomCoefficientAndDegreeProfile
    {V : Type*} [Fintype V] [DecidableEq V]
    (T : finiteTree V) (r : V) : Prop :=
  (rootedAtom T r).Monic ∧
    (rootedAtom T r).natDegree = Fintype.card V ∧
    (rootedAtom T r).coeff 0 = (Polynomial.X : Polynomial ℚ) ∧
    ∀ i < (rootedAtom T r).natDegree,
      (Polynomial.X : Polynomial ℚ) ∣ (rootedAtom T r).coeff i

def rootedAtomEisensteinIrreducibility
    {V : Type*} [Fintype V] [DecidableEq V]
    (T : finiteTree V) (r : V) : Prop :=
  Prime (Polynomial.X : Polynomial ℚ) ∧
    (∀ i < (rootedAtom T r).natDegree,
      (Polynomial.X : Polynomial ℚ) ∣ (rootedAtom T r).coeff i) ∧
    (rootedAtom T r).coeff 0 = (Polynomial.X : Polynomial ℚ) ∧
    ¬((Polynomial.X : Polynomial ℚ) ^ 2 ∣ (rootedAtom T r).coeff 0) ∧
    ¬((Polynomial.X : Polynomial ℚ) ∣
      (rootedAtom T r).coeff (rootedAtom T r).natDegree) ∧
    Irreducible (rootedAtom T r)

def rootedTreeIsomorphic
    {V W : Type*} [Fintype V] [Fintype W]
    (T : finiteTree V) (r : V) (S : finiteTree W) (s : W) : Prop :=
  ∃ e : T.1 ≃g S.1, e r = s

def completeRootedTreeRigidity : Prop :=
  ∀ {V W : Type*} [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W]
    (T : finiteTree V) (r : V) (S : finiteTree W) (s : W),
    rootedConnectedSubtreeBoundaryPolynomial T r =
        rootedConnectedSubtreeBoundaryPolynomial S s ↔
      rootedTreeIsomorphic T r S s

end MathlibPlus.Open.Research.RootedTrees
