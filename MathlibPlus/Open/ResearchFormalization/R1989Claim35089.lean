import MathlibPlus.Open.Research.BatchR1989.Claim35099

namespace MathlibPlus.Open.ResearchFormalization.R1989Claim35089

noncomputable section

abbrev F2 := ZMod 2
abbrev W (d : Nat) := Fin d → F2

def quotientEventA {d : Nat} (K : Submodule F2 (W d))
    (S : Set (W d)) (a : W d) : Set (W d ⧸ K) :=
  MathlibPlus.Open.Research.BatchR1989.quotientSupport_35099 K
    (MathlibPlus.Open.Research.BatchR1989.completeAutocorrelation_35099 S a)

def quotientEventB {d : Nat} (K : Submodule F2 (W d))
    (S : Set (W d)) (b : W d) : Set (W d ⧸ K) :=
  MathlibPlus.Open.Research.BatchR1989.quotientSupport_35099 K
    (MathlibPlus.Open.Research.BatchR1989.completeAutocorrelation_35099 S b)

def quotientEventOverlap {d : Nat} (K : Submodule F2 (W d))
    (S : Set (W d)) (a b : W d) : Set (W d ⧸ K) :=
  quotientEventA K S a ∩ quotientEventB K S b

def translatedDirectionalFunction {d : Nat}
    (f : W d → F2) (v : W d) : W d → F2 :=
  fun x => f (x + v)

def literalDirectionalOrbit {d : Nat}
    (f : W d → F2) : Set (W d → F2) :=
  {g | ∃ v : W d, g = translatedDirectionalFunction f v}

noncomputable def selectedIndicator {d : Nat} (S : Set (W d)) : W d → F2 :=
  fun x => @ite F2 (x ∈ S) (Classical.propDecidable (x ∈ S)) 1 0

def selectedOrbitClass {d m : Nat}
    (S : Fin m → Set (W d)) (i : Fin m) : Set (Fin m) :=
  {j |
    literalDirectionalOrbit (selectedIndicator (S j)) =
      literalDirectionalOrbit (selectedIndicator (S i))}

def selectedOrbitCappedClass {d m : Nat}
    (S : Fin m → Set (W d)) (M : Nat) : Prop :=
  ∃ i : Fin m,
    Set.ncard (selectedOrbitClass S i) ≤ M ∧
      ∀ j : Fin m, j ∈ selectedOrbitClass S i

/-- Claim 35089: exact homogeneous quotient supports supply pairwise-distinct
witnesses, the quotient and ambient cardinality bounds, and the orbit-cap
bound for a literal directional orbit class. -/
def claim_35089 : Prop :=
  ∀ (d m M : Nat) (K : Submodule F2 (W d))
    (S : Fin m → Set (W d)) (a b : W d),
    a + b ∈ K →
      (∀ i : Fin m,
        (Set.ncard (S i) : ℝ) > (Fintype.card (W d) : ℝ) / 2) →
        (∀ i j : Fin m, i < j →
          Disjoint (quotientEventA K (S i) a)
            (quotientEventB K (S j) b)) →
          (∀ i : Fin m,
            (quotientEventOverlap K (S i) a b).Nonempty) ∧
            (∃ t : Fin m → W d ⧸ K,
              (∀ i : Fin m,
                t i ∈ quotientEventOverlap K (S i) a b) ∧
                Function.Injective t ∧
                m ≤ Fintype.card (W d ⧸ K) ∧
                Fintype.card (W d ⧸ K) ≤ Fintype.card (W d) ∧
                (selectedOrbitCappedClass S M → m ≤ M))

end

end MathlibPlus.Open.ResearchFormalization.R1989Claim35089
