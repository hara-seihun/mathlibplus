import Mathlib

namespace MathlibPlus.ResearchFormalization.Batch01a00154dbb74168f699dfdca26eeb1Support

abbrev R1440GL53 := Matrix.GeneralLinearGroup (Fin 5) (ZMod 3)
abbrev R1440V53 := Fin 5 → ZMod 3

def r1440ConjugateSubgroups (P : Sylow 3 R1440GL53)
    (A B : Subgroup P) : Prop :=
  ∃ p : P, ∀ x : P, x ∈ B ↔ p * x * p⁻¹ ∈ A

def r1440SubgroupConjugacySetoid (P : Sylow 3 R1440GL53) : Setoid (Subgroup P) where
  r := r1440ConjugateSubgroups P
  iseqv := {
    refl := by
      intro A
      exact ⟨1, by simp⟩
    symm := by
      intro A B h
      rcases h with ⟨p, h⟩
      refine ⟨p⁻¹, ?_⟩
      intro x
      have hx := h (p⁻¹ * x * p)
      simpa [mul_assoc] using hx.symm
    trans := by
      intro A B C hAB hBC
      rcases hAB with ⟨p, hp⟩
      rcases hBC with ⟨q, hq⟩
      refine ⟨p * q, ?_⟩
      intro x
      exact (hq x).trans (hp (q * x * q⁻¹)) |>.trans (by simp [mul_assoc])
  }

noncomputable def r1440FixedVectorCount (P : Sylow 3 R1440GL53)
    (S : Subgroup P) : Nat := by
  classical
  exact (Finset.univ.filter (fun v : R1440V53 =>
    ∀ s : S, Matrix.mulVec (s : R1440GL53) v = v)).card

def r1440ClassesWithAtLeastNineFixedVectors
    (P : Sylow 3 R1440GL53) : Type :=
  {c : Quotient (r1440SubgroupConjugacySetoid P) //
    ∃ S : Subgroup P,
      Quotient.mk (r1440SubgroupConjugacySetoid P) S = c ∧
      9 ≤ r1440FixedVectorCount P S}

abbrev R4293Sign := Fin 2

def r4293MinusOne : R4293Sign := ⟨0, by decide⟩
def r4293PlusOne : R4293Sign := ⟨1, by decide⟩

def r4293SignValue : R4293Sign → ℝ
  | ⟨0, _⟩ => -1
  | ⟨1, _⟩ => 1

abbrev R4293BooleanAssignment (n : ℕ) := Fin n → R4293Sign
abbrev R4293BooleanFunction (n : ℕ) := R4293BooleanAssignment n → R4293Sign

def r4293PlusAt (x : R4293BooleanAssignment n) (i : Fin n) :
    R4293BooleanAssignment n :=
  Function.update x i r4293PlusOne

def r4293MinusAt (x : R4293BooleanAssignment n) (i : Fin n) :
    R4293BooleanAssignment n :=
  Function.update x i r4293MinusOne

noncomputable def r4293PartialDerivative (f : R4293BooleanAssignment n → ℝ)
    (x : R4293BooleanAssignment n) (i : Fin n) : ℝ :=
  (f (r4293PlusAt x i) - f (r4293MinusAt x i)) / 2

inductive R4293DecisionTree (n : ℕ) where
  | leaf : R4293Sign → R4293DecisionTree n
  | query : Fin n → R4293DecisionTree n → R4293DecisionTree n → R4293DecisionTree n

def R4293DecisionTree.evaluate : R4293DecisionTree n →
    R4293BooleanAssignment n → R4293Sign
  | .leaf b, _ => b
  | .query i whenMinus whenPlus, x =>
      if x i = r4293PlusOne then whenPlus.evaluate x else whenMinus.evaluate x

def R4293DecisionTree.queries : R4293DecisionTree n → Fin n →
    R4293BooleanAssignment n → Prop
  | .leaf _, _, _ => False
  | .query j whenMinus whenPlus, i, x =>
      j = i ∨ if x j = r4293PlusOne then whenPlus.queries i x else whenMinus.queries i x

def r4293Determines (T : R4293DecisionTree n)
    (H : R4293BooleanFunction n) : Prop :=
  ∀ x, T.evaluate x = H x

noncomputable def r4293LawExpectation
    (lambda : PMF (R4293BooleanFunction n)) :
    R4293BooleanAssignment n → ℝ := by
  classical
  exact fun x => ∑ H, (lambda H).toReal * r4293SignValue (H x)

noncomputable def r4293PivotalMass
    (lambda : PMF (R4293BooleanFunction n))
    (x : R4293BooleanAssignment n) (i : Fin n) : ℝ := by
  classical
  exact ∑ H, (lambda H).toReal *
    (if r4293PartialDerivative (fun y => r4293SignValue (H y)) x i ≠ 0
      then 1 else 0)

noncomputable def r4293TreeQueryMass
    (lambda : PMF (R4293BooleanFunction n))
    (trees : R4293BooleanFunction n → R4293DecisionTree n)
    (x : R4293BooleanAssignment n) (i : Fin n) : ℝ := by
  classical
  exact ∑ H, (lambda H).toReal *
    (if (trees H).queries i x then 1 else 0)

end MathlibPlus.ResearchFormalization.Batch01a00154dbb74168f699dfdca26eeb1Support
