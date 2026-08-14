import Mathlib

namespace MathlibPlus.Open.ResearchFormalization

section HigherPlaneTwists

abbrev HigherScalar := ZMod 3
abbrev HigherRankFive := Fin 5 → HigherScalar
abbrev HigherRankSix := HigherScalar × HigherRankFive
abbrev HigherFunction := HigherScalar → HigherScalar → HigherScalar

def higherRankFiveGForward (h : HigherRankFive) : HigherRankFive :=
  ![h 0, h 1, h 2 + h 0 * (h 0 - 1),
    h 3 + (2 * h 0 - 1) * h 1, h 4 + h 1 ^ 2]

def higherRankFiveGBackward (h : HigherRankFive) : HigherRankFive :=
  ![h 0, h 1, h 2 - h 0 * (h 0 - 1),
    h 3 - (2 * h 0 - 1) * h 1, h 4 - h 1 ^ 2]

def higherRankFiveG : HigherRankFive ≃ HigherRankFive :=
  { toFun := higherRankFiveGForward
    invFun := higherRankFiveGBackward
    left_inv := by
      intro h
      funext k
      fin_cases k <;> simp [higherRankFiveGForward, higherRankFiveGBackward] <;> ring
    right_inv := by
      intro h
      funext k
      fin_cases k <;> simp [higherRankFiveGForward, higherRankFiveGBackward] <;> ring }

def higherPolynomial (c : Fin 8 → HigherScalar)
    (i j : HigherScalar) : HigherScalar :=
  c 0 * i + c 1 * j + c 2 * i ^ 2 + c 3 * i * j + c 4 * j ^ 2 +
    c 5 * i ^ 2 * j + c 6 * i * j ^ 2 + c 7 * i ^ 2 * j ^ 2

def higherPlaneShear (φ : HigherFunction) : HigherRankSix ≃ HigherRankSix :=
  { toFun := fun e => (e.1 + φ (e.2 0) (e.2 1), e.2)
    invFun := fun e => (e.1 - φ (e.2 0) (e.2 1), e.2)
    left_inv := by
      intro e
      apply Prod.ext
      · dsimp
        abel
      · rfl
    right_inv := by
      intro e
      apply Prod.ext
      · dsimp
        abel
      · rfl }

def higherLiftedG : HigherRankSix ≃ HigherRankSix :=
  { toFun := fun e => (e.1, higherRankFiveG e.2)
    invFun := fun e => (e.1, higherRankFiveG.symm e.2)
    left_inv := by
      intro e
      apply Prod.ext
      · rfl
      · exact higherRankFiveG.symm_apply_apply e.2
    right_inv := by
      intro e
      apply Prod.ext
      · rfl
      · exact higherRankFiveG.apply_symm_apply e.2 }

def higherTwist (φ : HigherFunction) : HigherRankSix ≃ HigherRankSix :=
  (higherPlaneShear φ).trans higherLiftedG

def higherNormalizedFunctions : Set HigherFunction :=
  {φ | φ 0 0 = 0}

def higherDegreeFunctions : Set HigherFunction :=
  {φ | ∃ c : Fin 8 → HigherScalar,
      (∀ i j : HigherScalar, φ i j = higherPolynomial c i j) ∧
      (c 5 ≠ 0 ∨ c 6 ≠ 0 ∨ c 7 ≠ 0)}

def higherRhoZeroFunctions : Set HigherFunction :=
  {φ | ∃ c : Fin 8 → HigherScalar,
      (∀ i j : HigherScalar, φ i j = higherPolynomial c i j) ∧
      c 7 = 0 ∧ (c 5 ≠ 0 ∨ c 6 ≠ 0)}

def higherRhoNonzeroFunctions : Set HigherFunction :=
  {φ | ∃ c : Fin 8 → HigherScalar,
      (∀ i j : HigherScalar, φ i j = higherPolynomial c i j) ∧ c 7 ≠ 0}

end HigherPlaneTwists

section HigherGeneratedGroups

def higherTranslation (v : HigherRankSix) : Equiv.Perm HigherRankSix :=
  { toFun := fun x => x + v
    invFun := fun x => x - v
    left_inv := by
      intro x
      exact add_sub_cancel_right x v
    right_inv := by
      intro x
      exact sub_add_cancel x v }

noncomputable def higherTranslationGroup :
    Subgroup (Equiv.Perm HigherRankSix) :=
  Subgroup.closure (Set.range higherTranslation)

def higherConjugationHom (q : Equiv.Perm HigherRankSix) :
    Equiv.Perm HigherRankSix →* Equiv.Perm HigherRankSix :=
  { toFun := fun h => q⁻¹ * h * q
    map_one' := by simp
    map_mul' := by intro a b; simp [mul_assoc] }

def higherConjugateSubgroup
    (H : Subgroup (Equiv.Perm HigherRankSix))
    (q : Equiv.Perm HigherRankSix) : Subgroup (Equiv.Perm HigherRankSix) :=
  H.map (higherConjugationHom q)

def higherConjugateSet
    (H : Set (Equiv.Perm HigherRankSix))
    (q : Equiv.Perm HigherRankSix) : Set (Equiv.Perm HigherRankSix) :=
  {t | ∃ s, s ∈ H ∧ t = q⁻¹ * s * q}

noncomputable def higherGeneratedGroup (φ : HigherFunction) :
    Subgroup (Equiv.Perm HigherRankSix) :=
  Subgroup.closure
    ((higherTranslationGroup : Set (Equiv.Perm HigherRankSix)) ∪
      higherConjugateSet (higherTranslationGroup : Set (Equiv.Perm HigherRankSix))
        (higherTwist φ))

def higherPairOrbit (H : Set (Equiv.Perm HigherRankSix))
    (x y u v : HigherRankSix) : Prop :=
  ∃ g : Equiv.Perm HigherRankSix, g ∈ H ∧ g x = u ∧ g y = v

def higherExactTwoClosure (H : Set (Equiv.Perm HigherRankSix)) :
    Set (Equiv.Perm HigherRankSix) :=
  {q | ∀ x y : HigherRankSix, higherPairOrbit H x y (q x) (q y)}

def higherConjugacyInClosure (φ : HigherFunction) (h : Equiv.Perm HigherRankSix) : Prop :=
  h ∈ higherExactTwoClosure
      (higherGeneratedGroup φ : Set (Equiv.Perm HigherRankSix)) ∧
    higherConjugateSet (higherTranslationGroup : Set (Equiv.Perm HigherRankSix)) h =
      higherConjugateSet (higherTranslationGroup : Set (Equiv.Perm HigherRankSix))
        (higherTwist φ)

def higherNormalizes (φ : HigherFunction) : Prop :=
  higherConjugateSubgroup (higherGeneratedGroup φ) (higherTwist φ) =
    higherGeneratedGroup φ

def higherPointStabilizer
    (H : Subgroup (Equiv.Perm HigherRankSix)) :
    Subgroup (Equiv.Perm HigherRankSix) :=
  { carrier := {h | h ∈ H ∧ h 0 = 0}
    one_mem' := by simp
    mul_mem' := by
      intro a b ha hb
      refine ⟨H.mul_mem ha.1 hb.1, ?_⟩
      simp [ha.2, hb.2]
    inv_mem' := by
      intro a ha
      refine ⟨H.inv_mem ha.1, ?_⟩
      calc
        a.symm 0 = a.symm (a 0) := by rw [ha.2]
        _ = 0 := a.left_inv 0 }

def higherOrbitSetoid
    (K : Subgroup (Equiv.Perm HigherRankSix)) : Setoid HigherRankSix :=
  { r := fun x y => ∃ h : K, h.1 x = y
    iseqv :=
      { refl := by intro x; exact ⟨1, by simp⟩
        symm := by
          intro x y h
          rcases h with ⟨g, hg⟩
          refine ⟨g⁻¹, ?_⟩
          rw [← hg]
          exact g.1.left_inv x
        trans := by
          intro x y z hxy hyz
          rcases hxy with ⟨g, hg⟩
          rcases hyz with ⟨h, hh⟩
          refine ⟨h * g, ?_⟩
          simpa [hg] using hh } }

def higherDisplayedOrbitCondition (φ : HigherFunction) : Prop :=
  Nat.card (Quotient (higherOrbitSetoid
      (higherPointStabilizer (higherGeneratedGroup φ)))) = 105 ∧
    (∀ x : HigherRankSix,
      (higherOrbitSetoid
        (higherPointStabilizer (higherGeneratedGroup φ))).r x
          (higherTwist φ x))

/-- Claim 27743: every normalized higher-degree function has the displayed
normalizer, 105 point-stabilizer orbits, and a transporter in the exact
2-closure. -/
def claim27743 : Prop :=
  Set.ncard higherDegreeFunctions = 6318 ∧
    ∀ φ : HigherFunction, φ ∈ higherDegreeFunctions →
      higherNormalizes φ ∧
      higherDisplayedOrbitCondition φ ∧
      higherTwist φ 0 = 0 ∧
      higherConjugacyInClosure φ (higherTwist φ)

/-- Claim 27744: the two higher-degree coefficient sectors have the stated
sizes and generated-group orders. -/
def claim27744 : Prop :=
  Set.ncard higherRhoZeroFunctions = 1944 ∧
    (∀ φ : HigherFunction, φ ∈ higherRhoZeroFunctions →
      Nat.card (higherGeneratedGroup φ) = 3 ^ 10) ∧
    Set.ncard higherRhoNonzeroFunctions = 4374 ∧
    (∀ φ : HigherFunction, φ ∈ higherRhoNonzeroFunctions →
      Nat.card (higherGeneratedGroup φ) = 3 ^ 13)

/-- Claim 27745: every normalized plane-fiber function gives conjugate regular
translation groups in the exact 2-closure. -/
def claim27745 : Prop :=
  Set.ncard higherNormalizedFunctions = 6561 ∧
    ∀ φ : HigherFunction, φ ∈ higherNormalizedFunctions →
      ∃ h : Equiv.Perm HigherRankSix,
        higherConjugacyInClosure φ h

end HigherGeneratedGroups

end MathlibPlus.Open.ResearchFormalization
