import MathlibPlus.Combinatorics.Claim30192

namespace MathlibPlus.Open.ResearchFormalization.R1144Claim30197

abbrev C7 := ZMod 7

def translateDevelopment (B : Set C7) : Set (Set C7) :=
  MathlibPlus.Combinatorics.Claim30192.translationDevelopment B

def affinePointPermutation (pi : Equiv.Perm C7) : Prop :=
  ∃ a b : C7, ∀ x : C7, pi x = a * x + b

def nonlinearDevelopmentPermutation (pi : Equiv.Perm C7) : Prop :=
  ¬ affinePointPermutation pi ∧
    ∃ B : Set C7,
      2 ≤ B.ncard ∧ B.ncard ≤ 5 ∧
      Set.image pi '' translateDevelopment B =
        translateDevelopment (Set.image pi B)

def fanoA : Set (Set C7) :=
  translateDevelopment ({0, 1, 3} : Set C7)

def fanoB : Set (Set C7) :=
  translateDevelopment ({0, 2, 3} : Set C7)

def supportedLine (pi : Equiv.Perm C7)
    (F : Set (Set C7)) (B : Set C7) : Prop :=
  B ∈ F ∧
    Set.image pi '' translateDevelopment B =
      translateDevelopment (Set.image pi B)

def targetSystem (pi : Equiv.Perm C7)
    (F : Set (Set C7)) (F' : Set (Set C7)) : Prop :=
  Set.image (Set.image pi) F = F'

/-- Claim 30197: a nonlinear development permutation has one of the two
literal source Fano systems, and its seven source lines have one of the two
literal target systems. -/
def claim_30197 : Prop :=
  ∀ (pi : Equiv.Perm C7), nonlinearDevelopmentPermutation pi →
    ∃! F : Set (Set C7),
      (F = fanoA ∨ F = fanoB) ∧
      (∀ B : Set C7, B ∈ F → supportedLine pi F B) ∧
      ∃ F' : Set (Set C7),
        (F' = fanoA ∨ F' = fanoB) ∧ targetSystem pi F F'

end MathlibPlus.Open.ResearchFormalization.R1144Claim30197
