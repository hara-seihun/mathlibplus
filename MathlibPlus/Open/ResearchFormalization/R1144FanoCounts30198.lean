import MathlibPlus.Combinatorics.Claim30192

namespace MathlibPlus.Open.ResearchFormalization.R1144FanoCounts30198

noncomputable section

abbrev C7 := ZMod 7

def translateSet (B : Set C7) (t : C7) : Set C7 :=
  {x | ∃ b ∈ B, x = b + t}

def development (B : Set C7) : Set (Set C7) :=
  {C | ∃ t : C7, C = translateSet B t}

def affinePointPermutation (π : Equiv.Perm C7) : Prop :=
  ∃ a b : C7, ∀ x : C7, π x = a * x + b

def nonlinearDevelopmentPermutation (π : Equiv.Perm C7) : Prop :=
  ¬ affinePointPermutation π ∧
    ∃ B : Set C7,
      2 ≤ B.ncard ∧ B.ncard ≤ 5 ∧
      Set.image π '' development B = development (Set.image π B)

def fanoA : Set (Set C7) :=
  development ({0, 1, 3} : Set C7)

def fanoB : Set (Set C7) :=
  development ({0, 2, 3} : Set C7)

def supportedLine (π : Equiv.Perm C7)
    (F : Set (Set C7)) (B : Set C7) : Prop :=
  B ∈ F ∧ Set.image π '' development B = development (Set.image π B)

def sourceSystem (π : Equiv.Perm C7) (F : Set (Set C7)) : Prop :=
  (F = fanoA ∨ F = fanoB) ∧
    (∀ B : Set C7, B ∈ F → supportedLine π F B)

def targetSystem (π : Equiv.Perm C7)
    (F F' : Set (Set C7)) : Prop :=
  Set.image (Set.image π) F = F'

def orderedSourceTargetClass
    (F F' : Set (Set C7)) : Set (Equiv.Perm C7) :=
  {π | nonlinearDevelopmentPermutation π ∧
    sourceSystem π F ∧ targetSystem π F F'}

def sourceClass (F : Set (Set C7)) : Set (Equiv.Perm C7) :=
  {π | nonlinearDevelopmentPermutation π ∧ sourceSystem π F}

/-- Claim 30198: the two source systems each support 294 nonaffine
permutations, and each ordered source-target class has 147. -/
def claim30198 : Prop :=
  Set.ncard (sourceClass fanoA) = 294 ∧
    Set.ncard (sourceClass fanoB) = 294 ∧
      (∀ F : Set (Set C7), (F = fanoA ∨ F = fanoB) →
        ∀ F' : Set (Set C7), (F' = fanoA ∨ F' = fanoB) →
          Set.ncard (orderedSourceTargetClass F F') = 147)

end

end MathlibPlus.Open.ResearchFormalization.R1144FanoCounts30198
