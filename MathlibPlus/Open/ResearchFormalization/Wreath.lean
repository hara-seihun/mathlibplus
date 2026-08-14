import Mathlib

namespace MathlibPlus.Open.ResearchFormalization

abbrev ComponentPower (p d : ℕ) := Fin d → ZMod p
abbrev WreathVertex (p d : ℕ) := ComponentPower p d × ZMod p

/-- An explicit element of the dihedral wreath action on disjoint cycles. -/
def dihedralWreathMember' {p d : ℕ} (q : Equiv.Perm (WreathVertex p d)) : Prop :=
  ∃ σ : Equiv.Perm (ComponentPower p d),
    ∀ b : ComponentPower p d,
      ∃ ε : Fin 2, ∃ r : ZMod p,
        ∀ x : ZMod p,
          q (b, x) = (σ b, (if ε = 0 then x else -x) + r)

def dihedralWreathGroup (p d : ℕ) : Subgroup (Equiv.Perm (WreathVertex p d)) :=
  Subgroup.closure {q | dihedralWreathMember' q}

/-- The standard diagonal cycle rotation times component-translation subgroup. -/
def standardProductMember {p d : ℕ} (q : Equiv.Perm (WreathVertex p d)) : Prop :=
  ∃ a : ComponentPower p d, ∃ r : ZMod p,
    ∀ b : ComponentPower p d, ∀ x : ZMod p,
      q (b, x) = (b + a, x + r)

def standardProductGroup (p d : ℕ) : Subgroup (Equiv.Perm (WreathVertex p d)) :=
  Subgroup.closure {q | standardProductMember q}

def regularPermutationAction {α : Type*} (E : Subgroup (Equiv.Perm α)) : Prop :=
  ∀ x y : α, ∃! e : E, e.1 x = y

abbrev cyclicPowerGroup (p d : ℕ) := Multiplicative (ComponentPower p d × ZMod p)

def elementaryAbelianRegularSubgroup {p d : ℕ}
    (E : Subgroup (Equiv.Perm (WreathVertex p d))) : Prop :=
  regularPermutationAction E ∧ Nonempty (E ≃* cyclicPowerGroup p d)

def conjugateSubgroupMembership {α : Type*} (E K : Subgroup (Equiv.Perm α))
    (w : Equiv.Perm α) : Prop :=
  ∀ q, q ∈ E ↔ w⁻¹ * q * w ∈ K

/-- Claim 28121: every regular `C_p^(d+1)` subgroup of the explicit wreath
action is conjugate to the standard diagonal-times-component-translation group. -/
def wreathConjugacyLemma : Prop :=
  ∀ (p d : ℕ), Odd p →
    ∀ E : Subgroup (Equiv.Perm (WreathVertex p d)),
      E ≤ dihedralWreathGroup p d →
      elementaryAbelianRegularSubgroup E →
      ∃ w : Equiv.Perm (WreathVertex p d),
        w ∈ dihedralWreathGroup p d ∧
          conjugateSubgroupMembership E (standardProductGroup p d) w

abbrev RegularModuleCarrier (p d : ℕ) := ComponentPower p d → ZMod p

def regularModuleAction {p d : ℕ} (a : ComponentPower p d)
    (m : RegularModuleCarrier p d) : RegularModuleCarrier p d :=
  fun x => m (x - a)

/-- Claim 28123: all cocycles of the regular permutation module are
coboundaries. -/
def regularPermutationModuleCocycles : Prop :=
  ∀ (p d : ℕ), Nat.Prime p →
    ∀ f : ComponentPower p d → RegularModuleCarrier p d,
      (∀ a b : ComponentPower p d,
        f (a + b) = f a + regularModuleAction a (f b)) →
      ∃ h : RegularModuleCarrier p d,
        ∀ a : ComponentPower p d,
          f a = regularModuleAction a h - h

end MathlibPlus.Open.ResearchFormalization
