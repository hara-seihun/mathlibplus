import Mathlib

namespace MathlibPlus.Open.Groups.PrimeKernel

/-- The quotient projection `G → G/N`. -/
def quotientProjection
    (G : Type*) [AddCommGroup G]
    (N : AddSubgroup G) : G →+ G ⧸ N :=
  QuotientAddGroup.mk' N

/-- Normalization of a section-like map into the prime kernel. -/
def normalized
    {G : Type*} [AddCommGroup G]
    (N : AddSubgroup G) (s : (G ⧸ N) → N) : Prop :=
  s 0 = 0

/-- Claim 29932: the block translation `f_s(x)=x+s(π(x))`. -/
def primeKernelBlockTranslation
    {G : Type*} [AddCommGroup G] [Finite G]
    (p : ℕ) (N : AddSubgroup G)
    (hp : p.Prime) (hcyclic : IsAddCyclic N)
    (hcard : Nat.card N = p)
    (s : (G ⧸ N) → N) (hs : normalized N s) : G → G :=
  fun x => x + (s (quotientProjection G N x) : G)

/-- The linearity locus from Claim 29934. -/
def linearityLocus
    {G : Type*} [AddCommGroup G]
    (N : AddSubgroup G) (s : (G ⧸ N) → N) : Set (G ⧸ N) :=
  {h | ∀ k : G ⧸ N, s (h + k) = s h + s k}

/-- Closure under the additive subgroup operations, stated for a concrete set. -/
def isAddSubgroupSet
    {H : Type*} [AddCommGroup H] (S : Set H) : Prop :=
  0 ∈ S ∧
    (∀ x y, x ∈ S → y ∈ S → x + y ∈ S) ∧
    (∀ x, x ∈ S → -x ∈ S)

/-- The restriction of a function to a subgroup is additive, without an arbitrary witness. -/
def restrictionIsAddMonoidHom
    {H N : Type*} [AddCommGroup H] [AddCommGroup N]
    (S : Set H) (f : H → N) : Prop :=
  f 0 = 0 ∧
    ∀ x y, x ∈ S → y ∈ S → f (x + y) = f x + f y

/-- Claim 29934: `L_s` is a subgroup and the restricted map is a homomorphism. -/
def linearityLocusIsSubgroupClaim
    {G : Type*} [AddCommGroup G] [Finite G]
    (p : ℕ) (N : AddSubgroup G)
    (hp : p.Prime) (hcyclic : IsAddCyclic N)
    (hcard : Nat.card N = p)
    (s : (G ⧸ N) → N) (hs : normalized N s) : Prop :=
  isAddSubgroupSet (linearityLocus N s) ∧
    restrictionIsAddMonoidHom (linearityLocus N s) s

end MathlibPlus.Open.Groups.PrimeKernel
