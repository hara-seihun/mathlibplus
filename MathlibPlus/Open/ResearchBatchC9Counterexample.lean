import Mathlib

namespace MathlibPlus.Open.ResearchBatchC9Counterexample

abbrev C9 := ZMod 9
abbrev C3 := ZMod 3
abbrev C9C3 := C9 × C3

/-- The kernel `0 × C₃` in the product group. -/
def kernelC9C3 : AddSubgroup C9C3 :=
  AddSubgroup.prod (⊥ : AddSubgroup C9) (⊤ : AddSubgroup C3)

/-- The section with values 0,0,0,1,1,1,2,2,2 on `C₉`. -/
def sectionC9 (x : C9) : C3 :=
  (x.val / 3 : C3)

/-- Its linearity locus. -/
def sectionC9LinearityLocus : Set C9 :=
  {h | ∀ k : C9, sectionC9 (h + k) = sectionC9 h + sectionC9 k}

/-- The block translation `f_s(x,z)=(x,z+s(x))`. -/
def blockTranslationC9C3 : C9C3 → C9C3 :=
  fun z => (z.1, z.2 + sectionC9 z.1)

/-- The inverse-closed connection set. -/
def connectionSetC9C3 : Set C9C3 :=
  {(3, 0), (6, 0)}

/-- The characteristic subgroup `3G`, as a set of triples' multiples. -/
def threeMultiplesC9C3 : Set C9C3 :=
  {z | ∃ y : C9C3, z = 3 • y}

/-- The Cayley adjacency relation determined by a difference set. -/
def cayleyDifference
    {G : Type*} [AddGroup G]
    (S : Set G) (x y : G) : Prop :=
  y - x ∈ S

/-- The sharp `C₉×C₃` counterexample, including its Cayley-isomorphism property. -/
def sharpC9C3CounterexampleClaim : Prop :=
  (∀ z : C9C3, z ∈ kernelC9C3 ↔ z.1 = 0) ∧
    sectionC9 0 = 0 ∧
    sectionC9LinearityLocus = ({0, 3, 6} : Set C9) ∧
    sectionC9 3 = 1 ∧
    (∀ phi : C9 →+ C3, phi 3 = 0) ∧
    (∀ z : C9C3, z ∈ connectionSetC9C3 → -z ∈ connectionSetC9C3) ∧
    connectionSetC9C3 ⊆ threeMultiplesC9C3 ∧
    blockTranslationC9C3 '' connectionSetC9C3 = {(3, 1), (6, 2)} ∧
    Disjoint (blockTranslationC9C3 '' connectionSetC9C3) threeMultiplesC9C3 ∧
    (¬ ∃ alpha : C9C3 ≃+ C9C3,
      alpha '' connectionSetC9C3 = blockTranslationC9C3 '' connectionSetC9C3) ∧
    Function.Bijective blockTranslationC9C3 ∧
    (∀ x y : C9C3,
      cayleyDifference connectionSetC9C3 x y ↔
        cayleyDifference (blockTranslationC9C3 '' connectionSetC9C3)
          (blockTranslationC9C3 x) (blockTranslationC9C3 y))

end MathlibPlus.Open.ResearchBatchC9Counterexample
