import Mathlib

namespace MathlibPlus.Open.Combinatorics.SingletonSupport

/-- The zero/one/many register for an equality-comparable target-code type. -/
inductive SingletonSupport (K : Type*) where
  | zero
  | many
  | one (k : K)

namespace SingletonSupport

variable {K : Type*} [DecidableEq K] {E : Type*} [DecidableEq E]

def merge : SingletonSupport K → SingletonSupport K → SingletonSupport K
  | .zero, q => q
  | .many, _ => .many
  | .one k, .zero => .one k
  | .one k, .many => .many
  | .one k, .one l => if k = l then .one k else .many

noncomputable def ofFinset (A : Finset K) : SingletonSupport K := by
  classical
  by_cases h₀ : A = ∅
  · exact .zero
  · by_cases h₁ : ∃ k, A = {k}
    · exact .one (Classical.choose h₁)
    · exact .many

def singletonSupportRegisterClaim : Prop :=
  ∀ q : SingletonSupport K,
    q = .zero ∨ q = .many ∨ ∃ k, q = .one k

def zeroOneManyMergeClaim : Prop :=
  (∀ (q : SingletonSupport K), merge .zero q = q) ∧
    (∀ (q : SingletonSupport K), merge .many q = .many) ∧
      (∀ (k l : K), merge (.one k) (.one l) =
        if k = l then .one k else .many)

def ofFinsetUnionClaim : Prop :=
  ∀ A B : Finset K,
    ofFinset (A ∪ B) = merge (ofFinset A) (ofFinset B)

/-- The register exported by a finite unresolved event subfamily. -/
noncomputable def eventSingleton (κ : E → K) (U : Finset E) : SingletonSupport K :=
  ofFinset (U.image κ)

def exactSingletonEventTest (κ : E → K) : Prop :=
  ∀ (U : Finset E) (k : K),
    eventSingleton κ U = .one k ↔ U.image κ = {k}

/-- Folding the registers of an ordered finite partition. -/
noncomputable def eventPartitionFold (κ : E → K) (parts : List (Finset E)) :
    SingletonSupport K :=
  parts.foldl (fun q U => merge q (eventSingleton κ U)) .zero

def partitionCompositionalEventFold (κ : E → K) : Prop :=
  ∀ (parts : List (Finset E)) (U : Finset E),
    List.Pairwise (fun A B : Finset E => Disjoint A B) parts →
    U = parts.foldl (fun acc P => acc ∪ P) ∅ →
    eventPartitionFold κ parts = eventSingleton κ U

end SingletonSupport
end MathlibPlus.Open.Combinatorics.SingletonSupport
