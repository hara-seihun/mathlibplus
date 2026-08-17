import Mathlib

namespace MathlibPlus.Open.ResearchFormalization.R1414

noncomputable section

abbrev R1414Two := Equiv.Perm (Fin 2)
abbrev R1414Top (n : ℕ) := Equiv.Perm (Fin n) × R1414Two
abbrev R1414FiberIndex (n : ℕ) := Fin 2 × Fin n
abbrev R1414Kernel (n : ℕ) := R1414FiberIndex n → Multiplicative (ZMod 2)

/-- The action of `S_n × S_2` on the side-label fibers. -/
def r1414FiberPerm {n : ℕ} (g : R1414Top n) :
    Equiv.Perm (R1414FiberIndex n) :=
  Equiv.prodCongr g.2 g.1

def r1414FiberPermHom {n : ℕ} :
    R1414Top n →* Equiv.Perm (R1414FiberIndex n) where
  toFun := r1414FiberPerm
  map_one' := by
    ext x <;> simp [r1414FiberPerm]
  map_mul' := by
    intro g h
    ext x <;> simp only [r1414FiberPerm, Equiv.prodCongr_apply,
      Equiv.Perm.mul_apply]
    · rfl
    · rfl

def r1414KernelActionEquiv {n : ℕ} (g : R1414Top n) :
    R1414Kernel n ≃* R1414Kernel n :=
  MulEquiv.arrowCongr (r1414FiberPerm g)
    (MulEquiv.refl (Multiplicative (ZMod 2)))

def r1414KernelAction {n : ℕ} :
    R1414Top n →* MulAut (R1414Kernel n) where
  toFun := r1414KernelActionEquiv
  map_one' := by
    apply MulEquiv.ext
    intro f
    funext x
    change f ((r1414FiberPerm (1 : R1414Top n)).symm x) = f x
    change f ((r1414FiberPermHom (1 : R1414Top n)).symm x) = f x
    rw [r1414FiberPermHom.map_one]
    rw [show (1 : Equiv.Perm (R1414FiberIndex n)).symm = 1 by rfl]
    simp
  map_mul' g h := by
    apply MulEquiv.ext
    intro f
    funext x
    have hp : r1414FiberPerm (g * h) =
        r1414FiberPerm g * r1414FiberPerm h :=
      r1414FiberPermHom.map_mul g h
    change f ((r1414FiberPerm (g * h)).symm x) =
      (r1414KernelActionEquiv g (r1414KernelActionEquiv h f)) x
    rw [hp]
    simp [r1414KernelActionEquiv, Equiv.Perm.mul_def, Equiv.trans_apply]

abbrev R1414Semidirect (n : ℕ) :=
  SemidirectProduct (R1414Kernel n) (R1414Top n)
    (r1414KernelAction (n := n))
abbrev R1414AutModel (n : ℕ) := R1414Two × R1414Semidirect n

abbrev R1414YVertex (n : ℕ) := Fin 2 × (Fin n × Fin 2)
abbrev R1414Vertex (n : ℕ) := Fin 2 × R1414YVertex n

def r1414YRelation {n : ℕ} (x y : R1414YVertex n) : Prop :=
  x.1 ≠ y.1 ∧ x.2.1 ≠ y.2.1

def r1414YGraph (n : ℕ) : SimpleGraph (R1414YVertex n) :=
  SimpleGraph.fromRel (r1414YRelation (n := n))

def r1414OuterRelation {n : ℕ} (x y : R1414Vertex n) : Prop :=
  x.1 ≠ y.1 ∧ x.2 = y.2

def r1414ProductRelation {n : ℕ} (x y : R1414Vertex n) : Prop :=
  r1414OuterRelation x y ∨
    (x.1 = y.1 ∧ r1414YRelation x.2 y.2)

def r1414ProductGraph (n : ℕ) : SimpleGraph (R1414Vertex n) :=
  SimpleGraph.fromRel (r1414ProductRelation (n := n))

def r1414GraphAutomorphism {V : Type*} (G : SimpleGraph V)
    (e : Equiv.Perm V) : Prop :=
  ∀ x y, G.Adj x y ↔ G.Adj (e x) (e y)

def r1414OuterPerfectMatching (n : ℕ) : Prop :=
  ∀ (x : R1414Vertex n), ∃! y, r1414OuterRelation x y

def r1414OuterMatchingPreserved {n : ℕ}
    (e : Equiv.Perm (R1414Vertex n)) : Prop :=
  ∀ x y, r1414OuterRelation x y ↔
    r1414OuterRelation (e x) (e y)

def r1414OuterContraction {n : ℕ}
    (e : Equiv.Perm (R1414Vertex n)) : Prop :=
  ∃ c : R1414Two, ∃ f : Equiv.Perm (R1414YVertex n),
    r1414GraphAutomorphism (r1414YGraph n) f ∧
      ∀ (o : Fin 2) (y : R1414YVertex n),
        e (o, y) = (c o, f y)

/-- Claim 36936: the outer Cartesian matching is intrinsic, contracts to the
crown-fiber graph, and the endpoint choice is global. -/
def claim36936 : Prop :=
  ∀ n : ℕ, 3 ≤ n →
    SimpleGraph.Connected (r1414YGraph n) ∧
    r1414OuterPerfectMatching n ∧
    ∀ e : Equiv.Perm (R1414Vertex n),
      r1414GraphAutomorphism (r1414ProductGraph n) e →
      r1414OuterMatchingPreserved e ∧ r1414OuterContraction e

abbrev R1414Binary := ZMod 2 × (ZMod 2 × ZMod 2)
abbrev R1414CayleyGroup (n : ℕ) :=
  Multiplicative (R1414Binary × ZMod n)

def r1414E1 : R1414Binary := (1, (0, 0))
def r1414E2 : R1414Binary := (0, (1, 0))
def r1414E3 : R1414Binary := (0, (0, 1))

def r1414ConnectionSet (n : ℕ) : Set (R1414CayleyGroup n) :=
  {g | ∃ z : ZMod n, z ≠ 0 ∧
    g = Multiplicative.ofAdd (r1414E1, z)} ∪
  {g | ∃ z : ZMod n, z ≠ 0 ∧
    g = Multiplicative.ofAdd (r1414E2, z)} ∪
  {Multiplicative.ofAdd (r1414E3, (0 : ZMod n))}

def r1414CayleyGraph (n : ℕ) :
    SimpleGraph (R1414CayleyGroup n) :=
  SimpleGraph.mulCayley (r1414ConnectionSet n)

def r1414GraphAutSubgroup {G : Type*} (Γ : SimpleGraph G) :
    Subgroup (Equiv.Perm G) :=
  { carrier := {e | r1414GraphAutomorphism Γ e}
    one_mem' := by
      intro x y
      simp
    mul_mem' := by
      intro e f he hf x y
      exact (hf x y).trans (he (f x) (f y))
    inv_mem' := by
      intro e he x y
      simpa using (he (e⁻¹ x) (e⁻¹ y)).symm }

/-- Claim 36937: the explicit odd cyclic crown-fiber Cayley family has the
stated full graph automorphism group and order. -/
def claim36937 : Prop :=
  ∀ n : ℕ, Odd n → 3 ≤ n →
    ∃ A : Subgroup (Equiv.Perm (R1414CayleyGroup n)),
      (∀ e, e ∈ A ↔
        r1414GraphAutomorphism (r1414CayleyGraph n) e) ∧
      Nonempty (A ≃* R1414AutModel n) ∧
      Nat.card A = 2 ^ (2 * n + 2) * Nat.factorial n

def r1414RegularPermutationSubgroup {Ω : Type*} [Fintype Ω]
    (H : Subgroup (Equiv.Perm Ω)) : Prop :=
  ∀ a b : Ω, ∃! h : H, h.1 a = b

def r1414RegularTopSubgroup {n : ℕ}
    (H : Subgroup (R1414Top n)) : Prop :=
  r1414RegularPermutationSubgroup
    (Subgroup.map (r1414FiberPermHom (n := n)) H)

def r1414NCycle {n : ℕ} (σ : Equiv.Perm (Fin n)) : Prop :=
  σ.IsCycle ∧ σ.support = Finset.univ

def r1414ProjectionFacts {n : ℕ}
    (H : Subgroup (R1414Top n)) : Prop :=
  let P := Subgroup.map (MonoidHom.fst (Equiv.Perm (Fin n)) R1414Two) H
  let Q := Subgroup.map (MonoidHom.snd (Equiv.Perm (Fin n)) R1414Two) H
  (r1414RegularPermutationSubgroup P ∧
      ∃ σ : Equiv.Perm (Fin n), r1414NCycle σ ∧
        P = Subgroup.closure ({σ} : Set (Equiv.Perm (Fin n)))) ∧
    r1414RegularPermutationSubgroup Q ∧ Q = ⊤

def r1414RegularTopCopy {n : ℕ}
    (H : Subgroup (R1414Top n)) : Prop :=
  r1414RegularTopSubgroup H ∧
    Nonempty ((Multiplicative (ZMod n) × R1414Two) ≃* H)

def r1414ConjugateTopSubgroups {n : ℕ}
    (H K : Subgroup (R1414Top n)) : Prop :=
  ∃ g : R1414Top n, ∀ x : R1414Top n,
    x ∈ K ↔ ∃ h : R1414Top n, h ∈ H ∧ x = g * h * g⁻¹

def r1414AllNCyclesConjugate (n : ℕ) : Prop :=
  ∀ σ τ : Equiv.Perm (Fin n),
    r1414NCycle σ → r1414NCycle τ →
    ∃ g : Equiv.Perm (Fin n), g * σ * g⁻¹ = τ

/-- Claim 36939: the crown top group has exactly one regular-copy class;
its projections are the cyclic and unique two-point regular factors. -/
def claim36939 : Prop :=
  ∀ n : ℕ, 3 ≤ n →
    (∃ H : Subgroup (R1414Top n), r1414RegularTopCopy H ∧
      r1414ProjectionFacts H) ∧
    (∀ H K : Subgroup (R1414Top n),
      r1414RegularTopCopy H → r1414RegularTopCopy K →
      r1414ConjugateTopSubgroups H K) ∧
    (∀ H : Subgroup (R1414Top n),
      r1414RegularTopCopy H → r1414ProjectionFacts H) ∧
    r1414AllNCyclesConjugate n

end

end MathlibPlus.Open.ResearchFormalization.R1414
