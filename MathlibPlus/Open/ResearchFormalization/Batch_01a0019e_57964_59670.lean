import Mathlib

namespace MathlibPlus.Open.ResearchFormalization

/-- The additive Cayley adjacency relation used by the packet's abelian Cayley claims. -/
def addCayleyAdj {G : Type} [AddGroup G] (S : Set G) (u v : G) : Prop :=
  u ≠ v ∧ v - u ∈ S

def inverseClosedSet {G : Type} [AddGroup G] (S : Set G) : Prop :=
  ∀ x, x ∈ S ↔ -x ∈ S

/-- The Hénon polynomial on the three-dimensional vector carrier in Claims 57964--57967. -/
def henonF (p : ℕ) (z : Fin 3 → ZMod p) : Fin 3 → ZMod p :=
  ![z 0 ^ 2 + z 0 * z 1 * z 2, z 1 ^ 2, z 2 ^ 2]

def henonW (p : ℕ) (d : Fin 3 → ZMod p) :
    Submodule (ZMod p) (Fin 3 → ZMod p) :=
  Submodule.span (ZMod p)
    {u | ∃ a : Fin 3 → ZMod p,
      u = henonF p (a + d) - henonF p a - henonF p d ∨
      u = henonF p (a - d) - henonF p a - henonF p (-d)}

def claim57964 : Prop :=
  ∀ (p : ℕ), 5 ≤ p → Nat.Prime p →
    ∀ d : Fin 3 → ZMod p,
      henonF p d ∈ henonW p d ∧ henonW p (-d) = henonW p d

def henonSlice (S : Set ((Fin 3 → ZMod p) × (Fin 3 → ZMod p)))
    (d : Fin 3 → ZMod p) : Set (Fin 3 → ZMod p) :=
  {u | (u, d) ∈ S}

def unionOfCosets {G : Type} [AddCommGroup G] [Module (ZMod p) G]
    (W : Submodule (ZMod p) G) (A : Set G) : Prop :=
  ∀ u, u ∈ A → ∀ w, w ∈ W → u + w ∈ A

def henonQ (p : ℕ) (x z : Fin 3 → ZMod p) :
    (Fin 3 → ZMod p) × (Fin 3 → ZMod p) :=
  (z, x + henonF p z)

def henonQFun (p : ℕ) :
    ((Fin 3 → ZMod p) × (Fin 3 → ZMod p)) →
      ((Fin 3 → ZMod p) × (Fin 3 → ZMod p)) :=
  fun u => henonQ p u.1 u.2

def claim57966 : Prop :=
  ∀ (p : ℕ), 5 ≤ p → Nat.Prime p →
    ∀ (S : Set ((Fin 3 → ZMod p) × (Fin 3 → ZMod p))),
      (0 : (Fin 3 → ZMod p) × (Fin 3 → ZMod p)) ∉ S →
      (∀ d, d ≠ 0 → unionOfCosets (henonW p d) (henonSlice S d)) →
      Function.Bijective (henonQFun p) ∧
        (∀ u v,
          addCayleyAdj S u v ↔
            addCayleyAdj S (henonQFun p u) (henonQFun p v)) ∧
        (inverseClosedSet S →
          ∀ u v,
            addCayleyAdj S u v ↔
              addCayleyAdj S (henonQFun p u) (henonQFun p v))

def henonPaddedSlice (S : Set (((Fin 3 → ZMod p) × (Fin 3 → ZMod p)) ×
    (Fin (r - 6) → ZMod p)))
    (d : Fin 3 → ZMod p) (c : Fin (r - 6) → ZMod p) :
    Set (Fin 3 → ZMod p) :=
  {u | ((u, d), c) ∈ S}

def henonQbar (p r : ℕ)
    (x z : Fin 3 → ZMod p) (c : Fin (r - 6) → ZMod p) :
    ((Fin 3 → ZMod p) × (Fin 3 → ZMod p)) × (Fin (r - 6) → ZMod p) :=
  ((z, x + henonF p z), c)

def henonQbarFun (p r : ℕ) :
    (((Fin 3 → ZMod p) × (Fin 3 → ZMod p)) ×
      (Fin (r - 6) → ZMod p)) →
      (((Fin 3 → ZMod p) × (Fin 3 → ZMod p)) ×
        (Fin (r - 6) → ZMod p)) :=
  fun u => henonQbar p r u.1.1 u.1.2 u.2

def claim57967 : Prop :=
  ∀ (p r : ℕ), 5 ≤ p → Nat.Prime p → 6 ≤ r →
    ∀ (S : Set (((Fin 3 → ZMod p) × (Fin 3 → ZMod p)) ×
      (Fin (r - 6) → ZMod p))),
      (∀ (d : Fin 3 → ZMod p) (c : Fin (r - 6) → ZMod p),
        unionOfCosets (henonW p d) (henonPaddedSlice S d c)) →
      Function.Bijective (henonQbarFun p r) ∧
        (∀ (u v : ((Fin 3 → ZMod p) × (Fin 3 → ZMod p)) ×
            (Fin (r - 6) → ZMod p)),
          addCayleyAdj S u v ↔
            addCayleyAdj S (henonQbarFun p r u) (henonQbarFun p r v)) ∧
        (inverseClosedSet S →
          ∀ (u v : ((Fin 3 → ZMod p) × (Fin 3 → ZMod p)) ×
              (Fin (r - 6) → ZMod p)),
            addCayleyAdj S u v ↔
              addCayleyAdj S (henonQbarFun p r u) (henonQbarFun p r v))

/-- The two-dimensional complete-factor relation in the target of Claim 58989. -/
def cartesianAdj {M : Type} [AddGroup M] (S₀ : Set M)
    (u v : M × ZMod 3) : Prop :=
  (u.2 = v.2 ∧ u.1 ≠ v.1 ∧ v.1 - u.1 ∈ S₀) ∨
    (u.1 = v.1 ∧ u.2 ≠ v.2)

def thetaPow3 {M : Type} [AddCommGroup M] (θ : M ≃+ M)
    (i : ZMod 3) (x : M) : M :=
  (θ^[ZMod.val i]) x

def semidirectMul {M : Type} [AddCommGroup M] (θ : M ≃+ M)
    (u v : M × ZMod 3) : M × ZMod 3 :=
  (u.1 + thetaPow3 θ u.2 v.1, u.2 + v.2)

def semidirectInv {M : Type} [AddCommGroup M] (θ : M ≃+ M)
    (u : M × ZMod 3) : M × ZMod 3 :=
  (-thetaPow3 θ (-u.2) u.1, -u.2)

def semidirectAdj {M : Type} [AddCommGroup M]
    (θ : M ≃+ M) (S : Set (M × ZMod 3))
    (u v : M × ZMod 3) : Prop :=
  u ≠ v ∧ ∃ s, s ∈ S ∧ semidirectMul θ u s = v

def semidirectInverseClosed {M : Type} [AddCommGroup M]
    (θ : M ≃+ M) (S : Set (M × ZMod 3)) : Prop :=
  ∀ u, u ∈ S ↔ semidirectInv θ u ∈ S

def semidirectB {M : Type} [AddCommGroup M]
    (θ : M ≃+ M) (a : M) (i : ZMod 3) : M :=
  if i = 0 then 0 else if i = 1 then a else a + θ a

def semidirectShift {M : Type} [AddCommGroup M]
    (θ : M ≃+ M) (a : M) (u : M × ZMod 3) : M × ZMod 3 :=
  (u.1 - semidirectB θ a u.2, u.2)

def claim58989 : Prop :=
  ∀ (M : Type) [AddCommGroup M] [Fintype M]
    (θ : M ≃+ M),
    (∀ x, θ (θ (θ x)) = x) →
    (∀ x, θ x - x = 0 → x = 0) →
    ∀ (S₀ S₁ S₂ : Set M) (S : Set (M × ZMod 3)) (a : M),
      (∀ x i, (x, i) ∈ S ↔
        (i = 0 ∧ x ∈ S₀) ∨ (i = 1 ∧ x ∈ S₁) ∨ (i = 2 ∧ x ∈ S₂)) →
      inverseClosedSet S₀ →
      semidirectInverseClosed θ S →
      (∀ x, x ∈ S₂ ↔ ∃ y, y ∈ S₁ ∧ x = -(θ (θ y))) →
      (∀ x, x ∈ S₀ ↔ θ x ∈ S₀) →
      (∀ x, x ∈ S₁ ↔ x = a) →
      Function.Bijective (semidirectShift θ a) ∧
        ∀ u v,
          semidirectAdj θ S u v ↔
            cartesianAdj S₀ (semidirectShift θ a u) (semidirectShift θ a v)

/-- The elementary-Sylow premise is expressed by exponent p on every Sylow p subgroup. -/
def elementarySylows (G : Type) [Group G] [Fintype G] : Prop :=
  ∀ p : ℕ, p.Prime → ∀ P : Sylow p G,
    ∀ x : P.toSubgroup, x ^ p = 1

def flagPreserves {G : Type} [Group G]
    (L U : Subgroup G) (α : G ≃* G) : Prop :=
  (∀ x, x ∈ L ↔ α x ∈ L) ∧ (∀ x, x ∈ U ↔ α x ∈ U)

def flagAut (G : Type) [Group G] (L U : Subgroup G) :=
  {α : G ≃* G // flagPreserves L U α}

def sectionSubgroup {G : Type} [Group G]
    (L U : Subgroup G) : Subgroup U :=
  L.comap U.subtype

def claim59001 : Prop :=
  ∀ (G : Type) [CommGroup G] [Fintype G],
    elementarySylows G →
    ∀ (L U : Subgroup G), L ≤ U →
      ∀ f : (U ⧸ sectionSubgroup L U) ≃* (U ⧸ sectionSubgroup L U),
        ∃ α : flagAut G L U,
          ∀ u : U,
            f (QuotientGroup.mk' (sectionSubgroup L U) u) =
              QuotientGroup.mk' (sectionSubgroup L U)
                ⟨α.1 (u : G), (α.2.2 (u : G)).mp u.property⟩

/-- The displayed flags and the two displayed actions in Claims 59002 and 59005. -/
abbrev flagV : Type := Fin 3 → ZMod 3

def flagE₁ : flagV := ![1, 0, 0]
def flagE₂ : flagV := ![0, 1, 0]
def flagE₃ : flagV := ![0, 0, 1]

def flagU₁ : Submodule (ZMod 3) flagV :=
  Submodule.span (ZMod 3) {flagE₁, flagE₂}

def flagU₂ : Submodule (ZMod 3) flagV :=
  Submodule.span (ZMod 3) {flagE₁, flagE₃}

def flagF₁ (v : flagV) : flagV := ![-v 0, v 1, v 2]
def flagF₂ (v : flagV) : flagV := v

def claim59002 : Prop :=
  (∃ g₁ : flagV ≃ₗ[ZMod 3] flagV,
    ∀ v, v ∈ flagU₁ → flagF₁ v ∈ flagU₁ ∧ g₁ v = flagF₁ v) ∧
  (∃ g₂ : flagV ≃ₗ[ZMod 3] flagV,
    ∀ v, v ∈ flagU₂ → flagF₂ v ∈ flagU₂ ∧ g₂ v = flagF₂ v) ∧
  ¬∃ g : flagV ≃ₗ[ZMod 3] flagV,
    (∀ v, v ∈ flagU₁ → g v = flagF₁ v) ∧
    (∀ v, v ∈ flagU₂ → g v = flagF₂ v)

def paddedKernel (L : Type) [AddCommGroup L] [Module (ZMod 3) L] :
    Set (L × flagV) :=
  {x | x.2 = 0}

def paddedFlag (L : Type) [AddCommGroup L] [Module (ZMod 3) L]
    (U : Submodule (ZMod 3) flagV) : Set (L × flagV) :=
  {x | x.2 ∈ U}

def claim59005 : Prop :=
  ∀ (L : Type) [AddCommGroup L] [Module (ZMod 3) L],
    ¬∃ g : (L × flagV) ≃ₗ[ZMod 3] (L × flagV),
      (∀ x, x ∈ paddedKernel L ↔ g x ∈ paddedKernel L) ∧
      (∀ x, x ∈ paddedFlag L flagU₁ ↔ g x ∈ paddedFlag L flagU₁) ∧
      (∀ x, x ∈ paddedFlag L flagU₂ ↔ g x ∈ paddedFlag L flagU₂) ∧
      (∀ v, v ∈ flagU₁ →
        g (0, v) - (0, flagF₁ v) ∈ paddedKernel L) ∧
      (∀ v, v ∈ flagU₂ →
        g (0, v) - (0, flagF₂ v) ∈ paddedKernel L)

def rigidityC (c : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  fun i j =>
    if i = 0 then
      if j = 0 then 0 else if j = 1 then -1 else 0
    else if i = 1 then
      if j = 0 then 1 else if j = 1 then -2 * c else 0
    else 0

def matrixSymmetric2 (G : Matrix (Fin 2) (Fin 2) ℝ) : Prop :=
  ∀ i j, G i j = G j i

def matrixPositiveDefinite2 (G : Matrix (Fin 2) (Fin 2) ℝ) : Prop :=
  ∀ v : Fin 2 → ℝ, v ≠ 0 →
    0 < ∑ i, ∑ j, v i * G i j * v j

def rigidityInvariant (c : I → ℝ) (G : Matrix (Fin 2) (Fin 2) ℝ) : Prop :=
  ∀ i a b,
    (∑ u, ∑ v,
      rigidityC (c i) u a * G u v * rigidityC (c i) v b) = G a b

def claim59659 : Prop :=
  ∀ (I : Type) (c : I → ℝ), Nonempty I →
    (∃ G : Matrix (Fin 2) (Fin 2) ℝ,
      matrixSymmetric2 G ∧ matrixPositiveDefinite2 G ∧ rigidityInvariant c G) ↔
    ∃ c₀ : ℝ, |c₀| < 1 ∧ ∀ i, c i = c₀

def claim59658 : Prop :=
  ∀ (E : Set ℝ) (f g : ℝ → ℝ) (a : ℝ),
    E.Countable → Continuous f → Continuous g →
    (∀ x, x ∉ E →
      DifferentiableAt ℝ f x ∧ DifferentiableAt ℝ g x ∧
        deriv f x = deriv g x) →
    f a = g a → f = g

def claim59663 : Prop :=
  ∀ (f g : ℝ → ℝ) (S : Set ℝ) (a : ℝ),
    Differentiable ℝ f → Differentiable ℝ g →
    Continuous (fun x => deriv f x) →
    Continuous (fun x => deriv g x) →
    Dense S → (∀ x, x ∈ S → deriv f x = deriv g x) →
    f a = g a → f = g

abbrev ciGroup (r : ℕ) : Type := (Fin r → ZMod 2) × ZMod 9

def claim59668 : Prop :=
  ∀ (r : ℕ) (H : AddSubgroup (ciGroup r))
    (S : Set (ciGroup r)),
    inverseClosedSet S →
    (S = {x | x ∈ H ∧ x ≠ 0} ∨ S = {x | x ∉ H}) →
    ∀ (T : Set (ciGroup r)),
      (∀ x, x ∈ T → x ≠ 0) → inverseClosedSet T →
      (∃ φ : ciGroup r → ciGroup r,
        Function.Bijective φ ∧
          ∀ u v, addCayleyAdj S u v ↔
            addCayleyAdj T (φ u) (φ v)) →
      ∃ α : ciGroup r ≃+ ciGroup r,
        ∀ x, x ∈ S ↔ α x ∈ T

def fiberShift {V : Type} [AddGroup V]
    (f : V → ZMod 4) (x : ZMod 4 × V) : ZMod 4 × V :=
  (x.1 + f x.2, x.2)

def exponentThree {V : Type} [AddCommGroup V] : Prop :=
  ∀ x : V, x + x + x = 0

def claim59670 : Prop :=
  (∀ (V : Type) [AddCommGroup V], exponentThree (V := V) →
    ∀ (f : V → ZMod 4) (S T : Set (ZMod 4 × V)),
      (∀ a v w,
        (a, w) ∈ S ↔
          (a + f (v + w) - f v, w) ∈ T) →
      S = T) ∧
  (∀ r : ℕ, ∀ (f : (Fin r → ZMod 3) → ZMod 4)
      (S T : Set (ZMod 4 × (Fin r → ZMod 3))),
      (∀ x, x ∈ S → x ≠ 0) → (∀ x, x ∈ T → x ≠ 0) →
      (Function.Bijective (fiberShift f)) ∧
      ((∀ u v,
          addCayleyAdj S u v ↔
            addCayleyAdj T (fiberShift f u) (fiberShift f v)) →
        S = T))

end MathlibPlus.Open.ResearchFormalization
