import Mathlib

namespace MathlibPlus.Open.ResearchFormalizationBatch01_01a0014f

attribute [local instance] Classical.propDecidable

abbrev F3 := ZMod 3
abbrev QuadraticBase := F3 × F3
abbrev QuadraticV := F3 × F3 × F3

def quadratic_base (b : QuadraticBase) : QuadraticBase :=
  (b.1, b.2 + b.1 ^ 2)

def quadratic_section (s : QuadraticBase → F3) : Equiv.Perm QuadraticV :=
  { toFun := fun v =>
      (v.1 + s (v.2.1, v.2.2), v.2.1, v.2.2 + v.2.1 ^ 2)
    invFun := fun v =>
      (v.1 - s (v.2.1, v.2.2 - v.2.1 ^ 2),
        v.2.1, v.2.2 - v.2.1 ^ 2)
    left_inv := by
      rintro ⟨z, x, y⟩
      simp [sub_eq_add_neg, add_assoc, add_left_comm, add_comm]
    right_inv := by
      rintro ⟨z, x, y⟩
      simp [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] }

def quadratic_pure_lift : Equiv.Perm QuadraticV :=
  quadratic_section (fun _ => 0)

def quadratic_translation (a : QuadraticV) : Equiv.Perm QuadraticV :=
  { toFun := fun v =>
      (v.1 + a.1, v.2.1 + a.2.1, v.2.2 + a.2.2)
    invFun := fun v =>
      (v.1 - a.1, v.2.1 - a.2.1, v.2.2 - a.2.2)
    left_inv := by
      rintro ⟨z, x, y⟩
      simp [sub_eq_add_neg, add_assoc, add_left_comm, add_comm]
    right_inv := by
      rintro ⟨z, x, y⟩
      simp [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] }

def regular_translation_group : Subgroup (Equiv.Perm QuadraticV) :=
  Subgroup.closure (Set.range quadratic_translation)

def conjugate_set {α : Type*} [Group α] (f : α) (H : Subgroup α) : Set α :=
  {g | ∃ h : H, g = f * (h : α) * f⁻¹}

def quadratic_group (s : QuadraticBase → F3) : Subgroup (Equiv.Perm QuadraticV) :=
  Subgroup.closure
    (regular_translation_group.carrier ∪
      conjugate_set (quadratic_section s) regular_translation_group)

def normalized_shift (s : QuadraticBase → F3) : Prop :=
  s (0, 0) = 0

def normalized_quadratic_section_shift_presentation : Prop :=
  Fintype.card {s : QuadraticBase → F3 // normalized_shift s} = 3 ^ 8 ∧
    3 ^ 8 = 6561 ∧
    (∀ s : QuadraticBase → F3, ∀ z x y : F3,
      quadratic_section s (z, x, y) =
        (z + s (x, y), x, y + x ^ 2)) ∧
    quadratic_base (0, 0) = (0, 0) ∧
    (∀ x y : F3, quadratic_base (x, y) = (x, y + x ^ 2)) ∧
    quadratic_pure_lift = quadratic_section (fun _ => 0) ∧
    (∀ s : QuadraticBase → F3,
      quadratic_group s =
        Subgroup.closure
          (regular_translation_group.carrier ∪
            conjugate_set (quadratic_section s) regular_translation_group))

def two_closure {α : Type*} (H : Subgroup (Equiv.Perm α)) : Set (Equiv.Perm α) :=
  {q | ∀ x y : α, ∃ h : H,
      (h : Equiv.Perm α) x = q x ∧ (h : Equiv.Perm α) y = q y}

def pure_lift_failure_condition (s : QuadraticBase → F3) : Prop :=
  ∃ lam : F3, ∃ c : F3 → F3,
    (c 0 = 0) ∧
      (c ≠ (0 : F3 → F3)) ∧
        (¬ Function.Bijective c) ∧
          (∀ x y : F3, s (x, y) = lam * y + c x)

def normalized_pure_lift_failure_classification : Prop :=
  (∀ s : QuadraticBase → F3, normalized_shift s →
    (quadratic_pure_lift ∉ two_closure (quadratic_group s) ↔
      pure_lift_failure_condition s)) ∧
    Fintype.card
        {s : QuadraticBase → F3 //
          normalized_shift s ∧ pure_lift_failure_condition s} = 18 ∧
    Fintype.card
        {c : F3 → F3 //
          c 0 = 0 ∧ c ≠ (0 : F3 → F3) ∧ ¬ Function.Bijective c} = 6 ∧
    Fintype.card F3 = 3 ∧
    (∀ s : QuadraticBase → F3, normalized_shift s →
      ¬ pure_lift_failure_condition s →
        quadratic_pure_lift ∈ two_closure (quadratic_group s))


def step_base {B ι : Type*} (r : ι → Equiv.Perm B) : ι × Bool → Equiv.Perm B
  | (i, true) => r i
  | (i, false) => (r i)⁻¹

def step_voltage {p : ℕ} {B ι : Type*}
    (r : ι → Equiv.Perm B) (beta : ι → B → ZMod p) :
    ι × Bool → B → ZMod p
  | (i, true) => beta i
  | (i, false) => fun b => -beta i ((r i)⁻¹ b)

def word_base {B ι : Type*} (r : ι → Equiv.Perm B) :
    List (ι × Bool) → B → B
  | [], b => b
  | s :: w, b => word_base r w (step_base r s b)

def word_voltage {p : ℕ} {B ι : Type*}
    (r : ι → Equiv.Perm B) (beta : ι → B → ZMod p) :
    List (ι × Bool) → B → ZMod p
  | [], b => 0
  | s :: w, b =>
      step_voltage r beta s b + word_voltage r beta w (step_base r s b)

def lifted_generator {p : ℕ} {B ι : Type*}
    (r : ι → Equiv.Perm B) (beta : ι → B → ZMod p) (i : ι) :
    Equiv.Perm (ZMod p × B) :=
  { toFun := fun zb =>
      (zb.1 + beta i zb.2, r i zb.2)
    invFun := fun zb =>
      (zb.1 - beta i ((r i)⁻¹ zb.2), (r i)⁻¹ zb.2)
    left_inv := by
      rintro ⟨z, b⟩
      simp [sub_eq_add_neg, add_assoc, add_left_comm, add_comm]
    right_inv := by
      rintro ⟨z, b⟩
      simp [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] }

def base_group {B ι : Type*} (r : ι → Equiv.Perm B) : Subgroup (Equiv.Perm B) :=
  Subgroup.closure (Set.range r)

def lifted_group {p : ℕ} {B ι : Type*}
    (r : ι → Equiv.Perm B) (beta : ι → B → ZMod p) :
    Subgroup (Equiv.Perm (ZMod p × B)) :=
  Subgroup.closure (Set.range (lifted_generator r beta))

def orbit_set {α : Type*} (H : Subgroup (Equiv.Perm α)) (x : α) : Set α :=
  {y | ∃ h : H, (h : Equiv.Perm α) x = y}

def base_orbit {B ι : Type*} (r : ι → Equiv.Perm B) (b0 : B) : Set B :=
  orbit_set (base_group r) b0

def lifted_orbit {p : ℕ} {B ι : Type*}
    (r : ι → Equiv.Perm B) (beta : ι → B → ZMod p) (x : ZMod p × B) :
    Set (ZMod p × B) :=
  orbit_set (lifted_group r beta) x

def chosen_paths {B ι : Type*} (r : ι → Equiv.Perm B) (b0 : B)
    (O : Set B)
    (paths : ∀ b : {b // b ∈ O}, List (ι × Bool)) : Prop :=
  ∀ b, word_base r (paths b) b0 = b.1

def path_potential {p : ℕ} {B ι : Type*}
    (r : ι → Equiv.Perm B) (beta : ι → B → ZMod p) (b0 : B)
    (O : Set B)
    (paths : ∀ b : {b // b ∈ O}, List (ι × Bool)) :
    {b // b ∈ O} → ZMod p :=
  fun b => word_voltage r beta (paths b) b0

def loop_voltage_subgroup {p : ℕ} {B ι : Type*}
    (r : ι → Equiv.Perm B) (beta : ι → B → ZMod p) (b0 : B) :
    AddSubgroup (ZMod p) :=
  AddSubgroup.closure
    {v | ∃ w : List (ι × Bool),
      word_base r w b0 = b0 ∧ word_voltage r beta w b0 = v}

def potential_component {p : ℕ} {B : Type*}
    (O : Set B) (t : {b // b ∈ O} → ZMod p)
    (W : AddSubgroup (ZMod p)) (a : ZMod p) : Set (ZMod p × B) :=
  {x | ∃ b : {b // b ∈ O}, ∃ w : ZMod p,
    w ∈ W ∧ x = (a + t b + w, b.1)}

def potential_graph {p : ℕ} {B : Type*}
    (O : Set B) (t : {b // b ∈ O} → ZMod p) (a : ZMod p) :
    Set (ZMod p × B) :=
  {x | ∃ b : {b // b ∈ O}, x = (a + t b, b.1)}

def saturated_component {p : ℕ} {B : Type*} (O : Set B) :
    Set (ZMod p × B) := Set.univ ×ˢ O

def loop_voltage_subgroup_and_path_potential_orbit_formula : Prop :=
  ∀ (p : ℕ) (B : Type*) [Fintype B] (ι : Type*)
    (r : ι → Equiv.Perm B) (beta : ι → B → ZMod p) (b0 : B),
    Nat.Prime p →
    let O := base_orbit r b0
    ∀ (paths : ∀ b : {b // b ∈ O}, List (ι × Bool)),
      chosen_paths r b0 O paths →
      let W := loop_voltage_subgroup r beta b0
      let t := path_potential r beta b0 O paths
      (∀ a : ZMod p,
          lifted_orbit r beta (a, b0) = potential_component O t W a) ∧
        (∀ (z : ZMod p) (b : B) (hb : b ∈ O),
          lifted_orbit r beta (z, b) =
            potential_component O t W (z - t ⟨b, hb⟩)) ∧
        (∀ a a' : ZMod p,
          lifted_orbit r beta (a, b0) = lifted_orbit r beta (a', b0) ↔
            a - a' ∈ W) ∧
        (∀ (b : {b // b ∈ O}) (u v : List (ι × Bool)),
          word_base r u b0 = b.1 → word_base r v b0 = b.1 →
            word_voltage r beta u b0 - word_voltage r beta v b0 ∈ W) ∧
        (∀ w : ZMod p, w ∈ W →
          ∃ u : List (ι × Bool),
            word_base r u b0 = b0 ∧ word_voltage r beta u b0 = w)

def prime_fiber_components_saturated_or_potential_graphs : Prop :=
  ∀ (p : ℕ) (B : Type*) [Fintype B] (ι : Type*)
    (r : ι → Equiv.Perm B) (beta : ι → B → ZMod p) (b0 : B),
    (hp : Nat.Prime p) →
    letI : NeZero p := ⟨hp.ne_zero⟩
    let O := base_orbit r b0
    ∀ (paths : ∀ b : {b // b ∈ O}, List (ι × Bool)),
      chosen_paths r b0 O paths →
      let W := loop_voltage_subgroup r beta b0
      let t := path_potential r beta b0 O paths
      (W = ⊥ ∨ W = ⊤) ∧
        (W = ⊤ →
          (∀ a : ZMod p,
            lifted_orbit r beta (a, b0) = saturated_component O) ∧
          (∀ (z : ZMod p) (b : B) (hb : b ∈ O),
            lifted_orbit r beta (z, b) = saturated_component O)) ∧
        (W = ⊥ →
          (∀ a : ZMod p,
            lifted_orbit r beta (a, b0) = potential_graph O t a) ∧
          (∀ (z : ZMod p) (b : B) (hb : b ∈ O),
            lifted_orbit r beta (z, b) =
              potential_graph O t (z - t ⟨b, hb⟩)) ∧
          (∀ a a' : ZMod p,
            potential_graph O t a = potential_graph O t a' ↔ a = a') ∧
          Fintype.card (ZMod p) = p ∧
          (∀ (b : {b // b ∈ O}) (u v : List (ι × Bool)),
            word_base r u b0 = b.1 → word_base r v b0 = b.1 →
              word_voltage r beta u b0 = word_voltage r beta v b0))

def affine_fiber_function {p : ℕ} {B : Type*}
    (e : (ZMod p)ˣ) (ell : B → ZMod p) (qbar : Equiv.Perm B) :
    ZMod p × B → ZMod p × B :=
  fun zb => ((e : ZMod p) * zb.1 + ell zb.2, qbar zb.2)

def fixes_all_lifted_orbits {p : ℕ} {B ι : Type*}
    (r : ι → Equiv.Perm B) (beta : ι → B → ZMod p)
    (q : ZMod p × B → ZMod p × B) : Prop :=
  ∀ x, lifted_orbit r beta (q x) = lifted_orbit r beta x

def base_orbits_fixed {B ι : Type*}
    (r : ι → Equiv.Perm B) (qbar : Equiv.Perm B) : Prop :=
  ∀ b0 : B, Set.image qbar (base_orbit r b0) = base_orbit r b0

def quiet_component_exists {p : ℕ} {B ι : Type*} [Fintype B]
    (r : ι → Equiv.Perm B) (beta : ι → B → ZMod p) : Prop :=
  ∃ b0 : B,
    let O := base_orbit r b0
    ∃ paths : ∀ b : {b // b ∈ O}, List (ι × Bool),
      chosen_paths r b0 O paths ∧ loop_voltage_subgroup r beta b0 = ⊥

def quiet_equations {p : ℕ} {B ι : Type*} [Fintype B]
    (r : ι → Equiv.Perm B) (beta : ι → B → ZMod p)
    (ell : B → ZMod p) (qbar : Equiv.Perm B) : Prop :=
  ∀ b0 : B,
    let O := base_orbit r b0
    ∀ paths : ∀ b : {b // b ∈ O}, List (ι × Bool),
      chosen_paths r b0 O paths →
      loop_voltage_subgroup r beta b0 = ⊥ →
      let t := path_potential r beta b0 O paths
      ∀ b : {b // b ∈ O},
        ∃ hbq : qbar b.1 ∈ O,
          ell b.1 = t ⟨qbar b.1, hbq⟩ - t b

def exact_affine_orbit_fixation_criterion : Prop :=
  ∀ (p : ℕ) (B : Type*) [Fintype B] (ι : Type*)
    (r : ι → Equiv.Perm B) (beta : ι → B → ZMod p)
    (e : (ZMod p)ˣ) (ell : B → ZMod p) (qbar : Equiv.Perm B),
    Nat.Prime p →
    Function.Bijective (affine_fiber_function e ell qbar) ∧
      (fixes_all_lifted_orbits r beta (affine_fiber_function e ell qbar) ↔
        base_orbits_fixed r qbar ∧
          (quiet_component_exists r beta → e = 1) ∧
            quiet_equations r beta ell qbar)

def affine_repair_set {p : ℕ} {B ι : Type*} [Fintype B]
    (r : ι → Equiv.Perm B) (beta : ι → B → ZMod p) (qbar : Equiv.Perm B) :
    Set (B → ZMod p) :=
  {ell | fixes_all_lifted_orbits r beta
      (affine_fiber_function (1 : (ZMod p)ˣ) ell qbar)}

def quiet_constraint_set {p : ℕ} {B ι : Type*} [Fintype B]
    (r : ι → Equiv.Perm B) (beta : ι → B → ZMod p) (qbar : Equiv.Perm B) :
    Set (B → ZMod p) :=
  {ell | quiet_equations r beta ell qbar}

def quiet_homogeneous_shifts {p : ℕ} {B ι : Type*} [Fintype B]
    (r : ι → Equiv.Perm B) (beta : ι → B → ZMod p) : Set (B → ZMod p) :=
  {h | ∀ b0 : B,
    let O := base_orbit r b0
    ∀ paths : ∀ b : {b // b ∈ O}, List (ι × Bool),
      chosen_paths r b0 O paths →
      loop_voltage_subgroup r beta b0 = ⊥ →
      ∀ b : {b // b ∈ O}, h b.1 = 0}

def affine_repair_set_is_explicit_coset : Prop :=
  ∀ (p : ℕ) (B : Type*) [Fintype B] (ι : Type*)
    (r : ι → Equiv.Perm B) (beta : ι → B → ZMod p) (qbar : Equiv.Perm B),
    Nat.Prime p →
    ((¬ base_orbits_fixed r qbar → affine_repair_set r beta qbar = ∅) ∧
      (base_orbits_fixed r qbar →
        affine_repair_set r beta qbar = quiet_constraint_set r beta qbar) ∧
      (affine_repair_set r beta qbar = ∅ ∨
        ∃ ell₀ : B → ZMod p, ell₀ ∈ affine_repair_set r beta qbar ∧
          ∀ ell : B → ZMod p,
            ell ∈ affine_repair_set r beta qbar ↔
              ∃ h : B → ZMod p,
                h ∈ quiet_homogeneous_shifts r beta ∧ ell = ell₀ + h))

def displacement_subgroup {B : Type*} [AddCommGroup B]
    (q : Equiv.Perm B) : AddSubgroup B :=
  AddSubgroup.closure {d | ∃ t : B, d = t - q t + q 0}

def full_displacement {B : Type*} [AddCommGroup B]
    (q : Equiv.Perm B) : Prop := displacement_subgroup q = ⊤

def displacement_subgroup_of_a_fiber_permutation : Prop :=
  ∀ {B : Type*} [AddCommGroup B] (q : Equiv.Perm B),
    displacement_subgroup q =
        AddSubgroup.closure {d | ∃ t : B, d = t - q t + q 0} ∧
      (full_displacement q ↔ displacement_subgroup q = ⊤)

abbrev F7 := ZMod 7

instance f7_prime : Fact (Nat.Prime 7) := ⟨by norm_num⟩

abbrev F7V := Fin 3 → F7
abbrev F7CodeAmbient := Fin 3 → F7V

def f7_vector (a b c : F7) : F7V := ![a, b, c]

def f7_line (v : F7V) : Submodule F7 F7V :=
  Submodule.span F7 ({v} : Set F7V)

def f7_zeta : F7 := 2

def f7_P_mode_lines : Fin 3 → Submodule F7 F7V :=
  ![f7_line (f7_vector 1 0 0),
    f7_line (f7_vector 0 1 0),
    f7_line (f7_vector 0 0 1)]

def f7_QA_mode_lines : Fin 3 → Submodule F7 F7V :=
  ![f7_line (f7_vector 1 0 0),
    f7_line (f7_vector 1 1 1),
    f7_line (f7_vector 1 2 3)]

def f7_QB_mode_lines : Fin 3 → Submodule F7 F7V :=
  ![f7_line (f7_vector 1 0 0),
    f7_line (f7_vector 1 1 1),
    f7_line (f7_vector 1 2 4)]

def f7_code_set (U0 U1 U2 : Submodule F7 F7V) : Set F7CodeAmbient :=
  {c | ∃ u0 : F7V, u0 ∈ U0 ∧
      ∃ u1 : F7V, u1 ∈ U1 ∧
        ∃ u2 : F7V, u2 ∈ U2 ∧
          c = ![u0 + u1 + u2,
            u0 + f7_zeta • u1 + f7_zeta ^ 2 • u2,
            u0 + f7_zeta ^ 2 • u1 + f7_zeta • u2]}

def f7_code_submodule (U0 U1 U2 : Submodule F7 F7V) :
    Submodule F7 F7CodeAmbient :=
  Submodule.span F7 (f7_code_set U0 U1 U2)

def f7_coordinate_projection (j : Fin 3) :
    F7CodeAmbient →ₗ[F7] F7V :=
  { toFun := fun c => c j
    map_add' := by intro c d; rfl
    map_smul' := by intro a c; rfl }

def f7_projection_isomorphism (U0 U1 U2 : Submodule F7 F7V)
    (j : Fin 3) : Prop :=
  ∃ e : f7_code_submodule U0 U1 U2 ≃ₗ[F7] F7V,
    ∀ c, e c = c.1 j

def f7_cyclic_coordinate_permutation (c : F7CodeAmbient) : F7CodeAmbient :=
  ![c 1, c 2, c 0]

def f7_code_invariant_under_cycle (U0 U1 U2 : Submodule F7 F7V) : Prop :=
  ∀ c : F7CodeAmbient,
    c ∈ f7_code_set U0 U1 U2 ↔
      f7_cyclic_coordinate_permutation c ∈ f7_code_set U0 U1 U2

def exact_scalar_C3_Fourier_code_interface : Prop :=
  let P := f7_code_set (f7_P_mode_lines 0) (f7_P_mode_lines 1) (f7_P_mode_lines 2)
  let QA := f7_code_set (f7_QA_mode_lines 0) (f7_QA_mode_lines 1) (f7_QA_mode_lines 2)
  let QB := f7_code_set (f7_QB_mode_lines 0) (f7_QB_mode_lines 1) (f7_QB_mode_lines 2)
  (P = (f7_code_submodule
      (f7_P_mode_lines 0) (f7_P_mode_lines 1) (f7_P_mode_lines 2)).carrier) ∧
    (QA = (f7_code_submodule
      (f7_QA_mode_lines 0) (f7_QA_mode_lines 1) (f7_QA_mode_lines 2)).carrier) ∧
    (QB = (f7_code_submodule
      (f7_QB_mode_lines 0) (f7_QB_mode_lines 1) (f7_QB_mode_lines 2)).carrier) ∧
    Module.finrank F7 (f7_code_submodule
      (f7_P_mode_lines 0) (f7_P_mode_lines 1) (f7_P_mode_lines 2)) = 3 ∧
    Module.finrank F7 (f7_code_submodule
      (f7_QA_mode_lines 0) (f7_QA_mode_lines 1) (f7_QA_mode_lines 2)) = 3 ∧
    Module.finrank F7 (f7_code_submodule
      (f7_QB_mode_lines 0) (f7_QB_mode_lines 1) (f7_QB_mode_lines 2)) = 3 ∧
    (∀ j : Fin 3,
      f7_projection_isomorphism
        (f7_P_mode_lines 0) (f7_P_mode_lines 1) (f7_P_mode_lines 2) j) ∧
    (∀ j : Fin 3,
      f7_projection_isomorphism
        (f7_QA_mode_lines 0) (f7_QA_mode_lines 1) (f7_QA_mode_lines 2) j) ∧
    (∀ j : Fin 3,
      f7_projection_isomorphism
        (f7_QB_mode_lines 0) (f7_QB_mode_lines 1) (f7_QB_mode_lines 2) j) ∧
    f7_code_invariant_under_cycle
      (f7_P_mode_lines 0) (f7_P_mode_lines 1) (f7_P_mode_lines 2) ∧
    f7_code_invariant_under_cycle
      (f7_QA_mode_lines 0) (f7_QA_mode_lines 1) (f7_QA_mode_lines 2) ∧
    f7_code_invariant_under_cycle
      (f7_QB_mode_lines 0) (f7_QB_mode_lines 1) (f7_QB_mode_lines 2)

def f7_marked_lines_A : Fin 6 → Submodule F7 F7V :=
  ![f7_P_mode_lines 0, f7_P_mode_lines 1, f7_P_mode_lines 2,
    f7_QA_mode_lines 0, f7_QA_mode_lines 1, f7_QA_mode_lines 2]

def f7_marked_lines_B : Fin 6 → Submodule F7 F7V :=
  ![f7_P_mode_lines 0, f7_P_mode_lines 1, f7_P_mode_lines 2,
    f7_QB_mode_lines 0, f7_QB_mode_lines 1, f7_QB_mode_lines 2]

def f7_marked_span (lines : Fin 6 → Submodule F7 F7V)
    (S : Set (Fin 6)) : Submodule F7 F7V :=
  Submodule.span F7 (⋃ i ∈ S, (lines i : Set F7V))

def f7_pair_span (lines : Fin 6 → Submodule F7 F7V)
    (i j : Fin 6) : Submodule F7 F7V :=
  Submodule.span F7 ((lines i : Set F7V) ∪ (lines j : Set F7V))

def f7_pair_intersection (lines : Fin 6 → Submodule F7 F7V)
    (i j k l : Fin 6) : Submodule F7 F7V :=
  f7_pair_span lines i j ⊓ f7_pair_span lines k l

def complete_labelled_line_plane_signatures_coincide : Prop :=
  (∀ S : Set (Fin 6), S.Nonempty →
    Module.finrank F7 (f7_marked_span f7_marked_lines_A S) =
      Module.finrank F7 (f7_marked_span f7_marked_lines_B S)) ∧
    (∀ i j : Fin 6, i ≠ j → ∀ k : Fin 6,
      (f7_marked_lines_A k ≤ f7_pair_span f7_marked_lines_A i j ↔
        f7_marked_lines_B k ≤ f7_pair_span f7_marked_lines_B i j)) ∧
    (∀ i j k l : Fin 6, i ≠ j → k ≠ l →
      Module.finrank F7
          (f7_pair_intersection f7_marked_lines_A i j k l) =
        Module.finrank F7
          (f7_pair_intersection f7_marked_lines_B i j k l))

def no_common_scalar_equivariant_marked_transporter : Prop :=
  ¬ ∃ a : F7V ≃ₗ[F7] F7V,
    (∀ i : Fin 3,
      Set.image (fun v : F7V => a v) (f7_P_mode_lines i : Set F7V) =
        (f7_P_mode_lines i : Set F7V)) ∧
    (∀ i : Fin 3,
      Set.image (fun v : F7V => a v) (f7_QA_mode_lines i : Set F7V) =
        (f7_QB_mode_lines i : Set F7V))

def f7_projective_ratio (v : F7V) : F7 := v (2 : Fin 3) / v (1 : Fin 3)

def missing_marked_frame_projective_ratio : Prop :=
  complete_labelled_line_plane_signatures_coincide ∧
  f7_vector 1 2 3 0 = 1 ∧
    f7_vector 1 2 4 0 = 1 ∧
    f7_projective_ratio (f7_vector 1 2 3) = (3 : F7) / (2 : F7) ∧
    f7_projective_ratio (f7_vector 1 2 4) = (4 : F7) / (2 : F7) ∧
    (3 : F7) / (2 : F7) = 5 ∧
    (4 : F7) / (2 : F7) = 2 ∧
    f7_projective_ratio (f7_vector 1 2 3) ≠
      f7_projective_ratio (f7_vector 1 2 4) ∧
    f7_line (f7_vector 1 2 3) ≠ f7_line (f7_vector 1 2 4)

end MathlibPlus.Open.ResearchFormalizationBatch01_01a0014f
