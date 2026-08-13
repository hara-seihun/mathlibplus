import Mathlib.GroupTheory.SpecificGroups.Quaternion

namespace MathlibPlus.GroupTheory.Claim44712

abbrev Q8 := QuaternionGroup 2

def q8A (i : ZMod 4) : Q8 := QuaternionGroup.a i
def q8XA (i : ZMod 4) : Q8 := QuaternionGroup.xa i

def q8Pair (i : Fin 3) : Finset Q8 :=
  if i = 0 then {q8A 1, q8A 3}
  else if i = 1 then {q8XA 0, q8XA 2}
  else {q8XA 1, q8XA 3}

def q8Connection (c : Bool) (P : Finset (Fin 3)) : Finset Q8 :=
  (if c then {q8A 2} else ∅) ∪ P.biUnion q8Pair

def q8IsConnectionSet (S : Finset Q8) : Prop :=
  (1 : Q8) ∉ S ∧ ∀ x, x ∈ S ↔ x⁻¹ ∈ S

instance q8IsConnectionSetDecidable (S : Finset Q8) : Decidable (q8IsConnectionSet S) := by
  unfold q8IsConnectionSet
  infer_instance

/-- Every coordinate pair produces an identity-free inverse-closed connection set. -/
theorem q8_connection_is_connection_set :
    ∀ (c : Bool) (P : Finset (Fin 3)), q8IsConnectionSet (q8Connection c P) := by
  native_decide

/-- Every identity-free inverse-closed subset of `Q₈` has coordinates. -/
theorem q8_connection_coordinates_exists :
    ∀ S : Finset Q8, q8IsConnectionSet S →
      ∃ p : Bool × Finset (Fin 3), q8Connection p.1 p.2 = S := by
  native_decide

/-- The coordinate representation is unique. -/
theorem q8_connection_coordinates_unique :
    ∀ (c d : Bool) (P Q : Finset (Fin 3)),
      q8Connection c P = q8Connection d Q → c = d ∧ P = Q := by
  native_decide

/-- The valency of the coordinate `(c,P)` is `c + 2 |P|`. -/
theorem q8_connection_card :
    ∀ (c : Bool) (P : Finset (Fin 3)),
      (q8Connection c P).card = (if c then 1 else 0) + 2 * P.card := by
  native_decide

/-- The eight possible valency values are pairwise distinct. -/
theorem q8_valency_coordinates_injective :
    ∀ (c d : Bool) (P Q : Finset (Fin 3)),
      (q8Connection c P).card = (q8Connection d Q).card →
        c = d ∧ P.card = Q.card := by
  native_decide

def q8Conjugate (g : Q8) (S : Finset Q8) : Finset Q8 :=
  S.image (fun x => g * x * g⁻¹)

/-- Conjugation fixes the central involution and each of the three inverse
pairs of order-four elements. -/
theorem q8_inner_fixes_inverse_atoms :
    ∀ g : Q8,
      Finset.image (fun x : Q8 => g * x * g⁻¹) {q8A 2} = {q8A 2} ∧
        ∀ i : Fin 3,
          Finset.image (fun x : Q8 => g * x * g⁻¹) (q8Pair i) = q8Pair i := by
  native_decide

/-- Every inner automorphism fixes every identity-free inverse-closed
connection set. -/
theorem q8_inner_fixes_connection_sets :
    ∀ (g : Q8) (S : Finset Q8), q8IsConnectionSet S →
      q8Conjugate g S = S := by
  native_decide

/-- There are sixteen identity-free inverse-closed connection sets; the
preceding fixed-point theorem therefore makes the inner-action orbits singletons. -/
theorem q8_connection_set_count :
    Fintype.card {S : Finset Q8 // q8IsConnectionSet S} = 16 := by
  native_decide

end MathlibPlus.GroupTheory.Claim44712
