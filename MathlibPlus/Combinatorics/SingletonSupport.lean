import Mathlib

/-!
# Singleton-support register

The exact zero/one/many register and merge laws from packet `D-0113`.  This finite
semilattice records whether a support is empty, is concentrated at one exact code, or
contains multiple distinct codes.  The tree-attachment application is not asserted.
-/

namespace MathlibPlus.Combinatorics

/-- The zero/one/many quotient of an exact support set. -/
inductive SingletonSupport (K : Type*)
  | zero
  | one (code : K)
  | many
  deriving DecidableEq

namespace SingletonSupport

variable {K : Type*} [DecidableEq K]

/-- Merge two zero/one/many support summaries, retaining an exact code precisely when
both nonempty summaries carry that same code. -/
def merge : SingletonSupport K → SingletonSupport K → SingletonSupport K
  | .zero, q | q, .zero => q
  | .many, _ | _, .many => .many
  | .one k, .one l => if k = l then .one k else .many

@[simp] theorem zero_merge (a : SingletonSupport K) : merge .zero a = a := by
  rfl

@[simp] theorem merge_zero (a : SingletonSupport K) : merge a .zero = a := by
  cases a <;> rfl

@[simp] theorem many_merge (a : SingletonSupport K) : merge .many a = .many := by
  cases a <;> rfl

@[simp] theorem merge_many (a : SingletonSupport K) : merge a .many = .many := by
  cases a <;> rfl

@[simp] theorem merge_self (a : SingletonSupport K) : merge a a = a := by
  cases a <;> simp [merge]

/-- The support-summary merge is commutative. -/
theorem merge_comm (a b : SingletonSupport K) : merge a b = merge b a := by
  cases a <;> cases b <;> simp only [merge] <;>
    split_ifs <;> simp_all

/-- The support-summary merge is associative. -/
theorem merge_assoc (a b c : SingletonSupport K) :
    merge (merge a b) c = merge a (merge b c) := by
  cases a <;> cases b <;> cases c <;> simp only [merge] <;>
    split_ifs <;> simp_all

/-- The exact semilattice laws claimed by the packet, bundled in its original
quantifier shape. -/
theorem merge_laws :
    (∀ a b : SingletonSupport K, merge a b = merge b a) ∧
    (∀ a b c : SingletonSupport K, merge (merge a b) c = merge a (merge b c)) ∧
    (∀ a : SingletonSupport K, merge a a = a) ∧
    (∀ a : SingletonSupport K, merge .zero a = a) ∧
    ∀ a : SingletonSupport K, merge .many a = .many := by
  exact ⟨merge_comm, merge_assoc, merge_self, zero_merge, many_merge⟩

end SingletonSupport
end MathlibPlus.Combinatorics
