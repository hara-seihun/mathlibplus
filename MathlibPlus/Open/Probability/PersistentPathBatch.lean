import Mathlib

namespace MathlibPlus.Open.Probability.PersistentPathBatch

structure PersistentPLPath (T Q Ω : ℕ) where
  transcript : Fin Ω → Fin T → Bool
  queryWeight : Fin Ω → Fin T → ℝ
  A : Fin T → Fin Ω → ℝ
  c : Fin T → ℝ
  p : Fin T → Fin Ω → ℝ
  C : Fin Q → Fin Ω → ℝ
  probability : Fin Ω → ℝ
  lambda : Fin T → ℝ
  p_positive : ∀ t : Fin T, ∀ ω : Fin Ω, 0 < p t ω
  probability_nonnegative : ∀ ω : Fin Ω, 0 ≤ probability ω
  probability_total : ∑ ω : Fin Ω, probability ω = 1
  lambda_positive : ∀ t : Fin T, 0 < lambda t
  lambda_total : ∑ t : Fin T, lambda t = 1

def persistentS {T Q Ω : ℕ} (path : PersistentPLPath T Q Ω)
    (t : Fin T) (ω : Fin Ω) : ℝ :=
  path.A t ω * path.c t / path.p t ω

def persistentM {T Q Ω : ℕ} (path : PersistentPLPath T Q Ω)
    (s t : Fin T) : ℝ :=
  ∑ ω : Fin Ω, path.probability ω *
    (∑ q : Fin Q, path.C q ω * persistentS path s ω * persistentS path t ω)

def persistentG {T Q Ω : ℕ} (path : PersistentPLPath T Q Ω)
    (t : Fin T) : ℝ :=
  ∑ ω : Fin Ω, path.probability ω *
    (∑ q : Fin Q,
      path.C q ω * path.queryWeight ω t * path.A t ω *
        (path.c t / path.p t ω) ^ 2)

def persistentK {T Q Ω : ℕ} (path : PersistentPLPath T Q Ω) : ℝ :=
  ∑ ω : Fin Ω, path.probability ω *
    (∑ q : Fin Q,
      path.C q ω * (∑ t : Fin T, path.lambda t * persistentS path t ω) ^ 2)

def PersistentPLPathQuantities : Prop :=
  ∀ (T Q Ω : ℕ) (path : PersistentPLPath T Q Ω),
    (∀ t : Fin T, ∀ ω : Fin Ω,
      persistentS path t ω = path.A t ω * path.c t / path.p t ω) ∧
    (∀ s t : Fin T,
      persistentM path s t =
        ∑ ω : Fin Ω, path.probability ω *
          (∑ q : Fin Q,
            path.C q ω * persistentS path s ω * persistentS path t ω)) ∧
    (∀ t : Fin T,
      persistentG path t =
        ∑ ω : Fin Ω, path.probability ω *
          (∑ q : Fin Q,
            path.C q ω * path.queryWeight ω t * path.A t ω *
              (path.c t / path.p t ω) ^ 2)) ∧
    persistentK path =
      ∑ ω : Fin Ω, path.probability ω *
        (∑ q : Fin Q,
          path.C q ω * (∑ t : Fin T, path.lambda t * persistentS path t ω) ^ 2)

end MathlibPlus.Open.Probability.PersistentPathBatch
