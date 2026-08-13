import MathlibPlus.Basic

namespace MathlibPlus.Combinatorics

/-- Incidence pairing for a finite edge flow: a divergence equation turns the
edge/potential pairing into the vertex/divergence pairing.  This is the exact
finite algebraic core of claim 54914. -/
theorem flow_potential_pairing_claim54914
    {E V R : Type*} [Fintype E] [Fintype V] [DecidableEq V]
    [CommRing R] (tail head : E → V) (b potential : V → R)
    (edgeFlow : E → R)
    (hdiv : ∀ v,
      b v = (∑ e : E, if tail e = v then edgeFlow e else 0) -
        ∑ e : E, if head e = v then edgeFlow e else 0) :
    (∑ e : E, edgeFlow e * (potential (tail e) - potential (head e))) =
      ∑ v : V, b v * potential v := by
  classical
  have htail :
      (∑ e : E, edgeFlow e * potential (tail e)) =
        ∑ v : V, (∑ e : E, if tail e = v then edgeFlow e else 0) * potential v := by
    calc
      (∑ e : E, edgeFlow e * potential (tail e)) =
          ∑ e : E, ∑ v : V,
            (if tail e = v then edgeFlow e else 0) * potential v := by
        apply Finset.sum_congr rfl
        intro e he
        rw [Finset.sum_eq_single (tail e)]
        · simp
        · intro v hv hne
          have hne' : tail e ≠ v := by
            intro h
            exact hne h.symm
          simp [hne']
        · simp
      _ = ∑ v : V, ∑ e : E,
            (if tail e = v then edgeFlow e else 0) * potential v := by
        rw [Finset.sum_comm]
      _ = ∑ v : V, (∑ e : E, if tail e = v then edgeFlow e else 0) * potential v := by
        apply Finset.sum_congr rfl
        intro v hv
        rw [Finset.sum_mul]
  have hhead :
      (∑ e : E, edgeFlow e * potential (head e)) =
        ∑ v : V, (∑ e : E, if head e = v then edgeFlow e else 0) * potential v := by
    calc
      (∑ e : E, edgeFlow e * potential (head e)) =
          ∑ e : E, ∑ v : V,
            (if head e = v then edgeFlow e else 0) * potential v := by
        apply Finset.sum_congr rfl
        intro e he
        rw [Finset.sum_eq_single (head e)]
        · simp
        · intro v hv hne
          have hne' : head e ≠ v := by
            intro h
            exact hne h.symm
          simp [hne']
        · simp
      _ = ∑ v : V, ∑ e : E,
            (if head e = v then edgeFlow e else 0) * potential v := by
        rw [Finset.sum_comm]
      _ = ∑ v : V, (∑ e : E, if head e = v then edgeFlow e else 0) * potential v := by
        apply Finset.sum_congr rfl
        intro v hv
        rw [Finset.sum_mul]
  calc
    (∑ e : E, edgeFlow e * (potential (tail e) - potential (head e))) =
        (∑ e : E, edgeFlow e * potential (tail e)) -
          ∑ e : E, edgeFlow e * potential (head e) := by
      simp_rw [mul_sub]
      rw [Finset.sum_sub_distrib]
    _ = (∑ v : V, (∑ e : E, if tail e = v then edgeFlow e else 0) * potential v) -
          ∑ v : V, (∑ e : E, if head e = v then edgeFlow e else 0) * potential v := by
      rw [htail, hhead]
    _ = ∑ v : V, b v * potential v := by
      rw [← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro v hv
      rw [hdiv]
      ring

/-- If the divergence is one unit at the initial vertex and minus one unit at
the terminal vertex, the pairing is the corresponding endpoint difference. -/
theorem endpoint_flow_potential_pairing_claim54914
    {E V R : Type*} [Fintype E] [Fintype V] [DecidableEq V]
    [CommRing R] (tail head : E → V) (source sink : V)
    (edgeFlow : E → R) (potential : V → R) (hsource : source ≠ sink)
    (hdiv : ∀ v,
      (if v = source then 1 else if v = sink then -1 else 0) =
        (∑ e : E, if tail e = v then edgeFlow e else 0) -
          ∑ e : E, if head e = v then edgeFlow e else 0) :
    (∑ e : E, edgeFlow e * (potential (tail e) - potential (head e))) =
      potential source - potential sink := by
  have hpair := flow_potential_pairing_claim54914 tail head
    (fun v : V => if v = source then 1 else if v = sink then -1 else 0)
    potential edgeFlow hdiv
  rw [hpair]
  have hterm : ∀ v : V,
      (if v = source then 1 else if v = sink then -1 else 0) * potential v =
        (if v = source then potential v else 0) -
          (if v = sink then potential v else 0) := by
    intro v
    by_cases hs : v = source
    · subst v
      simp [hsource]
    · by_cases hk : v = sink
      · subst v
        simp [hsource, Ne.symm hsource]
      · simp [hs, hk]
  simp_rw [hterm]
  rw [Finset.sum_sub_distrib]
  simp

end MathlibPlus.Combinatorics
