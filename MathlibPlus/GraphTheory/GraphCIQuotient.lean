import MathlibPlus.Open.GraphTheory.GraphCIQuotient

namespace MathlibPlus.GraphTheory

open scoped Pointwise

noncomputable section

private theorem quotientPreimage_mulCayley_adj_iff
    {G : Type*} [Group G] (N : Subgroup G) [N.Normal]
    {S : Set (G ⧸ N)} (hS : 1 ∉ S) (x y : G) :
    (SimpleGraph.mulCayley ((QuotientGroup.mk' N) ⁻¹' S)).Adj x y ↔
      (SimpleGraph.mulCayley S).Adj
        (QuotientGroup.mk' N x) (QuotientGroup.mk' N y) := by
  rw [SimpleGraph.mulCayley_adj, SimpleGraph.mulCayley_adj]
  constructor
  · rintro ⟨hxy, hmem⟩
    refine ⟨?_, ?_⟩
    · intro heq
      rcases hmem with hmem | hmem
      · apply hS
        change (QuotientGroup.mk' N x)⁻¹ * QuotientGroup.mk' N y ∈ S at hmem
        simpa [heq] using hmem
      · apply hS
        change (QuotientGroup.mk' N y)⁻¹ * QuotientGroup.mk' N x ∈ S at hmem
        simpa [heq] using hmem
    · simpa only [Set.mem_preimage, map_inv, map_mul] using hmem
  · rintro ⟨hxy, hmem⟩
    refine ⟨fun h => hxy (congrArg (QuotientGroup.mk' N) h), ?_⟩
    simpa only [Set.mem_preimage, map_inv, map_mul] using hmem

private theorem quotientPreimageInsert_mulCayley_adj_iff
    {G : Type*} [Group G] (N : Subgroup G) [N.Normal]
    {S : Set (G ⧸ N)} (hS : 1 ∉ S) (x y : G) :
    (SimpleGraph.mulCayley ((QuotientGroup.mk' N) ⁻¹' insert 1 S)).Adj x y ↔
      x ≠ y ∧
        (QuotientGroup.mk' N x = QuotientGroup.mk' N y ∨
          (SimpleGraph.mulCayley S).Adj
            (QuotientGroup.mk' N x) (QuotientGroup.mk' N y)) := by
  rw [SimpleGraph.mulCayley_adj, SimpleGraph.mulCayley_adj]
  constructor
  · rintro ⟨hxy, hmem⟩
    refine ⟨hxy, ?_⟩
    rcases hmem with hmem | hmem
    · rcases hmem with hmem | hmem
      · exact Or.inl (inv_mul_eq_one.mp hmem)
      · refine Or.inr ⟨?_, Or.inl hmem⟩
        intro heq
        apply hS
        have hone : (QuotientGroup.mk' N x)⁻¹ * QuotientGroup.mk' N y = 1 :=
          inv_mul_eq_one.mpr heq
        exact hone ▸ hmem
    · rcases hmem with hmem | hmem
      · exact Or.inl (inv_mul_eq_one.mp hmem).symm
      · refine Or.inr ⟨?_, Or.inr hmem⟩
        intro heq
        apply hS
        have hone : (QuotientGroup.mk' N y)⁻¹ * QuotientGroup.mk' N x = 1 :=
          inv_mul_eq_one.mpr heq.symm
        exact hone ▸ hmem
  · rintro ⟨hxy, heq | hadj⟩
    · refine ⟨hxy, Or.inl (Or.inl ?_)⟩
      exact inv_mul_eq_one.mpr heq
    · exact ⟨hxy, hadj.2.imp Or.inr Or.inr⟩

private theorem preimage_inverse
    {G Q : Type*} [Group G] [Group Q] (q : G →* Q)
    (U : Set Q) (hU : U = U⁻¹) : q ⁻¹' U = (q ⁻¹' U)⁻¹ := by
  ext x
  change q x ∈ U ↔ x ∈ (q ⁻¹' U)⁻¹
  rw [Set.mem_inv]
  change q x ∈ U ↔ q x⁻¹ ∈ U
  rw [map_inv, ← Set.mem_inv]
  exact Set.ext_iff.mp hU (q x)

private theorem eraseOne_inverse
    {G : Type*} [Group G] (U : Set G) (hU : U = U⁻¹) :
    U \ {1} = (U \ {1})⁻¹ := by
  ext x
  rw [Set.mem_inv]
  have hi : x⁻¹ ∈ U ↔ x ∈ U := by
    constructor
    · intro hxi
      rw [hU, Set.mem_inv]
      exact hxi
    · intro hx
      rw [hU, Set.mem_inv]
      simpa using hx
  constructor
  · rintro ⟨hxU, hx1⟩
    exact ⟨hi.mpr hxU, by simpa using hx1⟩
  · rintro ⟨hxU, hx1⟩
    exact ⟨hi.mp hxU, by simpa using hx1⟩

private theorem insertOne_inverse
    {G : Type*} [Group G] (U : Set G) (hU : U = U⁻¹) :
    insert 1 U = (insert 1 U)⁻¹ := by
  ext x
  rw [Set.mem_inv]
  simp only [Set.mem_insert_iff, inv_eq_one]
  have hi : x⁻¹ ∈ U ↔ x ∈ U := by
    constructor
    · intro hxi
      rw [hU, Set.mem_inv]
      exact hxi
    · intro hx
      rw [hU, Set.mem_inv]
      simpa using hx
  rw [hi]

private theorem leftImage_preimage_eq_iff
    {G Q : Type*} [Group G] [Group Q] (q : G →* Q)
    (hq : Function.Surjective q) (U : Set Q) (x : G) :
    (fun u => x * u) '' (q ⁻¹' U) = q ⁻¹' U ↔
      (fun u => q x * u) '' U = U := by
  constructor
  · intro h
    apply Set.Subset.antisymm
    · rintro z ⟨u, hu, rfl⟩
      obtain ⟨g, rfl⟩ := hq u
      have hxg : x * g ∈ q ⁻¹' U := by
        rw [← h]
        exact ⟨g, hu, rfl⟩
      simpa only [Set.mem_preimage, map_mul] using hxg
    · intro z hz
      obtain ⟨g, rfl⟩ := hq z
      have hg : g ∈ q ⁻¹' U := hz
      rw [← h] at hg
      rcases hg with ⟨u, hu, hxu⟩
      refine ⟨q u, hu, ?_⟩
      simpa only [map_mul] using congrArg q hxu
  · intro h
    apply Set.Subset.antisymm
    · rintro z ⟨u, hu, rfl⟩
      show q (x * u) ∈ U
      rw [map_mul, ← h]
      exact ⟨q u, hu, rfl⟩
    · intro z hz
      have hz' : q z ∈ (fun u => q x * u) '' U := by rwa [h]
      rcases hz' with ⟨u, hu, hxu⟩
      refine ⟨x⁻¹ * z, ?_, by simp⟩
      show q (x⁻¹ * z) ∈ U
      have heq : q (x⁻¹ * z) = u := by
        calc
          q (x⁻¹ * z) = (q x)⁻¹ * q z := by simp
          _ = (q x)⁻¹ * (q x * u) := by rw [← hxu]
          _ = u := by simp
      rwa [heq]

private theorem leftImage_map
    {G H : Type*} [Group G] [Group H] (φ : G ≃* H)
    {U : Set G} {V : Set H} (hφ : φ '' U = V) {x : G}
    (hx : (fun u => x * u) '' U = U) :
    (fun v => φ x * v) '' V = V := by
  apply Set.Subset.antisymm
  · rintro y ⟨v, hv, rfl⟩
    have hv' : v ∈ φ '' U := by rwa [hφ]
    rcases hv' with ⟨u, hu, rfl⟩
    have hxu : x * u ∈ U := by
      rw [← hx]
      exact ⟨u, hu, rfl⟩
    have himage : φ (x * u) ∈ φ '' U := ⟨x * u, hxu, rfl⟩
    rw [hφ] at himage
    simpa only [map_mul] using himage
  · intro y hy
    have hy' : y ∈ φ '' U := by rwa [hφ]
    rcases hy' with ⟨u, hu, rfl⟩
    have hu' : u ∈ (fun z => x * z) '' U := by rwa [hx]
    rcases hu' with ⟨z, hz, rfl⟩
    refine ⟨φ z, ?_, by rw [map_mul]⟩
    rw [← hφ]
    exact ⟨z, hz, rfl⟩

private theorem leftImage_dichotomy
    {G : Type*} [Group G] (S : Set G) (hSinv : S = S⁻¹) (hSone : 1 ∉ S) :
    (∀ x : G, (fun s => x * s) '' S = S → x = 1) ∨
      (∀ x : G, (fun s => x * s) '' insert 1 S = insert 1 S → x = 1) := by
  by_cases hopen : ∀ x : G, (fun s => x * s) '' S = S → x = 1
  · exact Or.inl hopen
  · right
    push Not at hopen
    rcases hopen with ⟨x, hx, hx1⟩
    intro y hy
    by_contra hy1
    have hinv : ∀ {z : G}, z ∈ S → z⁻¹ ∈ S := by
      intro z hz
      rw [hSinv, Set.mem_inv]
      simpa using hz
    have hyS : y ∈ S := by
      have : y ∈ insert 1 S := by
        rw [← hy]
        exact ⟨1, Set.mem_insert 1 S, by simp⟩
      rcases this with (rfl | hyS)
      · exact (hy1 rfl).elim
      · exact hyS
    have hxS : x ∉ S := by
      intro hxmem
      have hxi : x⁻¹ ∈ S := hinv hxmem
      have : (1 : G) ∈ (fun s => x * s) '' S := ⟨x⁻¹, hxi, by simp⟩
      rw [hx] at this
      exact hSone this
    have hyx_not : y⁻¹ * x ∉ S := by
      intro hyx
      have himage : x ∈ (fun s => y * s) '' insert 1 S :=
        ⟨y⁻¹ * x, Set.mem_insert_of_mem 1 hyx, by simp⟩
      rw [hy] at himage
      rcases himage with hxeq | hxmem
      · exact hx1 hxeq
      · exact hxS hxmem
    have hyx : y⁻¹ * x ∈ S := by
      have : y ∈ (fun s => x * s) '' S := by rwa [hx]
      rcases this with ⟨z, hz, hxz⟩
      have hzi : z⁻¹ ∈ S := hinv hz
      have heq : y⁻¹ * x = z⁻¹ := by
        rw [← hxz]
        simp
      rwa [heq]
    exact hyx_not hyx

private theorem normalizedIso
    {G : Type*} [Group G] {S T : Set G}
    (e : SimpleGraph.mulCayley S ≃g SimpleGraph.mulCayley T) :
    ∃ e₀ : SimpleGraph.mulCayley S ≃g SimpleGraph.mulCayley T, e₀ 1 = 1 := by
  let L : G ≃ G := Equiv.mulLeft (e 1)⁻¹
  let e₀ : SimpleGraph.mulCayley S ≃g SimpleGraph.mulCayley T :=
    { toEquiv := e.toEquiv.trans L
      map_rel_iff' := by
        intro x y
        change (SimpleGraph.mulCayley T).Adj ((e 1)⁻¹ * e x) ((e 1)⁻¹ * e y) ↔ _
        rw [SimpleGraph.mulCayley_adj_mul_iff_right]
        exact e.map_rel_iff }
  refine ⟨e₀, ?_⟩
  simp [e₀, L]

private theorem mulCayley_neighborSet_eq_leftImage
    {G : Type*} [Group G] (S : Set G) (hSinv : S = S⁻¹) (hSone : 1 ∉ S)
    (x : G) :
    (SimpleGraph.mulCayley S).neighborSet x = (fun s => x * s) '' S := by
  ext y
  rw [SimpleGraph.mem_neighborSet, SimpleGraph.mulCayley_adj]
  constructor
  · rintro ⟨_, h | h⟩
    · exact ⟨x⁻¹ * y, h, by simp⟩
    · refine ⟨x⁻¹ * y, ?_, by simp⟩
      have hi : (y⁻¹ * x)⁻¹ ∈ S := by
        rw [hSinv, Set.mem_inv]
        simpa using h
      simpa using hi
  · rintro ⟨s, hs, rfl⟩
    refine ⟨?_, Or.inl (by simpa using hs)⟩
    intro hxs
    apply hSone
    have : s = 1 := by
      simpa using (congrArg (fun z => x⁻¹ * z) hxs).symm
    simpa [this] using hs

private theorem leftImage_rigid_of_iso
    {G : Type*} [Group G] {S T : Set G}
    (hSinv : S = S⁻¹) (hTinv : T = T⁻¹) (hSone : 1 ∉ S) (hTone : 1 ∉ T)
    (e : SimpleGraph.mulCayley S ≃g SimpleGraph.mulCayley T) (he1 : e 1 = 1)
    (hSrigid : ∀ x : G, (fun s => x * s) '' S = S → x = 1) :
    ∀ y : G, (fun t => y * t) '' T = T → y = 1 := by
  intro y hy
  let x := e.symm y
  have hyN : (SimpleGraph.mulCayley T).neighborSet y =
      (SimpleGraph.mulCayley T).neighborSet 1 := by
    rw [mulCayley_neighborSet_eq_leftImage T hTinv hTone,
      mulCayley_neighborSet_eq_leftImage T hTinv hTone]
    simpa using hy
  have hxN : (SimpleGraph.mulCayley S).neighborSet x =
      (SimpleGraph.mulCayley S).neighborSet 1 := by
    ext z
    change (SimpleGraph.mulCayley S).Adj x z ↔ (SimpleGraph.mulCayley S).Adj 1 z
    rw [← e.map_rel_iff, ← e.map_rel_iff]
    have hex : e x = y := e.apply_symm_apply y
    rw [hex, he1]
    exact Set.ext_iff.mp hyN (e z)
  have hxP : (fun s => x * s) '' S = S := by
    rw [mulCayley_neighborSet_eq_leftImage S hSinv hSone,
      mulCayley_neighborSet_eq_leftImage S hSinv hSone] at hxN
    simpa using hxN
  have hx1 := hSrigid x hxP
  calc
    y = e x := (e.apply_symm_apply y).symm
    _ = e 1 := by rw [hx1]
    _ = 1 := he1

private theorem closedLeftImage_rigid_of_iso
    {G : Type*} [Group G] {S T : Set G}
    (hSinv : S = S⁻¹) (hTinv : T = T⁻¹) (hSone : 1 ∉ S) (hTone : 1 ∉ T)
    (e : SimpleGraph.mulCayley S ≃g SimpleGraph.mulCayley T) (he1 : e 1 = 1)
    (hSrigid : ∀ x : G, (fun s => x * s) '' insert 1 S = insert 1 S → x = 1) :
    ∀ y : G, (fun t => y * t) '' insert 1 T = insert 1 T → y = 1 := by
  intro y hy
  let x := e.symm y
  have closed_eq (U : Set G) (hUinv : U = U⁻¹) (hUone : 1 ∉ U) (a : G) :
      insert a ((SimpleGraph.mulCayley U).neighborSet a) =
        (fun u => a * u) '' insert 1 U := by
    rw [mulCayley_neighborSet_eq_leftImage U hUinv hUone]
    ext z
    constructor
    · rintro (rfl | ⟨u, hu, rfl⟩)
      · exact ⟨1, Set.mem_insert 1 U, by simp⟩
      · exact ⟨u, Set.mem_insert_of_mem 1 hu, rfl⟩
    · rintro ⟨u, hu, rfl⟩
      rcases hu with rfl | hu
      · simp
      · exact Set.mem_insert_of_mem a ⟨u, hu, rfl⟩
  have hyC : insert y ((SimpleGraph.mulCayley T).neighborSet y) =
      insert 1 ((SimpleGraph.mulCayley T).neighborSet 1) := by
    rw [closed_eq T hTinv hTone, closed_eq T hTinv hTone]
    simpa using hy
  have hxC : insert x ((SimpleGraph.mulCayley S).neighborSet x) =
      insert 1 ((SimpleGraph.mulCayley S).neighborSet 1) := by
    ext z
    change (z = x ∨ (SimpleGraph.mulCayley S).Adj x z) ↔
      (z = 1 ∨ (SimpleGraph.mulCayley S).Adj 1 z)
    have heq : e z = y ↔ z = x := by
      constructor
      · intro h
        exact e.injective (h.trans (e.apply_symm_apply y).symm)
      · intro h
        rw [h]
        exact e.apply_symm_apply y
    have hone : e z = 1 ↔ z = 1 := by
      constructor
      · intro h
        apply e.injective
        simpa [he1] using h
      · rintro rfl
        exact he1
    rw [← heq, ← hone, ← e.map_rel_iff, ← e.map_rel_iff]
    have hex : e x = y := e.apply_symm_apply y
    rw [hex, he1]
    exact Set.ext_iff.mp hyC (e z)
  have hxP : (fun s => x * s) '' insert 1 S = insert 1 S := by
    rw [closed_eq S hSinv hSone, closed_eq S hSinv hSone] at hxC
    simpa using hxC
  have hx1 := hSrigid x hxP
  calc
    y = e x := (e.apply_symm_apply y).symm
    _ = e 1 := by rw [hx1]
    _ = 1 := he1

/-- Ordinary undirected graph-CI descends through every finite normal quotient.
The proof uses the open/closed twin-period dichotomy: an independent-fibre or
complete-fibre lift makes the selected normal kernel exact and hence forces
every ambient group-automorphism transporter to descend. -/
theorem graphCIHereditaryToNormalQuotients_proved :
    MathlibPlus.Open.GraphTheory.graphCIHereditaryToNormalQuotients := by
  intro G _ hG N _ hCI S T hSinv hTinv hSone hTone hIso
  let q : G →* (G ⧸ N) := QuotientGroup.mk' N
  let coord : G ≃ (G ⧸ N) × N := Subgroup.groupEquivQuotientProdSubgroup (s := N)
  let liftEquiv : ((G ⧸ N) ≃ (G ⧸ N)) → (G ≃ G) := fun e =>
    coord.trans ((Equiv.prodCongr e (Equiv.refl N)).trans coord.symm)
  have coord_fst (x : G) : (coord x).1 = q x := rfl
  have liftEquiv_mk (e : (G ⧸ N) ≃ (G ⧸ N)) (x : G) :
      q (liftEquiv e x) = e (q x) := by
    rw [← coord_fst]
    dsimp [liftEquiv]
    rw [coord.apply_symm_apply]
    exact congrArg e (coord_fst x)
  have preimage_one (U : Set (G ⧸ N)) (hU : 1 ∉ U) : 1 ∉ q ⁻¹' U := by
    simpa using hU
  rcases hIso with ⟨e⟩
  obtain ⟨e₀, he₀⟩ := normalizedIso e
  rcases leftImage_dichotomy S hSinv hSone with hopen | hclosed
  · have hopenT := leftImage_rigid_of_iso hSinv hTinv hSone hTone e₀ he₀ hopen
    let US : Set G := q ⁻¹' S
    let UT : Set G := q ⁻¹' T
    let liftedIso : SimpleGraph.mulCayley US ≃g SimpleGraph.mulCayley UT :=
      { toEquiv := liftEquiv e.toEquiv
        map_rel_iff' := by
          intro x y
          rw [quotientPreimage_mulCayley_adj_iff N hSone,
            quotientPreimage_mulCayley_adj_iff N hTone]
          rw [liftEquiv_mk, liftEquiv_mk]
          exact e.map_rel_iff }
    obtain ⟨φ, hφ⟩ := hCI US UT
      (preimage_inverse q S hSinv) (preimage_inverse q T hTinv)
      (preimage_one S hSone) (preimage_one T hTone) ⟨liftedIso⟩
    have periodS (x : G) : (fun u => x * u) '' US = US ↔ x ∈ N := by
      rw [leftImage_preimage_eq_iff q (QuotientGroup.mk'_surjective N)]
      constructor
      · intro hp
        have hqx : q x = 1 := hopen (q x) hp
        change (x : G ⧸ N) = 1 at hqx
        rwa [QuotientGroup.eq_one_iff] at hqx
      · intro hx
        have hqx : q x = 1 := by
          change (x : G ⧸ N) = 1
          rwa [QuotientGroup.eq_one_iff]
        simp [hqx]
    have periodT (x : G) : (fun u => x * u) '' UT = UT ↔ x ∈ N := by
      rw [leftImage_preimage_eq_iff q (QuotientGroup.mk'_surjective N)]
      constructor
      · intro hp
        have hqx : q x = 1 := hopenT (q x) hp
        change (x : G ⧸ N) = 1 at hqx
        rwa [QuotientGroup.eq_one_iff] at hqx
      · intro hx
        have hqx : q x = 1 := by
          change (x : G ⧸ N) = 1
          rwa [QuotientGroup.eq_one_iff]
        simp [hqx]
    have hφinv : φ.symm '' UT = US := by
      apply Set.Subset.antisymm
      · rintro x ⟨y, hy, rfl⟩
        rw [← hφ] at hy
        rcases hy with ⟨z, hz, hzy⟩
        simpa [← hzy] using hz
      · intro x hx
        refine ⟨φ x, ?_, φ.symm_apply_apply x⟩
        rw [← hφ]
        exact ⟨x, hx, rfl⟩
    have hNmap : N.map (φ : G →* G) = N := by
      ext y
      constructor
      · rintro ⟨x, hx, rfl⟩
        apply (periodT (φ x)).mp
        exact leftImage_map φ hφ ((periodS x).mpr hx)
      · intro hy
        let x := φ.symm y
        have hxP : (fun u => x * u) '' US = US :=
          leftImage_map φ.symm hφinv ((periodT y).mpr hy)
        exact ⟨x, (periodS x).mp hxP, by simp [x]⟩
    let φq : (G ⧸ N) ≃* (G ⧸ N) := QuotientGroup.congr N N φ hNmap
    refine ⟨φq, Set.Subset.antisymm ?_ ?_⟩
    · rintro y ⟨x, hx, rfl⟩
      obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective N x
      have hφg : φ g ∈ UT := by
        rw [← hφ]
        exact ⟨g, hx, rfl⟩
      change QuotientGroup.mk' N (φ g) ∈ T at hφg
      simpa [φq] using hφg
    · intro y hy
      obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective N y
      have hg : g ∈ UT := hy
      rw [← hφ] at hg
      rcases hg with ⟨z, hz, hzg⟩
      refine ⟨q z, hz, ?_⟩
      change QuotientGroup.congr N N φ hNmap (QuotientGroup.mk' N z) =
        QuotientGroup.mk' N g
      rw [QuotientGroup.congr_mk']
      exact congrArg q hzg
  · have hclosedT := closedLeftImage_rigid_of_iso hSinv hTinv hSone hTone e₀ he₀ hclosed
    let CS : Set G := q ⁻¹' insert 1 S \ {1}
    let CT : Set G := q ⁻¹' insert 1 T \ {1}
    have hInsertSinv : insert 1 S = (insert 1 S)⁻¹ := insertOne_inverse S hSinv
    have hInsertTinv : insert 1 T = (insert 1 T)⁻¹ := insertOne_inverse T hTinv
    have hCSinv : CS = CS⁻¹ :=
      eraseOne_inverse (q ⁻¹' insert 1 S) (preimage_inverse q _ hInsertSinv)
    have hCTinv : CT = CT⁻¹ :=
      eraseOne_inverse (q ⁻¹' insert 1 T) (preimage_inverse q _ hInsertTinv)
    have hCSone : 1 ∉ CS := by simp [CS]
    have hCTone : 1 ∉ CT := by simp [CT]
    let liftedIso : SimpleGraph.mulCayley CS ≃g SimpleGraph.mulCayley CT :=
      { toEquiv := liftEquiv e.toEquiv
        map_rel_iff' := by
          intro x y
          change (SimpleGraph.mulCayley (q ⁻¹' insert 1 T \ {1})).Adj
              (liftEquiv e.toEquiv x) (liftEquiv e.toEquiv y) ↔
            (SimpleGraph.mulCayley (q ⁻¹' insert 1 S \ {1})).Adj x y
          rw [SimpleGraph.mulCayley_erase_one, SimpleGraph.mulCayley_erase_one]
          rw [quotientPreimageInsert_mulCayley_adj_iff N hTone,
            quotientPreimageInsert_mulCayley_adj_iff N hSone]
          rw [liftEquiv_mk, liftEquiv_mk]
          constructor
          · rintro ⟨hxy, heq | hadj⟩
            · exact ⟨fun h => hxy (congrArg (liftEquiv e.toEquiv) h), Or.inl (e.injective heq)⟩
            · exact ⟨fun h => hxy (congrArg (liftEquiv e.toEquiv) h), Or.inr (e.map_rel_iff.mp hadj)⟩
          · rintro ⟨hxy, heq | hadj⟩
            · exact ⟨fun h => hxy ((liftEquiv e.toEquiv).injective h), Or.inl (congrArg e heq)⟩
            · exact ⟨fun h => hxy ((liftEquiv e.toEquiv).injective h), Or.inr (e.map_rel_iff.mpr hadj)⟩ }
    obtain ⟨φ, hφ⟩ := hCI CS CT hCSinv hCTinv hCSone hCTone ⟨liftedIso⟩
    have hφfull : φ '' (q ⁻¹' insert 1 S) = q ⁻¹' insert 1 T := by
      ext y
      constructor
      · rintro ⟨x, hx, rfl⟩
        by_cases hx1 : x = 1
        · subst x
          simp
        · have hxCS : x ∈ CS := ⟨hx, hx1⟩
          have : φ x ∈ CT := by rw [← hφ]; exact ⟨x, hxCS, rfl⟩
          exact this.1
      · intro hy
        by_cases hy1 : y = 1
        · subst y
          exact ⟨1, by simp, by simp⟩
        · have hyCT : y ∈ CT := ⟨hy, hy1⟩
          rw [← hφ] at hyCT
          rcases hyCT with ⟨x, hxCS, hxy⟩
          exact ⟨x, hxCS.1, hxy⟩
    have periodS (x : G) :
        (fun u => x * u) '' (q ⁻¹' insert 1 S) = q ⁻¹' insert 1 S ↔ x ∈ N := by
      rw [leftImage_preimage_eq_iff q (QuotientGroup.mk'_surjective N)]
      constructor
      · intro hp
        have hqx : q x = 1 := hclosed (q x) hp
        change (x : G ⧸ N) = 1 at hqx
        rwa [QuotientGroup.eq_one_iff] at hqx
      · intro hx
        have hqx : q x = 1 := by
          change (x : G ⧸ N) = 1
          rwa [QuotientGroup.eq_one_iff]
        simp [hqx]
    have periodT (x : G) :
        (fun u => x * u) '' (q ⁻¹' insert 1 T) = q ⁻¹' insert 1 T ↔ x ∈ N := by
      rw [leftImage_preimage_eq_iff q (QuotientGroup.mk'_surjective N)]
      constructor
      · intro hp
        have hqx : q x = 1 := hclosedT (q x) hp
        change (x : G ⧸ N) = 1 at hqx
        rwa [QuotientGroup.eq_one_iff] at hqx
      · intro hx
        have hqx : q x = 1 := by
          change (x : G ⧸ N) = 1
          rwa [QuotientGroup.eq_one_iff]
        simp [hqx]
    have hφinv : φ.symm '' (q ⁻¹' insert 1 T) = q ⁻¹' insert 1 S := by
      apply Set.Subset.antisymm
      · rintro x ⟨y, hy, rfl⟩
        rw [← hφfull] at hy
        rcases hy with ⟨z, hz, hzy⟩
        simpa [← hzy] using hz
      · intro x hx
        refine ⟨φ x, ?_, φ.symm_apply_apply x⟩
        rw [← hφfull]
        exact ⟨x, hx, rfl⟩
    have hNmap : N.map (φ : G →* G) = N := by
      ext y
      constructor
      · rintro ⟨x, hx, rfl⟩
        apply (periodT (φ x)).mp
        exact leftImage_map φ hφfull ((periodS x).mpr hx)
      · intro hy
        let x := φ.symm y
        have hxP := leftImage_map φ.symm hφinv ((periodT y).mpr hy)
        exact ⟨x, (periodS x).mp hxP, by simp [x]⟩
    let φq : (G ⧸ N) ≃* (G ⧸ N) := QuotientGroup.congr N N φ hNmap
    have hφqInsert : φq '' insert 1 S = insert 1 T := by
      apply Set.Subset.antisymm
      · rintro y ⟨x, hx, rfl⟩
        obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective N x
        have hφg : φ g ∈ q ⁻¹' insert 1 T := by
          rw [← hφfull]
          exact ⟨g, hx, rfl⟩
        change QuotientGroup.mk' N (φ g) ∈ insert 1 T at hφg
        simpa [φq] using hφg
      · intro y hy
        obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective N y
        have hg : g ∈ q ⁻¹' insert 1 T := hy
        rw [← hφfull] at hg
        rcases hg with ⟨z, hz, hzg⟩
        refine ⟨q z, hz, ?_⟩
        change QuotientGroup.congr N N φ hNmap (QuotientGroup.mk' N z) =
          QuotientGroup.mk' N g
        rw [QuotientGroup.congr_mk']
        exact congrArg q hzg
    refine ⟨φq, Set.Subset.antisymm ?_ ?_⟩
    · rintro y ⟨x, hx, rfl⟩
      have : φq x ∈ insert 1 T := by
        rw [← hφqInsert]
        exact ⟨x, Set.mem_insert_of_mem 1 hx, rfl⟩
      rcases this with heq | hmem
      · have hx1 : x = 1 := by
          have := congrArg φq.symm heq
          simpa using this
        exact (hSone (hx1 ▸ hx)).elim
      · exact hmem
    · intro y hy
      have : y ∈ φq '' insert 1 S := by
        rw [hφqInsert]
        exact Set.mem_insert_of_mem 1 hy
      rcases this with ⟨x, hx, hxy⟩
      rcases hx with rfl | hx
      · have hy1 : y = 1 := by simpa using hxy.symm
        exact (hTone (hy1 ▸ hy)).elim
      · exact ⟨x, hx, hxy⟩

end

end MathlibPlus.GraphTheory
