import NLS.ZakharovShabat.SourceEquation2_29
import NLS.ZakharovShabat.SourcePsiFreeJacobian
import NLS.SequenceSpaces.CoefficientComplexification

/-!
# Failure of uniform convergence on a fixed original neighborhood

At the free source a root displacement at the omitted index leaves Qn
unchanged but changes a neighboring diagonal of Q*. A fixed small spike
can move to arbitrarily distant indices while remaining in any given
lp ball and in the original isolating disks. This refutes uniform
convergence on one fixed neighborhood. It does not refute mathlib's
locally uniform convergence, whose neighborhood may depend on epsilon.
-/

noncomputable section
open Set Complex Metric Filter Topology
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

theorem sourcePsiContour_free_single_diagonal
    (hp : p ≠ ⊤) (hp1 : 1 < p) (m k : ℤ) (hkm : k ≠ m)
    (r : ℝ) (hr : 0 < r) (hrπ : r < Real.pi) (t : ℂ) :
    sourcePsiContour hp hp1 m (lp.single p k t) (0:CoeffPair p) ((Real.pi:ℂ)*m) r =
      1+t/((Real.pi:ℂ)*k-(Real.pi:ℂ)*m) := by
  let c : ℂ := (Real.pi:ℂ)*m
  let base : ℂ → ℂ := fun z => -I*(z-(Real.pi:ℂ)*m)⁻¹
  let variation : ℂ → ℂ := fun z => I*((z-(Real.pi:ℂ)*m)⁻¹*(z-(Real.pi:ℂ)*k)⁻¹)
  have hinv (j : ℤ) : ContinuousOn (fun z : ℂ => (z-(Real.pi:ℂ)*j)⁻¹) (sphere c r) := by
    apply ContinuousOn.inv₀
    · exact continuousOn_id.sub continuousOn_const
    · intro z hz
      exact sub_ne_zero.mpr (freeCircle_point_ne_freeCenter m j r hr hrπ z hz)
  have hb : CircleIntegrable base c r := (continuousOn_const.mul (hinv m)).circleIntegrable hr.le
  have hv : CircleIntegrable (fun z => t*variation z) c r :=
    (continuousOn_const.mul (continuousOn_const.mul ((hinv m).mul (hinv k)))).circleIntegrable hr.le
  have he : (∮ z in C(c,r), sourcePsiContourIntegrandJoint hp hp1 m
      (z,((lp.single p k t:Coeff p),(0:CoeffPair p)))) = ∮ z in C(c,r), base z+t*variation z := by
    apply circleIntegral.integral_congr hr.le
    intro z hz
    exact sourcePsiContourIntegrandJoint_single_zero_eq hp hp1 m m k hkm r hr hrπ z hz t
  have hbase : (∮ z in C(c,r), base z) = 2*(Real.pi:ℂ) := by
    rw [circleIntegral.integral_const_mul,freeCircle_sub_inv_integral m m r hr hrπ,if_pos rfl]
    ring_nf
    simp [I_sq]
  have hvar : (∮ z in C(c,r), variation z) = (2*Real.pi:ℂ)/((Real.pi:ℂ)*k-(Real.pi:ℂ)*m) := by
    have hc : variation = fun z : ℂ => I*((z-(Real.pi:ℂ)*k)⁻¹*(z-(Real.pi:ℂ)*m)⁻¹) := by
      funext z; dsimp only [variation]; ring
    rw [hc,freeCircle_two_inv_integral m k m hkm.symm hkm r hr hrπ,if_pos rfl]
  unfold sourcePsiContour
  rw [he,circleIntegral.integral_add hb hv,hbase,circleIntegral.integral_const_mul,hvar]
  have hπ : (Real.pi:ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  field_simp [hπ]

theorem SourceLemma12_4Data.original_freeJacobian_diagonal
    {hp : p ≠ ⊤} {hp1 : 1 < p} {W V : Set (CoeffPair p)}
    {D : ℤ → Set ℂ} {c : ℝ} (H : SourceLemma12_4Data hp hp1 W)
    (hD : SourceIsolatingNeighborhoods hp hp1 V D c)
    (h0W : (0:CoeffPair p) ∈ W) (h0V : (0:CoeffPair p) ∈ V)
    (n m : ℤ) (hmn : m ≠ n) (r : ℝ) (hr : 0 < r) (hrπ : r < Real.pi)
    (he : D m = ball ((Real.pi:ℂ)*m) r) :
    sourcePsiOriginalJacobianEntry hp hp1 n m m (0:Coeff p) (0:CoeffPair p) = 2 := by
  let P := hD.periodCircle 0 h0V m (Real.pi*m) r hr (by simpa using he)
  rw [H.originalJacobianEntry_eq_contour_deriv 0 h0W n m m 0 P]
  have hd := (hasDerivAt_sourcePsiEquationCoordinate_single_zero hp hp1 m n m hmn hmn r hr hrπ).deriv
  simpa only [P,SourceIsolatingNeighborhoods.periodCircle,zero_add,ite_true,Complex.ofReal_mul,Complex.ofReal_intCast] using hd

-- Fixed-size spikes placed at the omitted index leave Qn unchanged, but alter Q* in the adjacent row.
theorem SourceLemma12_4Data.original_free_spike_diagonal_difference
    {hp : p ≠ ⊤} {hp1 : 1 < p} {W V : Set (CoeffPair p)}
    {D : ℤ → Set ℂ} {c : ℝ} (H : SourceLemma12_4Data hp hp1 W)
    (hD : SourceIsolatingNeighborhoods hp hp1 V D c)
    (h0W : (0:CoeffPair p) ∈ W) (h0V : (0:CoeffPair p) ∈ V)
    (n : ℤ) (t : ℂ) (ha : (lp.single p n t:Coeff p) ∈ sourcePsiOriginalRootPlacement D)
    (r : ℝ) (hr : 0 < r) (hrπ : r < Real.pi)
    (he : D (n+1) = ball ((Real.pi:ℂ)*((n+1:ℤ):ℂ)) r) :
    ((sourcePsiOriginalFullRootJacobian hp hp1 n (lp.single p n t) (0:CoeffPair p) -
        sourcePsiOriginalLimitOperator hp hp1 (lp.single p n t) (0:CoeffPair p))
      (lp.single p (n+1) 1)) (n+1) = 2*t/(Real.pi:ℂ) := by
  have hmn : n+1 ≠ n := by omega
  have hfill : sourcePsiOriginalJacobianEntry hp hp1 n (n+1) (n+1) (lp.single p n t) (0:CoeffPair p) = 2 := by
    have heq := sourcePsiOriginalJacobianEntry_add_single_deleted hp hp1 n (n+1) (n+1)
      (0:Coeff p) (0:CoeffPair p) t
    simp only [zero_add] at heq
    rw [heq]
    exact H.original_freeJacobian_diagonal hD h0W h0V n (n+1) hmn r hr hrπ he
  have hlim := H.originalLimitOperator_entry_contour hD 0 h0W h0V (by simp)
    (lp.single p n t) ha (n+1) (n+1) (Real.pi*((n+1:ℤ):ℝ)) r hr (by simpa using he)
  change (sourcePsiOriginalFullRootJacobian hp hp1 n (lp.single p n t) 0 (lp.single p (n+1) 1)) (n+1) -
    (sourcePsiOriginalLimitOperator hp hp1 (lp.single p n t) 0 (lp.single p (n+1) 1)) (n+1) = _
  rw [show (sourcePsiOriginalFullRootJacobian hp hp1 n (lp.single p n t) 0 (lp.single p (n+1) 1)) (n+1) = 2 from
    (sourcePsiOriginalFullRootJacobian_entry hp hp1 n (n+1) (n+1) hmn _ _).trans hfill]
  simp only [Complex.ofReal_mul,Complex.ofReal_intCast] at hlim
  rw [hlim,sourcePsiContour_free_single_diagonal hp hp1 (n+1) n hmn.symm r hr hrπ t]
  push_cast
  have hπ : (Real.pi:ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  field_simp [hπ]
  ring

theorem SourceIsolatingNeighborhoods.original_free_spike_placement
    {hp : p ≠ ⊤} {hp1 : 1 < p} {V : Set (CoeffPair p)}
    {D : ℤ → Set ℂ} {c : ℝ} (hD : SourceIsolatingNeighborhoods hp hp1 V D c)
    (h0V : (0:CoeffPair p) ∈ V) (n : ℤ) (hn : D n = refinedResonantDisk n)
    (t : ℂ) (ht : ‖t‖ < Real.pi/4) :
    (lp.single p n t:Coeff p) ∈ sourcePsiOriginalRootPlacement D := by
  intro k
  by_cases hkn : k = n
  · subst k
    simpa [hn,refinedResonantDisk,mem_ball,dist_eq_norm,displacedRoots] using ht
  · have hg := hD.gap 0 h0V k
    rw [sourcePeriodicSegment_zero_source hp hp1 k] at hg
    have hk : (Real.pi:ℂ)*k ∈ D k := hg (by simp)
    simpa [displacedRoots,Pi.single_eq_of_ne hkn] using hk

theorem SourceLemma12_4Data.original_free_spike_norm_lowerBound
    {hp : p ≠ ⊤} {hp1 : 1 < p} {W V : Set (CoeffPair p)}
    {D : ℤ → Set ℂ} {c : ℝ} (H : SourceLemma12_4Data hp hp1 W)
    (hD : SourceIsolatingNeighborhoods hp hp1 V D c)
    (h0W : (0:CoeffPair p) ∈ W) (h0V : (0:CoeffPair p) ∈ V)
    (n : ℤ) (t : ℂ) (ht : ‖t‖ < Real.pi/4)
    (hn : D n = refinedResonantDisk n) (hm : D (n+1) = refinedResonantDisk (n+1)) :
    2*‖t‖/Real.pi ≤ ‖sourcePsiOriginalFullRootJacobian hp hp1 n (lp.single p n t) (0:CoeffPair p) -
      sourcePsiOriginalLimitOperator hp hp1 (lp.single p n t) (0:CoeffPair p)‖ := by
  let Q := sourcePsiOriginalFullRootJacobian hp hp1 n (lp.single p n t) (0:CoeffPair p) -
    sourcePsiOriginalLimitOperator hp hp1 (lp.single p n t) (0:CoeffPair p)
  have he := H.original_free_spike_diagonal_difference hD h0W h0V n t
    (hD.original_free_spike_placement h0V n hn t ht) (Real.pi/4) (by positivity)
    (by linarith [Real.pi_pos]) hm
  have hb := (lp.norm_apply_le_norm (zero_lt_one.trans hp1).ne' (Q (lp.single p (n+1) 1)) (n+1)).trans
    (Q.le_opNorm (lp.single p (n+1) 1))
  change ‖(Q (lp.single p (n+1) 1)) (n+1)‖ ≤ ‖Q‖*‖(lp.single p (n+1) 1:Coeff p)‖ at hb
  rw [he] at hb
  simpa only [lp.norm_single (zero_lt_one.trans hp1),norm_one,mul_one,norm_div,norm_mul,
    Complex.norm_ofNat,Complex.norm_real,Real.norm_of_nonneg Real.pi_pos.le] using hb

-- In EVERY lp ball around zero, moving spikes prevent uniform operator-norm convergence.
theorem SourceLemma12_4Data.original_free_nonuniform_on_ball
    {hp : p ≠ ⊤} {hp1 : 1 < p} {W V : Set (CoeffPair p)}
    {D : ℤ → Set ℂ} {c : ℝ} (H : SourceLemma12_4Data hp hp1 W)
    (hD : SourceIsolatingNeighborhoods hp hp1 V D c)
    (h0W : (0:CoeffPair p) ∈ W) (h0V : (0:CoeffPair p) ∈ V)
    (r : ℝ) (hr : 0 < r) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ N : ℕ, ∃ n : ℤ, N ≤ n.natAbs ∧
      ∃ a : Coeff p, a ∈ ball 0 r ∧ a ∈ sourcePsiOriginalRootPlacement D ∧
        (∀ k : ℤ, (a k).im = 0) ∧
        ε ≤ ‖sourcePsiOriginalFullRootJacobian hp hp1 n a (0:CoeffPair p) -
          sourcePsiOriginalLimitOperator hp hp1 a (0:CoeffPair p)‖ := by
  let δ := min (r/2) (Real.pi/8)
  have hδ : 0 < δ := lt_min (by positivity) (by positivity)
  have hδr : δ < r := (min_le_left _ _).trans_lt (by linarith)
  have hδπ : δ < Real.pi/4 := (min_le_right _ _).trans_lt (by linarith [Real.pi_pos])
  obtain ⟨K,hK⟩ := hD.tail
  refine ⟨2*δ/Real.pi,by positivity,?_⟩
  intro N
  let n : ℤ := (K+N+1:ℕ)
  have hn : K < n.natAbs := by simp [n]; omega
  have hnN : N ≤ n.natAbs := by simp [n]; omega
  have hm : K < (n+1).natAbs := by
    have hn0 : 0 ≤ n := by dsimp [n]; positivity
    omega
  have hnorm : ‖(δ:ℂ)‖ = δ := by simp [hδ.le]
  have hsmall : ‖(δ:ℂ)‖ < Real.pi/4 := by rwa [hnorm]
  refine ⟨n,hnN,lp.single p n (δ:ℂ),?_,hD.original_free_spike_placement h0V n (hK n hn) _ hsmall,?_,?_⟩
  · simpa only [mem_ball,dist_zero_right,lp.norm_single (zero_lt_one.trans hp1),hnorm] using hδr
  · intro k
    by_cases hkn : k = n
    · subst k; simp
    · simp [Pi.single_eq_of_ne hkn]
  · simpa only [hnorm] using H.original_free_spike_norm_lowerBound hD h0W h0V n (δ:ℂ) hsmall
      (hK n hn) (hK (n+1) hm)

theorem SourceLemma12_4Data.original_free_not_tendstoUniformlyOn_ball
    {hp : p ≠ ⊤} {hp1 : 1 < p} {W V : Set (CoeffPair p)}
    {D : ℤ → Set ℂ} {c : ℝ} (H : SourceLemma12_4Data hp hp1 W)
    (hD : SourceIsolatingNeighborhoods hp hp1 V D c)
    (h0W : (0:CoeffPair p) ∈ W) (h0V : (0:CoeffPair p) ∈ V)
    (r : ℝ) (hr : 0 < r) :
    ¬ TendstoUniformlyOn
      (fun n : ℤ => fun a : Coeff p => sourcePsiOriginalFullRootJacobian hp hp1 n a (0:CoeffPair p))
      (fun a : Coeff p => sourcePsiOriginalLimitOperator hp hp1 a (0:CoeffPair p))
      (Filter.comap Int.natAbs atTop)
      {a : Coeff p | a ∈ ball 0 r ∧ a ∈ sourcePsiOriginalRootPlacement D ∧ ∀ k : ℤ, (a k).im = 0} := by
  intro h
  obtain ⟨ε,hε,hbad⟩ := H.original_free_nonuniform_on_ball hD h0W h0V r hr
  have hev := Metric.tendstoUniformlyOn_iff.mp h ε hε
  obtain ⟨N,hN⟩ := eventually_atTop.mp (eventually_comap.mp hev)
  obtain ⟨n,hn,a,har,haD,haR,hlo⟩ := hbad N
  have hhi := hN n.natAbs hn n rfl a ⟨har,haD,haR⟩
  have : ‖sourcePsiOriginalFullRootJacobian hp hp1 n a (0:CoeffPair p) -
      sourcePsiOriginalLimitOperator hp hp1 a (0:CoeffPair p)‖ < ε := by
    simpa only [dist_eq_norm,norm_sub_rev] using hhi
  exact (not_lt_of_ge hlo) this

/-- The same obstruction lies in the source's actual real Omega, with
its source-first product topology, on every ball about the free point. -/
theorem SourceLemma12_4Data.originalOmega_free_not_tendstoUniformlyOn_ball
    {hp : p ≠ ⊤} {hp1 : 1 < p} {W V : Set (CoeffPair p)}
    {D : ℤ → Set ℂ} {c : ℝ} (H : SourceLemma12_4Data hp hp1 W)
    (hD : SourceIsolatingNeighborhoods hp hp1 V D c)
    (h0W : (0:CoeffPair p) ∈ W) (h0V : (0:CoeffPair p) ∈ V)
    (r : ℝ) (hr : 0 < r) :
    ¬ TendstoUniformlyOn
      (fun (n : ℤ) (t : realTypeSourceSubmodule p × RealCoeff p) =>
        sourcePsiOriginalFullRootJacobian hp hp1 n (RealCoeff.complexCLM p t.2) t.1)
      (fun t : realTypeSourceSubmodule p × RealCoeff p =>
        sourcePsiOriginalLimitOperator hp hp1 (RealCoeff.complexCLM p t.2) t.1)
      (Filter.comap Int.natAbs atTop) (ball 0 r ∩ sourcePsiOriginalOmega V D) := by
  intro h
  obtain ⟨ε,hε,hbad⟩ := H.original_free_nonuniform_on_ball hD h0W h0V r hr
  obtain ⟨N,hN⟩ := eventually_atTop.mp (eventually_comap.mp
    (Metric.tendstoUniformlyOn_iff.mp h ε hε))
  obtain ⟨n,hn,a,har,haD,haR,hlo⟩ := hbad N
  let t : realTypeSourceSubmodule p × RealCoeff p := (0,Coeff.reCLM p a)
  have hta : RealCoeff.complexCLM p t.2 = a := RealCoeff.complexCLM_reCLM p a haR
  have htr : t ∈ ball 0 r := by
    have haNorm : ‖a‖ < r := by simpa only [mem_ball,dist_zero_right] using har
    have htNorm := (Coeff.Complexification.norm_re_le a).trans_lt haNorm
    simpa [t,mem_ball,dist_zero_right,Prod.norm_def] using htNorm
  have htD : t ∈ sourcePsiOriginalOmega V D := ⟨h0V,hta ▸ haD⟩
  have hhi := hN n.natAbs hn n rfl t ⟨htr,htD⟩
  have : ‖sourcePsiOriginalFullRootJacobian hp hp1 n a (0:CoeffPair p)-
      sourcePsiOriginalLimitOperator hp hp1 a (0:CoeffPair p)‖ < ε := by
    simpa only [dist_eq_norm,hta,t,ZeroMemClass.coe_zero,norm_sub_rev] using hhi
  exact (not_lt_of_ge hlo) this

/-- No fixed neighborhood of the free point inside the original Omega
supports uniform operator-norm convergence. -/
theorem SourceLemma12_4Data.originalOmega_free_no_uniform_neighborhood
    {hp : p ≠ ⊤} {hp1 : 1 < p} {W V : Set (CoeffPair p)}
    {D : ℤ → Set ℂ} {c : ℝ} (H : SourceLemma12_4Data hp hp1 W)
    (hD : SourceIsolatingNeighborhoods hp hp1 V D c)
    (h0W : (0:CoeffPair p) ∈ W) (h0V : (0:CoeffPair p) ∈ V) :
    ¬ ∃ U ∈ 𝓝[sourcePsiOriginalOmega V D] (0 : realTypeSourceSubmodule p × RealCoeff p),
      TendstoUniformlyOn
        (fun (n : ℤ) (t : realTypeSourceSubmodule p × RealCoeff p) =>
          sourcePsiOriginalFullRootJacobian hp hp1 n (RealCoeff.complexCLM p t.2) t.1)
        (fun t : realTypeSourceSubmodule p × RealCoeff p =>
          sourcePsiOriginalLimitOperator hp hp1 (RealCoeff.complexCLM p t.2) t.1)
        (Filter.comap Int.natAbs atTop) U := by
  rintro ⟨U,hU,hconv⟩
  obtain ⟨r,hr,hball⟩ := Metric.mem_nhdsWithin_iff.mp hU
  exact H.originalOmega_free_not_tendstoUniformlyOn_ball hD h0W h0V r hr (hconv.mono hball)

/-- The obstruction occurs for an existing original isolating family at the
free source, for every finite exponent above one. -/
theorem sourceLemma12_10_no_fixedUniformNeighborhood (hp : p ≠ ⊤) (hp1 : 1 < p) :
    ∃ V : Set (CoeffPair p), ∃ D : ℤ → Set ℂ, ∃ c : ℝ,
      IsOpen V ∧ (0:CoeffPair p) ∈ V ∧ SourceIsolatingNeighborhoods hp hp1 V D c ∧
      ¬ ∃ U ∈ 𝓝[sourcePsiOriginalOmega V D] (0 : realTypeSourceSubmodule p × RealCoeff p),
        TendstoUniformlyOn
          (fun (n : ℤ) (t : realTypeSourceSubmodule p × RealCoeff p) =>
            sourcePsiOriginalFullRootJacobian hp hp1 n (RealCoeff.complexCLM p t.2) t.1)
          (fun t : realTypeSourceSubmodule p × RealCoeff p =>
            sourcePsiOriginalLimitOperator hp hp1 (RealCoeff.complexCLM p t.2) t.1)
          (Filter.comap Int.natAbs atTop) U := by
  obtain ⟨W,_,_,hR,H⟩ := sourceProposition12_9 hp hp1
  let H4 := H.previous.previous.previous.previous.previous
  have h0W : (0:CoeffPair p) ∈ W := hR (by simp [realTypeSourceLocus])
  obtain ⟨V,hV,_,h0V,_,D,c,hD⟩ := H4.previous.quotients.neighborhoods 0 h0W
  exact ⟨V,D,c,hV,h0V,hD.toSourceIsolatingNeighborhoods,
    H4.originalOmega_free_no_uniform_neighborhood hD.toSourceIsolatingNeighborhoods h0W h0V⟩

end NLS.ZakharovShabat
