import NLS.KdV.HillFullProductUniformLimit
import NLS.KdV.HillAbelianComplexPeriods
import NLS.KdV.HillIntrinsicPeriodLinearity
import NLS.ComplexAnalysis.CompactParameterBounds
import NLS.ComplexAnalysis.NormalizedCircleIntegralBounds

noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology
open NLS.ComplexAnalysis NLS.ZakharovShabat
open scoped ENNReal ComplexConjugate Classical

namespace NLS.KdV



variable (q : WeightedCoeff SpectralWeight.one.toWeight 2)
    (hq : SpectralWeight.one.toCoeff q∈Coeff.paritySubspace 0)
    (hr : IsRealHillPotential (SpectralWeight.one.toCoeff q))

/-- Original contour period of the actual omitted product; n=0 is
the full-product period, without a singular differential prefactor. -/
def hillAbelianProductComplexPeriod (n k : ℕ) (t : Coeff 2 × Coeff 2) : ℂ :=
  (2*(Real.pi : ℂ))⁻¹ * ∮ E in C((hillRealGapCenter q hq hr k : ℂ),
    hillRealGapHalfLength q hq hr k+hillRealGapCollar q hq hr k),
    hillAbelianHilbertProduct n (E,t.1)/hillAbelianComplexRoot q hq hr (E,t.2)

theorem analyticOnNhd_hillAbelianProductComplexPeriod_of_domain
    (n k : ℕ) (hk : 1 ≤ k) (U : Set (Coeff 2)) (hU : IsOpen U)
    (hcircle : ∀ p ∈ U, ∀ z ∈ sphere (hillRealGapCenter q hq hr k : ℂ)
      (hillRealGapHalfLength q hq hr k+hillRealGapCollar q hq hr k),
      (z,p) ∈ hillAbelianComplexRootDomain q hq hr) :
    AnalyticOnNhd ℂ (hillAbelianProductComplexPeriod q hq hr n k) (univ ×ˢ U) := by
  let J : ℂ × (Coeff 2 × Coeff 2) → ℂ × Coeff 2 := fun v => (v.1,v.2.2)
  let K : ℂ × (Coeff 2 × Coeff 2) → ℂ × Coeff 2 := fun v => (v.1,v.2.1)
  let D := J ⁻¹' hillAbelianComplexRootDomain q hq hr
  let F : ℂ × (Coeff 2 × Coeff 2) → ℂ := fun v =>
    hillAbelianHilbertProduct n (K v)/hillAbelianComplexRoot q hq hr (J v)
  have hJ : AnalyticOnNhd ℂ J univ := by
    intro v _
    exact analyticAt_fst.prod (analyticAt_snd.comp analyticAt_snd)
  have hK : AnalyticOnNhd ℂ K univ := by
    intro v _
    exact analyticAt_fst.prod (analyticAt_fst.comp analyticAt_snd)
  have hD : IsOpen D := (isOpen_hillAbelianComplexRootDomain q hq hr).preimage
    (continuousOn_univ.mp hJ.continuousOn)
  have hF : AnalyticOnNhd ℂ F D := by
    intro v hv
    have hn := (analyticOnNhd_hillAbelianHilbertProduct n (K v) (mem_univ _)).comp (hK v (mem_univ _))
    have hd := (analyticOnNhd_hillAbelianComplexRoot q hq hr (J v) hv).comp (hJ v (mem_univ _))
    exact hn.div hd (hillAbelianComplexRoot_ne_zero q hq hr (J v) hv)
  have hR := add_nonneg (hillRealGapContour_geometry q hq hr k hk).1
    (hillRealGapContour_geometry q hq hr k hk).2.1.le
  have hc := analyticOnNhd_circleIntegral_of_jointAnalytic F hD hF
    (hillRealGapCenter q hq hr k : ℂ)
    (hillRealGapHalfLength q hq hr k + hillRealGapCollar q hq hr k) hR
    (isOpen_univ.prod hU)
    (fun t ht z hz => hcircle t.2 ht.2 z hz)
  exact analyticOnNhd_const.mul hc


/-- The original differential period is exactly the rescaled product
period for each positive differential index. -/
theorem hillAbelianProductComplexPeriod_eq_rescaled (n k : ℕ) (hn : 1≤n) (t : Coeff 2 × Coeff 2) :
    hillAbelianProductComplexPeriod q hq hr n k t=
      ((n : ℂ)*Real.pi/2)*hillAbelianComplexPeriod q hq hr n k t := by
  have hn0 : (n : ℂ)≠0 := by exact_mod_cast (by omega : n≠0)
  have hp0 : (Real.pi : ℂ)≠0 := ofReal_ne_zero.mpr Real.pi_ne_zero
  have he (E : ℂ) : hillAbelianHilbertProduct n (E,t.1)=
      ((n : ℂ)*Real.pi/2)*hillAbelianHilbertPsi n (E,t.1) := by
    rw [hillAbelianHilbertPsi]
    field_simp
  unfold hillAbelianProductComplexPeriod hillAbelianComplexPeriod
  simp_rw [he,mul_div_assoc]
  rw [circleIntegral.integral_const_mul]
  ring

/-- At the base source this is exactly the original physical contour
functional of the omitted product, including the full product at zero. -/
theorem hillAbelianProductComplexPeriod_at_base (n k : ℕ) (hk : 1≤k) (a : Coeff 2) :
    hillAbelianProductComplexPeriod q hq hr n k (a,SpectralWeight.one.toCoeff q)=
      hillIntrinsicGapPeriod q hq hr k (fun E => hillAbelianHilbertProduct n (E,a)) := by
  unfold hillAbelianProductComplexPeriod hillIntrinsicGapPeriod
  congr 1
  apply circleIntegral.integral_congr
    (add_nonneg (hillRealGapContour_geometry q hq hr k hk).1 (hillRealGapContour_geometry q hq hr k hk).2.1.le)
  intro E hE
  dsimp only []
  rw [hillAbelianComplexRoot_base q hq hr E (hillRealGapContour_sphere_subset q hq hr k hk hE)]

private theorem hillAbelianProductIntegrand_circleIntegrable
    (n k : ℕ) (hk : 1≤k) (a p : Coeff 2)
    (hd : ∀ E∈sphere (hillRealGapCenter q hq hr k : ℂ)
      (hillRealGapHalfLength q hq hr k+hillRealGapCollar q hq hr k),
      (E,p)∈hillAbelianComplexRootDomain q hq hr) :
    CircleIntegrable (fun E => hillAbelianHilbertProduct n (E,a)/hillAbelianComplexRoot q hq hr (E,p))
      (hillRealGapCenter q hq hr k : ℂ) (hillRealGapHalfLength q hq hr k+hillRealGapCollar q hq hr k) := by
  apply ContinuousOn.circleIntegrable
    (add_nonneg (hillRealGapContour_geometry q hq hr k hk).1 (hillRealGapContour_geometry q hq hr k hk).2.1.le)
  intro E hE
  have ha := (analyticOnNhd_hillAbelianHilbertProduct n (E,a) (mem_univ _)).comp
    (f := fun E : ℂ => (E,a)) (analyticAt_id.prod analyticAt_const)
  have hroota := (analyticOnNhd_hillAbelianComplexRoot q hq hr (E,p) (hd E hE)).comp
    (f := fun E : ℂ => (E,p)) (analyticAt_id.prod analyticAt_const)
  exact (ha.div hroota (hillAbelianComplexRoot_ne_zero q hq hr (E,p) (hd E hE))).continuousAt.continuousWithinAt

/-- Around every real source, each fixed original contour period of
the omitted products converges to the full-product period uniformly
on bounded root balls, with a source neighborhood before n. -/
theorem exists_hillAbelianProductComplexPeriod_full_uniform_bound
    (k : ℕ) (hk : 1≤k) (B : ℝ) (hB : 0≤B) :
    ∃ U : Set (Coeff 2), ∃ C : ℝ, IsOpen U ∧ SpectralWeight.one.toCoeff q∈U ∧ 0<C ∧
      (∀ n : ℕ, AnalyticOnNhd ℂ (hillAbelianProductComplexPeriod q hq hr n k) (univ ×ˢ U)) ∧
      ∀ n : ℕ, 1≤n → ∀ a : Coeff 2, ‖a‖≤B → ∀ p∈U,
        ‖hillAbelianProductComplexPeriod q hq hr n k (a,p)-
          hillAbelianProductComplexPeriod q hq hr 0 k (a,p)‖≤C/(n : ℝ) := by
  let c : ℂ := hillRealGapCenter q hq hr k
  let R := hillRealGapHalfLength q hq hr k+hillRealGapCollar q hq hr k
  let D := hillAbelianComplexRootDomain q hq hr
  have hR : 0<R := add_pos_of_nonneg_of_pos (hillRealGapContour_geometry q hq hr k hk).1
    (hillRealGapContour_geometry q hq hr k hk).2.1
  have hi : ContinuousOn (fun v : ℂ × Coeff 2 => (hillAbelianComplexRoot q hq hr v)⁻¹) D := by
    intro v hv
    exact (((analyticOnNhd_hillAbelianComplexRoot q hq hr v hv).inv
      (hillAbelianComplexRoot_ne_zero q hq hr v hv)).continuousAt).continuousWithinAt
  obtain ⟨U,hU,hqU,D0,hD0,hroot⟩ := exists_local_uniform_bound_on_compact_of_continuousOn
    (fun v : ℂ × Coeff 2 => (hillAbelianComplexRoot q hq hr v)⁻¹) D
    (isOpen_hillAbelianComplexRootDomain q hq hr) hi (sphere c R) (isCompact_sphere c R)
    (SpectralWeight.one.toCoeff q) (fun E hE => mem_hillAbelianComplexRootDomain_base q hq hr E
      (hillRealGapContour_sphere_subset q hq hr k hk hE))
  let T := ‖c‖+R+B+1
  have hT : 0≤T := by dsimp only [T];positivity
  obtain ⟨A,hA,hprod⟩ := exists_hillAbelianHilbertProduct_full_uniform_bound T hT
  let C := R*A*(D0+1)+1
  have hC : 0<C := by dsimp only [C];positivity
  have hdom (p : Coeff 2) (hp : p∈U) (E : ℂ) (hE : E∈sphere c R) : (E,p)∈D :=
    (hroot p hp E hE).1
  refine ⟨U,C,hU,hqU,hC,(fun n => analyticOnNhd_hillAbelianProductComplexPeriod_of_domain q hq hr n k hk U hU hdom),?_⟩
  intro n hn a ha p hp
  have hnpos : (0:ℝ)<n := by exact_mod_cast (by omega : 0<n)
  have hbd (E : ℂ) (hE : E∈sphere c R) :
      ‖(1 : ℂ)*(hillAbelianHilbertProduct n (E,a)/hillAbelianComplexRoot q hq hr (E,p)-
        hillAbelianHilbertProduct 0 (E,a)/hillAbelianComplexRoot q hq hr (E,p))‖≤A*(D0+1)/(n : ℝ) := by
    have hEt : ‖(E,a)‖≤T := by
      have hEc : ‖E-c‖=R := by simpa only [mem_sphere,dist_eq_norm] using hE
      have hh := norm_le_norm_sub_add E c
      rw [Prod.norm_def]
      dsimp only [T]
      exact max_le (by linarith) (by linarith [norm_nonneg c])
    rw [one_mul,←sub_div,div_eq_mul_inv,norm_mul]
    have hinv : ‖(hillAbelianComplexRoot q hq hr (E,p))⁻¹‖≤D0+1 :=
      (hroot p hp E hE).2.trans (by linarith)
    have hb := mul_le_mul (hprod n hn (E,a) hEt) hinv (norm_nonneg _) (by positivity : 0≤A/(n : ℝ))
    exact hb.trans_eq (by ring)
  have hh := norm_normalized_circleIntegral_difference_le
    (fun E => hillAbelianHilbertProduct n (E,a)/hillAbelianComplexRoot q hq hr (E,p))
    (fun E => hillAbelianHilbertProduct 0 (E,a)/hillAbelianComplexRoot q hq hr (E,p))
    c 1 R (A*(D0+1)/(n : ℝ)) hR.le
    (hillAbelianProductIntegrand_circleIntegrable q hq hr n k hk a p (hdom p hp))
    (hillAbelianProductIntegrand_circleIntegrable q hq hr 0 k hk a p (hdom p hp)) hbd
  rw [one_mul] at hh
  apply hh.trans
  change R*(A*(D0+1)/(n : ℝ))≤C/(n : ℝ)
  rw [show R*(A*(D0+1)/(n : ℝ))=(R*A*(D0+1))/(n : ℝ) by ring]
  exact div_le_div_of_nonneg_right (by dsimp only [C];linarith) hnpos.le

/-- On the same kind of common source neighborhood, the root derivatives
of each original fixed-gap product period converge in operator norm. -/
theorem exists_hillAbelianProductComplexPeriod_full_root_derivative_uniform_bound
    (k : ℕ) (hk : 1≤k) (B : ℝ) (hB : 0≤B) :
    ∃ U : Set (Coeff 2), ∃ C : ℝ, IsOpen U ∧ SpectralWeight.one.toCoeff q∈U ∧ 0<C ∧
      ∀ n : ℕ, 1≤n → ∀ a : Coeff 2, ‖a‖≤B → ∀ p∈U,
        ‖fderiv ℂ (fun b => hillAbelianProductComplexPeriod q hq hr n k (b,p)) a-
          fderiv ℂ (fun b => hillAbelianProductComplexPeriod q hq hr 0 k (b,p)) a‖≤C/(n : ℝ) := by
  obtain ⟨U,C,hU,hqU,hC,ha,hbound⟩ := exists_hillAbelianProductComplexPeriod_full_uniform_bound q hq hr k hk (B+2) (by positivity)
  refine ⟨U,2*C,hU,hqU,by positivity,?_⟩
  intro n hn a hab p hp
  have hslice (j : ℕ) : AnalyticOnNhd ℂ (fun b => hillAbelianProductComplexPeriod q hq hr j k (b,p)) univ := by
    intro b _
    exact (ha j (b,p) ⟨mem_univ _,hp⟩).comp (f := fun b : Coeff 2 => (b,p)) (analyticAt_id.prod analyticAt_const)
  let f : Coeff 2 → ℂ := fun b => hillAbelianProductComplexPeriod q hq hr n k (b,p)-
    hillAbelianProductComplexPeriod q hq hr 0 k (b,p)
  have hf : AnalyticOnNhd ℂ f univ := (hslice n).sub (hslice 0)
  have hh := norm_fderiv_le_of_ball_bound f 0 a (B+1) 1 (C/(n : ℝ)) (by norm_num)
    (hf.differentiableOn.mono (subset_univ _)) (fun b hb => hbound n hn b (by
      have hh : ‖b‖<(B+1)+1 := by simpa only [mem_ball,dist_zero_right] using hb
      linarith) p hp) (by simpa only [mem_ball,dist_zero_right] using (by linarith : ‖a‖<B+1))
  have hd : fderiv ℂ f a=fderiv ℂ (fun b => hillAbelianProductComplexPeriod q hq hr n k (b,p)) a-
      fderiv ℂ (fun b => hillAbelianProductComplexPeriod q hq hr 0 k (b,p)) a :=
    (((hslice n) a (mem_univ _)).differentiableAt.hasFDerivAt.sub
      (((hslice 0) a (mem_univ _)).differentiableAt.hasFDerivAt)).fderiv
  rw [hd] at hh
  exact hh.trans_eq (by ring)

end NLS.KdV
