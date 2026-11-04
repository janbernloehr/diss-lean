import NLS.KdV.HillProductPeriodUniformLimit

noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology
open NLS.ComplexAnalysis NLS.ZakharovShabat
open scoped ENNReal ComplexConjugate Classical

namespace NLS.KdV



variable (q : WeightedCoeff SpectralWeight.one.toWeight 2)
    (hq : SpectralWeight.one.toCoeff q∈Coeff.paritySubspace 0)
    (hr : IsRealHillPotential (SpectralWeight.one.toCoeff q))

private theorem hillAbelianProductIntegrand_circleIntegrable_at_parameter
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


/-- Uniform original product-period limits at any complex base parameter
whose whole original fixed contour lies in the actual root domain. -/
theorem exists_hillAbelianProductComplexPeriod_full_uniform_bound_at_parameter
    (k : ℕ) (hk : 1≤k) (pbase : Coeff 2)
    (hbase : ∀ E∈sphere (hillRealGapCenter q hq hr k : ℂ)
      (hillRealGapHalfLength q hq hr k+hillRealGapCollar q hq hr k),
      (E,pbase)∈hillAbelianComplexRootDomain q hq hr) (B : ℝ) (hB : 0≤B) :
    ∃ U : Set (Coeff 2), ∃ C : ℝ, IsOpen U ∧ pbase∈U ∧ 0<C ∧
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
    pbase hbase
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
    (hillAbelianProductIntegrand_circleIntegrable_at_parameter q hq hr n k hk a p (hdom p hp))
    (hillAbelianProductIntegrand_circleIntegrable_at_parameter q hq hr 0 k hk a p (hdom p hp)) hbd
  rw [one_mul] at hh
  apply hh.trans
  change R*(A*(D0+1)/(n : ℝ))≤C/(n : ℝ)
  rw [show R*(A*(D0+1)/(n : ℝ))=(R*A*(D0+1))/(n : ℝ) by ring]
  exact div_le_div_of_nonneg_right (by dsimp only [C];linarith) hnpos.le


/-- Actual product-period convergence at every admissible complex source. -/
theorem tendsto_hillAbelianProductComplexPeriod_full_at_parameter
    (k : ℕ) (hk : 1≤k) (a p : Coeff 2)
    (hbase : ∀ E∈sphere (hillRealGapCenter q hq hr k : ℂ)
      (hillRealGapHalfLength q hq hr k+hillRealGapCollar q hq hr k),
      (E,p)∈hillAbelianComplexRootDomain q hq hr) :
    Tendsto (fun n : ℕ => hillAbelianProductComplexPeriod q hq hr n k (a,p)) atTop
      (𝓝 (hillAbelianProductComplexPeriod q hq hr 0 k (a,p))) := by
  obtain ⟨U,C,_,hpU,_,_,hbound⟩ := exists_hillAbelianProductComplexPeriod_full_uniform_bound_at_parameter q hq hr k hk p hbase ‖a‖ (norm_nonneg a)
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  apply squeeze_zero' (Eventually.of_forall (fun _ => norm_nonneg _)) _
    ((tendsto_natCast_atTop_atTop : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop).const_div_atTop C)
  filter_upwards [eventually_ge_atTop 1] with n hn
  exact hbound n hn a le_rfl p hpU

/-- The original mixed-period scaling converges to minus 2*pi times
the genuine full-product contour period, retaining the source normalization. -/
theorem tendsto_scaled_hillAbelianComplexPeriod_full_at_parameter
    (k : ℕ) (hk : 1≤k) (a p : Coeff 2)
    (hbase : ∀ E∈sphere (hillRealGapCenter q hq hr k : ℂ)
      (hillRealGapHalfLength q hq hr k+hillRealGapCollar q hq hr k),
      (E,p)∈hillAbelianComplexRootDomain q hq hr) :
    Tendsto (fun n : ℕ => (((freeHillValue k : ℂ)-(freeHillValue n : ℂ))/(n : ℂ))*
      hillAbelianComplexPeriod q hq hr n k (a,p)) atTop
      (𝓝 ((-2*(Real.pi : ℂ))*hillAbelianProductComplexPeriod q hq hr 0 k (a,p))) := by
  have hinvReal : Tendsto (fun n : ℕ => (n : ℝ)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop
  have hc : Tendsto (fun n : ℕ => (n : ℂ)⁻¹) atTop (𝓝 0) := by
    simpa only [Function.comp_def,ofReal_inv,ofReal_natCast,ofReal_zero] using (Complex.continuous_ofReal.tendsto 0).comp hinvReal
  let c : ℕ → ℂ := fun n => -2*(Real.pi : ℂ)+(2*(freeHillValue k : ℂ)/(Real.pi : ℂ))*((n : ℂ)⁻¹)^2
  have hclim : Tendsto c atTop (𝓝 (-2*(Real.pi : ℂ))) := by
    simpa only [zero_pow (by norm_num : (2:ℕ)≠0),mul_zero,add_zero] using
      (hc.pow 2).const_mul (2*(freeHillValue k : ℂ)/(Real.pi : ℂ)) |>.const_add (-2*(Real.pi : ℂ))
  have hprod := tendsto_hillAbelianProductComplexPeriod_full_at_parameter q hq hr k hk a p hbase
  apply (hclim.mul hprod).congr'
  filter_upwards [eventually_ge_atTop 1] with n hn
  have hn0 : (n : ℂ)≠0 := by exact_mod_cast (by omega : n≠0)
  have hp0 : (Real.pi : ℂ)≠0 := ofReal_ne_zero.mpr Real.pi_ne_zero
  have hfree : (freeHillValue n : ℂ)=(Real.pi : ℂ)^2*(n : ℂ)^2 := by
    simp only [freeHillValue,ofReal_mul,ofReal_pow]
    push_cast
    rfl
  have he : c n*((n : ℂ)*Real.pi/2)=((freeHillValue k : ℂ)-(freeHillValue n : ℂ))/(n : ℂ) := by
    dsimp only [c]
    rw [hfree]
    field_simp
    ring
  rw [hillAbelianProductComplexPeriod_eq_rescaled q hq hr n k hn,←mul_assoc,he]

end NLS.KdV
