import NLS.KdV.HillHminusOneReflection
import NLS.KdV.HillL2HalfPlaneSheets

/-! # Physical half-plane sheet signs for every real H^-1 potential

Real L2 density and joint continuity give the weak upper sign. The
maximum modulus principle and the proved nonconstant H^-1 trace make it
strict. Reflection fixes the lower sign and both multiplier moduli.
-/
noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology NLS.ComplexAnalysis
open scoped ComplexConjugate
namespace NLS.KdV

/-- The physical L2 sheet sign in the original unit-period inclusion. -/
theorem hillHminusContinuedPrimitive_re_nonneg_L2 (a : PeriodOneRealL2)
    (z : ℂ) (hz : 0 < z.im) :
    0 ≤ (hillHminusContinuedPrimitive (z,periodOneL2Inclusion a.val)).re := by
  let Q : WeightedCoeff SpectralWeight.one.toWeight 2 :=
    ⟨Coeff.periodDouble a.val,by
      change Memℓp (fun k => (SpectralWeight.one.toWeight k : ℂ)*Coeff.periodDouble a.val k) 2
      simpa using lp.memℓp (Coeff.periodDouble a.val)⟩
  have hQ : SpectralWeight.one.toCoeff Q = Coeff.periodDouble a.val := by
    ext k
    exact SpectralWeight.toCoeff_apply _ _ k
  have hpar : SpectralWeight.one.toCoeff Q ∈ Coeff.paritySubspace 0 := by
    rw [hQ]
    exact Coeff.periodDouble_mem a.val
  have hreal : IsRealHillPotential (SpectralWeight.one.toCoeff Q) := by
    rw [hQ]
    exact IsRealHillPotential.periodDouble a.property
  have hd : (z,Coeff.periodDouble a.val) ∈ hillL2ContinuationDomain := by
    rw [← hQ]
    exact mem_hillL2ContinuationDomain_of_im_ne_zero Q hpar hreal z hz.ne'
  rw [hillHminusContinuedPrimitive_eq_hillL2 z a.val hd,← hQ]
  exact hillL2ContinuedPrimitive_re_nonneg Q hpar hreal z hz

/-- The physical sheet sign survives the full H^-1 limit, without a
bounded L2 norm for the real approximants. -/
theorem hillHminusContinuedPrimitive_re_nonneg (q : PeriodOneHminusOne)
    (hq : IsRealPeriodOneHminusOne q) (z : ℂ) (hz : 0 < z.im) :
    0 ≤ (hillHminusContinuedPrimitive (z,q)).re := by
  have hm : Continuous (fun a : PeriodOneRealHminusOne => (z,a.val)) :=
    continuous_const.prodMk continuous_subtype_val
  have hp : Continuous (fun a : PeriodOneRealHminusOne => hillHminusContinuedPrimitive (z,a.val)) :=
    ContinuousOn.comp_continuous (g := hillHminusContinuedPrimitive)
      (f := fun a : PeriodOneRealHminusOne => (z,a.val))
      analyticOnNhd_hillHminusContinuedPrimitive.continuousOn hm
      (fun a => mem_hillHminusContinuationDomain_of_im_ne_zero a.val a.property z hz.ne')
  have hG : Continuous (fun a : PeriodOneRealHminusOne => (hillHminusContinuedPrimitive (z,a.val)).re) :=
    Continuous.comp (g := Complex.re)
      (f := fun a : PeriodOneRealHminusOne => hillHminusContinuedPrimitive (z,a.val)) continuous_re hp
  have hsubset : range periodOneRealL2Inclusion ⊆
      {a : PeriodOneRealHminusOne | 0 ≤ (hillHminusContinuedPrimitive (z,a.val)).re} := by
    rintro _ ⟨a,rfl⟩
    exact hillHminusContinuedPrimitive_re_nonneg_L2 a z hz
  have hclosed : IsClosed {a : PeriodOneRealHminusOne | 0 ≤ (hillHminusContinuedPrimitive (z,a.val)).re} :=
    isClosed_le continuous_const hG
  have hpoint : (⟨q,hq⟩ : PeriodOneRealHminusOne) ∈
      {a : PeriodOneRealHminusOne | 0 ≤ (hillHminusContinuedPrimitive (z,a.val)).re} :=
    closure_minimal hsubset hclosed (denseRange_periodOneRealL2Inclusion ⟨q,hq⟩)
  exact hpoint

/-- The actual free-normalized H^-1 primitive selects the expanding
Floquet sheet on the complete upper energy half-plane. -/
theorem hillHminusContinuedPrimitive_re_pos (q : PeriodOneHminusOne)
    (hq : IsRealPeriodOneHminusOne q) (z : ℂ) (hz : 0 < z.im) :
    0 < (hillHminusContinuedPrimitive (z,q)).re := by
  let F : ℂ → ℂ := fun w => hillHminusContinuedPrimitive (w,q)
  let U : Set ℂ := {w | 0 < w.im}
  have hU : IsOpen U := isOpen_lt continuous_const continuous_im
  have hF : AnalyticOnNhd ℂ F U :=
    (analyticOnNhd_hillHminusContinuedPrimitive_off_real q hq).mono (fun _ hw => hw.ne')
  have hD : AnalyticOnNhd ℂ (hillHminusDiscriminant q) univ := by
    intro w _
    exact (analyticOnNhd_hillHminusDiscriminant_joint (w,q) (mem_univ _)).comp
      (f := fun w : ℂ => (w,q)) (analyticAt_id.prod analyticAt_const)
  have hnot : ¬ ∃ c : ℂ, ∀ w ∈ U, F w = c := by
    rintro ⟨c,hc⟩
    have hi : I ∈ U := by simp [U]
    have heq : hillHminusDiscriminant q =ᶠ[𝓝 I] (fun _ => 2*cosh c) := by
      filter_upwards [hU.mem_nhds hi] with w hw
      rw [← (hillHminusContinuedPrimitive_trace _
        (mem_hillHminusContinuationDomain_of_im_ne_zero q hq w hw.ne')).1]
      change 2*cosh (F w) = 2*cosh c
      rw [hc w hw]
    have he := hD.eqOn_of_preconnected_of_eventuallyEq analyticOnNhd_const
      isPreconnected_univ (mem_univ I) heq
    exact hillHminusDiscriminant_not_constant q ⟨2*cosh c,fun w => he (mem_univ w)⟩
  exact re_pos_of_analyticOnNhd_nonneg_not_constant F U hU
    (convex_halfSpace_im_gt 0).isPreconnected hF
    (fun w hw => hillHminusContinuedPrimitive_re_nonneg q hq w hw) hnot z hz

theorem hillHminusContinuedPrimitive_re_neg (q : PeriodOneHminusOne)
    (hq : IsRealPeriodOneHminusOne q) (z : ℂ) (hz : z.im < 0) :
    (hillHminusContinuedPrimitive (z,q)).re < 0 := by
  have hp := hillHminusContinuedPrimitive_re_pos q hq (conj z)
    (by simpa only [conj_im] using neg_pos.mpr hz)
  rw [hillHminusContinuedPrimitive_conj q hq z
    (mem_hillHminusContinuationDomain_of_im_ne_zero q hq z hz.ne),neg_re,conj_re] at hp
  linarith

theorem one_lt_norm_hillHminusContinuedMultiplier (q : PeriodOneHminusOne)
    (hq : IsRealPeriodOneHminusOne q) (z : ℂ) (hz : 0 < z.im) :
    1 < ‖hillHminusContinuedMultiplier (z,q)‖ := by
  rw [← exp_hillHminusContinuedPrimitive _
    (mem_hillHminusContinuationDomain_of_im_ne_zero q hq z hz.ne'),norm_exp,Real.one_lt_exp_iff]
  exact hillHminusContinuedPrimitive_re_pos q hq z hz

theorem norm_hillHminusContinuedMultiplier_lt_one (q : PeriodOneHminusOne)
    (hq : IsRealPeriodOneHminusOne q) (z : ℂ) (hz : z.im < 0) :
    ‖hillHminusContinuedMultiplier (z,q)‖ < 1 := by
  rw [← exp_hillHminusContinuedPrimitive _
    (mem_hillHminusContinuationDomain_of_im_ne_zero q hq z hz.ne),norm_exp,Real.exp_lt_one_iff]
  exact hillHminusContinuedPrimitive_re_neg q hq z hz

end NLS.KdV
