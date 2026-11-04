import NLS.ComplexAnalysis.ParametricCircleStationarity
import NLS.ComplexAnalysis.ParametricCircleTransforms
import NLS.ComplexAnalysis.ParametricConvexPrimitive
import NLS.ComplexAnalysis.QuotientDerivative

/-! # Stationary source derivatives of actual integral transforms -/
noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology MeasureTheory
namespace NLS.ComplexAnalysis
variable {A : Type} [NormedAddCommGroup A] [NormedSpace ℂ A]

/-- Cauchy transforms preserve source stationarity off their actual circle. -/
theorem fderiv_parametricCircleCauchyTransform_source_apply_eq_zero
    (F : ℂ × A → ℂ) (D : Set (ℂ × A)) (hD : IsOpen D) (hF : AnalyticOnNhd ℂ F D)
    (c : ℂ) (r : ℝ) (hr : 0≤r) (a v : A) (E : ℂ) (hE : E∉sphere c r)
    (hc : ∀ w∈sphere c r, (w,a)∈D)
    (hz : ∀ w∈sphere c r, (fderiv ℂ (fun p : A => F (w,p)) a) v=0) :
    (fderiv ℂ (fun p : A => parametricCircleCauchyTransform F c r (E,p)) a) v=0 := by
  let U := D ∩ {t : ℂ × A | t.1≠E}
  let G (t : ℂ × A) := F t/(t.1-E)
  have hU : IsOpen U := hD.inter (isOpen_ne_fun continuous_fst continuous_const)
  have hG : AnalyticOnNhd ℂ G U := fun t ht =>
    (hF t ht.1).div (analyticAt_fst.sub analyticAt_const) (sub_ne_zero.mpr ht.2)
  have hraw : (fderiv ℂ (fun p : A => ∮ w in C(c,r),G (w,p)) a) v=0 := by
    apply fderiv_circleIntegral_apply_eq_zero_of_jointAnalytic G U hU hG c r hr a v
      (fun w hw => ⟨hc w hw,fun he => hE (he ▸ hw)⟩)
    intro w hw
    have hsec := (hF (w,a) (hc w hw)).comp
      (f := fun p : A => (w,p)) (analyticAt_const.prod analyticAt_id)
    have hne : w-E≠0 := sub_ne_zero.mpr (fun he => hE (he ▸ hw))
    change (fderiv ℂ (fun p : A => F (w,p)/(w-E)) a) v=0
    rw [fderiv_div_apply (fun p : A => F (w,p)) (fun _ : A => w-E) a hsec.differentiableAt (differentiableAt_const _) hne v,hz w hw]
    simp
  change (fderiv ℂ ((2*Real.pi*I : ℂ)⁻¹ • fun p : A => ∮ w in C(c,r),G (w,p)) a) v=0
  rw [fderiv_const_smul_field]
  change (2*Real.pi*I : ℂ)⁻¹*((fderiv ℂ (fun p : A => ∮ w in C(c,r),G (w,p)) a) v)=0
  rw [hraw,mul_zero]

/-- The actual compact interval differentiation theorem transfers zero source
variation from the integrand to its literal interval integral. -/
theorem fderiv_intervalIntegral_source_apply_eq_zero
    (F : ℂ × A → ℂ) (D : Set (ℂ × A)) (hD : IsOpen D) (hF : AnalyticOnNhd ℂ F D)
    (l r : ℝ) (a v : A) (hc : ∀ t∈uIcc l r, ((t : ℂ),a)∈D)
    (hz : ∀ t∈uIcc l r, (fderiv ℂ (fun p : A => F ((t : ℂ),p)) a) v=0) :
    (fderiv ℂ (fun p : A => ∫ t in l..r,F ((t : ℂ),p)) a) v=0 := by
  have hd := (hasFDerivAt_intervalIntegral_of_jointAnalytic F hD hF l r a hc).fderiv
  have hdf : ContinuousOn (fderiv ℂ F) D :=
    (hF.contDiffOn_of_completeSpace (n := 1)).continuousOn_fderiv_of_isOpen hD (by norm_num)
  have hmap : Continuous (fun t : ℝ => ((t : ℂ),a)) := Complex.continuous_ofReal.prodMk continuous_const
  have hint : IntervalIntegrable (fun t : ℝ => (fderiv ℂ F ((t : ℂ),a)).comp
      (ContinuousLinearMap.inr ℂ ℂ A)) volume l r :=
    ((hdf.comp hmap.continuousOn hc).clm_comp continuousOn_const).intervalIntegrable
  rw [hd,ContinuousLinearMap.intervalIntegral_apply hint v]
  calc
    _ = ∫ _t in l..r,(0 : ℂ) := by
      apply intervalIntegral.integral_congr
      intro t ht
      change ((fderiv ℂ F ((t : ℂ),a)).comp (ContinuousLinearMap.inr ℂ ℂ A)) v=0
      rw [← fderiv_source_section_eq_joint F (t : ℂ) a (hF _ (hc t ht)).differentiableAt]
      exact hz t ht
    _ = 0 := by simp

/-- A normalized affine-segment primitive preserves stationary source data. -/
theorem fderiv_parametricConvexPrimitive_source_apply_eq_zero
    (F : ℂ × A → ℂ) (Ω : Set ℂ) (V : Set A) (c : ℂ)
    (hΩ : IsOpen Ω) (hconv : Convex ℝ Ω) (hV : IsOpen V) (hc : c∈Ω)
    (hF : AnalyticOnNhd ℂ F (Ω ×ˢ V)) (a v : A) (ha : a∈V)
    (hz : ∀ z∈Ω, (fderiv ℂ (fun p : A => F (z,p)) a) v=0)
    (z : ℂ) (hzΩ : z∈Ω) :
    (fderiv ℂ (fun p : A => parametricConvexPrimitive F c (z,p)) a) v=0 := by
  let T (t : ℂ × A) := (c+t.1*(z-c),t.2)
  let D := T ⁻¹' (Ω ×ˢ V)
  let G (t : ℂ × A) := (z-c)*F (T t)
  have hT : Continuous T := by dsimp only [T];fun_prop
  have hD : IsOpen D := (hΩ.prod hV).preimage hT
  have hG : AnalyticOnNhd ℂ G D := by
    intro t ht
    exact analyticAt_const.mul ((hF (T t) ht).comp
      (f := T) ((analyticAt_const.add (analyticAt_fst.mul analyticAt_const)).prod analyticAt_snd))
  have hsegment (t : ℝ) (ht : t∈uIcc (0 : ℝ) 1) : c+(t : ℂ)*(z-c)∈Ω := by
    have h := hconv.lineMap_mem hc hzΩ (show t∈Icc (0 : ℝ) 1 by simpa only [uIcc_of_le zero_le_one] using ht)
    simpa only [AffineMap.lineMap_apply_module',Complex.real_smul,add_comm] using h
  change (fderiv ℂ (fun p : A => ∫ t in (0 : ℝ)..1,G ((t : ℂ),p)) a) v=0
  apply fderiv_intervalIntegral_source_apply_eq_zero G D hD hG 0 1 a v
    (fun t ht => ⟨hsegment t ht,ha⟩)
  intro t ht
  change (fderiv ℂ ((z-c) • fun p : A => F (c+(t : ℂ)*(z-c),p)) a) v=0
  rw [fderiv_const_smul_field]
  change (z-c)*((fderiv ℂ (fun p : A => F (c+(t : ℂ)*(z-c),p)) a) v)=0
  rw [hz _ (hsegment t ht),mul_zero]

end NLS.ComplexAnalysis
