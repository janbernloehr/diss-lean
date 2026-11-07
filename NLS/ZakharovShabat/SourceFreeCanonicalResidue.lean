import NLS.ZakharovShabat.SourcePsiFree
import NLS.ZakharovShabat.SourceCriticalRootPeriodCircle

/-! Exact free canonical-root residues on ANY genuine period circle.
The analytic numerator may depend on arbitrary independent parameters;
no product normalization away from the free source is used. -/
noncomputable section
open Set Metric Complex
open scoped ENNReal Classical
namespace NLS.ZakharovShabat

theorem SourceCriticalRootPeriodCircle.freeSineQuotient_ne_zero
    (m : ℤ) (D : SourceCriticalRootPeriodCircle (by norm_num) (by norm_num) (0:CoeffPair 2) m)
    (z : ℂ) (hz : z ∈ closedBall (D.center:ℂ) D.radius) : freeSineQuotient m z ≠ 0 := by
  by_cases hzm : z = (Real.pi:ℂ)*m
  · rw [hzm,freeSineQuotient_center]
    intro h
    have hn := norm_cos_freeCenter m
    rw [h,norm_zero] at hn
    norm_num at hn
  · rw [freeSineQuotient_eq_div m z hzm]
    apply div_ne_zero _ (sub_ne_zero.mpr hzm)
    intro hs
    obtain ⟨j,hj⟩ := Complex.sin_eq_zero_iff.mp hs
    have hje : z = (Real.pi:ℂ)*j := by simpa only [mul_comm] using hj
    have hjm : j ≠ m := fun h => hzm (h ▸ hje)
    have havoid := D.closedBall_subset_omittedDomain hz j hjm
    rw [sourcePeriodicSegment_zero_source] at havoid
    exact havoid (mem_singleton_iff.mpr hje)

theorem SourceCriticalRootPeriodCircle.freeCanonicalRoot_residue
    (m : ℤ) (D : SourceCriticalRootPeriodCircle (by norm_num) (by norm_num) (0:CoeffPair 2) m)
    (f : ℂ → ℂ) (hf : AnalyticOnNhd ℂ f (closedBall (D.center:ℂ) D.radius)) :
    (2*Real.pi:ℂ)⁻¹*(∮ z in C((D.center:ℂ),D.radius),
      f z/sourceCanonicalRoot (by norm_num) (by norm_num) (0:CoeffPair 2) z) =
      -f ((Real.pi:ℂ)*m)/(2*cos ((Real.pi:ℂ)*m)) := by
  let c : ℂ := (Real.pi:ℂ)*m
  let g : ℂ → ℂ := fun z => (I/2)*f z/freeSineQuotient m z
  have hg : AnalyticOnNhd ℂ g (closedBall (D.center:ℂ) D.radius) := by
    intro z hz
    exact (analyticAt_const.mul (hf z hz)).div
      (analyticOnNhd_freeSineQuotient m z (mem_univ _)) (D.freeSineQuotient_ne_zero m z hz)
  have hc : c ∈ ball (D.center:ℂ) D.radius := by
    apply D.gap
    rw [sourcePeriodicSegment_zero_source]
    exact mem_singleton _
  have he (z : ℂ) (hz : z ∈ sphere (D.center:ℂ) D.radius) :
      f z/sourceCanonicalRoot (by norm_num) (by norm_num) (0:CoeffPair 2) z =
        (z-c)⁻¹*g z := by
    have hzne : z ≠ c := by
      have h := D.sphere_subset_rootDomain hz m
      simpa only [sourcePeriodicSegment_zero_source,mem_singleton_iff] using h
    have hq := D.freeSineQuotient_ne_zero m z (sphere_subset_closedBall hz)
    rw [sourceCanonicalRoot_zero_source_eq_free_sine (by norm_num) (by norm_num) m,
      ← freeSineQuotient_mul_sub m z]
    dsimp only [g,c]
    field_simp [sub_ne_zero.mpr hzne,hq]
    simp [I_sq,neg_div]
  rw [circleIntegral.integral_congr D.radius_pos.le he]
  have hC := hg.differentiableOn.circleIntegral_sub_inv_smul hc
  simp only [smul_eq_mul] at hC
  rw [hC]
  dsimp only [g,c]
  rw [freeSineQuotient_center]
  have hpi : (Real.pi:ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  have hcos : cos ((Real.pi:ℂ)*m) ≠ 0 := by
    intro h
    have hh := norm_cos_freeCenter m
    rw [h,norm_zero] at hh
    norm_num at hh
  field_simp [hpi,hcos]
  simp [I_sq]

end NLS.ZakharovShabat
