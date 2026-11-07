import NLS.ZakharovShabat.SourceNormalizedActionCircleCorrectionBound
import NLS.ZakharovShabat.SourceHigherActionOneKernel

/-! Recentring the actual first higher-action contour at the periodic
midpoint removes the growing free spectral weight. The resulting
estimate uses only the fixed-circle radius and the deleted factor. -/
noncomputable section
open Set Metric Complex
namespace NLS.ZakharovShabat

theorem norm_normalizedActionCircleKernel_le_of_separation
    (τ q B z : ℂ) (a M : ℝ) (ha : 0 < a)
    (hsep : a ≤ ‖τ-z‖) (hq : ‖q‖ ≤ a^2) (hB : ‖B‖ ≤ M) :
    ‖normalizedActionCircleKernel τ q B z‖ ≤
      1/(8*a)+2*M+a^2*(2/a^3+M/a^2+2*M^2/a) := by
  have hM : 0 ≤ M := (norm_nonneg B).trans hB
  have hd : τ ≠ z := sub_ne_zero.mp (norm_pos_iff.mp (ha.trans_le hsep))
  have hsmall : ‖q‖ ≤ ‖τ-z‖^2 := hq.trans (pow_le_pow_left₀ ha.le hsep 2)
  have hw := (normalizedStandardRoot_denominator_lower_bounds τ q z hd hsmall).1
  have hw0 : normalizedStandardRoot τ q z ≠ 0 :=
    norm_pos_iff.mp (by linarith [ha.trans_le hsep])
  have hp0 : τ-z+normalizedStandardRoot τ q z ≠ 0 :=
    normalizedStandardRoot_add_ne_zero τ q z hd
  rw [normalizedActionCircleKernel_eq_zeroGap_add_correction τ q B z hd hw0 hp0]
  have hfirst : ‖-(1/8:ℂ)*(z-τ)⁻¹‖ ≤ 1/(8*a) := by
    simp only [norm_mul,norm_neg,norm_inv,norm_div,norm_one,Complex.norm_ofNat,norm_sub_rev]
    calc
      (1/8:ℝ)*‖τ-z‖⁻¹ ≤ (1/8:ℝ)*a⁻¹ :=
        mul_le_mul_of_nonneg_left ((inv_le_inv₀ (ha.trans_le hsep) ha).mpr hsep) (by norm_num)
      _ = _ := by field_simp
  have htwo : ‖(2:ℂ)*B‖ ≤ 2*M := by
    simpa only [norm_mul,Complex.norm_ofNat] using
      (mul_le_mul_of_nonneg_left hB (by norm_num : (0:ℝ) ≤ 2))
  have hc := norm_normalizedActionCircleKernelCorrection_le_of_separation τ q B z a M ha hsep hq hB
  have hprod : ‖q*normalizedActionCircleKernelCorrection τ q B z‖ ≤
      a^2*(2/a^3+M/a^2+2*M^2/a) := by
    rw [norm_mul]
    exact mul_le_mul hq hc (norm_nonneg _) (sq_nonneg _)
  exact (norm_add_le _ _).trans ((add_le_add ((norm_add_le _ _).trans
    (add_le_add hfirst htwo)) hprod))

theorem norm_centeredActionCircle_le (c τ b : ℂ) (R C L : ℝ) (f : ℂ → ℂ)
    (hR : 0 ≤ R) (hf : ContinuousOn f (sphere c R))
    (hb : ∀ z ∈ sphere c R, ‖z+b-2*τ‖ ≤ L)
    (hbound : ∀ z ∈ sphere c R, ‖f z‖ ≤ C) :
    ‖-(2*(Real.pi:ℂ))⁻¹*(∮ z in C(c,R), (z+b)*f z) -
      τ*(-(Real.pi:ℂ)⁻¹*(∮ z in C(c,R), f z))‖ ≤ R*(L*C) := by
  have hi : CircleIntegrable (fun z => (z+b)*f z) c R :=
    ((continuousOn_id.add continuousOn_const).mul hf).circleIntegrable hR
  have hj : CircleIntegrable (fun z => (2*τ)*f z) c R :=
    (continuousOn_const.mul hf).circleIntegrable hR
  have he : (∮ z in C(c,R), (z+b-2*τ)*f z) =
      (∮ z in C(c,R), (z+b)*f z)-(2*τ)*(∮ z in C(c,R), f z) := by
    have hfun : (fun z => (z+b-2*τ)*f z) = fun z => (z+b)*f z-(2*τ)*f z := by
      funext z; ring
    rw [hfun,circleIntegral.integral_sub hi hj,circleIntegral.integral_const_mul]
  have hc : -(2*(Real.pi:ℂ))⁻¹*(∮ z in C(c,R), (z+b)*f z) -
      τ*(-(Real.pi:ℂ)⁻¹*(∮ z in C(c,R), f z)) =
      -(2*(Real.pi:ℂ))⁻¹*(∮ z in C(c,R), (z+b-2*τ)*f z) := by
    rw [he]
    field_simp
    ring
  have hpoint : ∀ z ∈ sphere c R, ‖(z+b-2*τ)*f z‖ ≤ L*C := by
    intro z hz
    rw [norm_mul]
    exact mul_le_mul (hb z hz) (hbound z hz) (norm_nonneg _) (by
      have h := hb (circleMap c R 0) (circleMap_mem_sphere c hR 0)
      exact (norm_nonneg _).trans h)
  rw [hc,norm_mul,norm_neg]
  have hn : ‖(2*(Real.pi:ℂ))⁻¹‖ = (2*Real.pi)⁻¹ := by simp [Real.pi_pos.le]
  rw [hn]
  calc
    _ ≤ (2*Real.pi)⁻¹*(2*Real.pi*R*(L*C)) :=
      mul_le_mul_of_nonneg_left (circleIntegral.norm_integral_le_of_norm_le_const hR hpoint) (by positivity)
    _ = _ := by field_simp

end NLS.ZakharovShabat
