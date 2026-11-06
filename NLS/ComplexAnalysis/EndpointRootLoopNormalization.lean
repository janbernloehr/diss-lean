import NLS.ComplexAnalysis.TwoEndpointRoot
import NLS.ComplexAnalysis.PiecewiseContourPeriod
import NLS.ZakharovShabat.SourceStandardRootEllipsePeriod
import NLS.ZakharovShabat.SourceStandardRootLogPrimitive

/-! # Actual winding normalization of standard endpoint-root ellipses -/
noncomputable section
set_option autoImplicit false
open Set Metric Complex NLS.ZakharovShabat
namespace NLS.ComplexAnalysis

theorem standardRootGapSegment_eq_segment (t d : ℂ) :
    standardRootGapSegment t d = segment ℝ (t-d) (t+d) := by
  ext z
  constructor
  · rintro ⟨a,ha,rfl⟩
    have hp : (a+1)/2 ∈ Icc (0 : ℝ) 1 := by constructor <;> linarith [ha.1,ha.2]
    convert lineMap_mem_segment ℝ (t-d) (t+d) hp using 1
    simp only [AffineMap.lineMap_apply_module,Complex.real_smul]
    push_cast
    ring
  · intro hz
    obtain ⟨a,ha,he⟩ := (segment_eq_image_lineMap ℝ (t-d) (t+d) ▸ hz)
    refine ⟨2*a-1,⟨by linarith [ha.1],by linarith [ha.2]⟩,?_⟩
    rw [← he,AffineMap.lineMap_apply_module]
    simp only [Complex.real_smul]
    push_cast
    ring

theorem standardRoot_ne_zero_off_gap (t d z : ℂ) (hz : z ∉ standardRootGapSegment t d) :
    normalizedStandardRoot t ((2*d)^2) z ≠ 0 := by
  have hz' : z ∉ segment ℝ (t-d) (t+d) := by rwa [← standardRootGapSegment_eq_segment]
  have hs := normalizedStandardRoot_sq_off_segment (t-d) (t+d) z hz'
  have hm : ((t-d)+(t+d))/2 = t := by ring
  have hd : ((t+d)-(t-d))^2 = (2*d)^2 := by ring
  rw [hm,hd] at hs
  intro he
  rw [he,zero_pow (by norm_num : 2 ≠ 0)] at hs
  rcases mul_eq_zero.mp hs.symm with h | h
  · exact hz' (sub_eq_zero.mp h ▸ left_mem_segment ℝ (t-d) (t+d))
  · exact hz' (sub_eq_zero.mp h ▸ right_mem_segment ℝ (t-d) (t+d))

theorem standardRoot_inv_loop_integral_eq_neg_pole
    (t d : ℂ) (Γ : PiecewiseC1Loop) (hΓ : Γ.Inside (standardRootGapSegment t d)ᶜ) :
    Γ.integral (fun z => (normalizedStandardRoot t ((2*d)^2) z)⁻¹) =
      -Γ.integral (fun z => (z-t)⁻¹) := by
  let U := (standardRootGapSegment t d)ᶜ
  let f : ℂ → ℂ := fun z => (normalizedStandardRoot t ((2*d)^2) z)⁻¹
  let g : ℂ → ℂ := fun z => (z-t)⁻¹
  have ht : t ∈ standardRootGapSegment t d := ⟨0,by constructor <;> norm_num,by simp⟩
  have hmid (z : ℂ) (hz : z ∈ U) : t ≠ z := fun he => hz (he ▸ ht)
  have hslit (z : ℂ) (hz : z ∈ U) : 1-(2*d)^2/(4*(t-z)^2) ∈ slitPlane := by
    change z ∉ standardRootGapSegment t d at hz
    have hh := gap_radicand_mem_slitPlane (t-d) (t+d) z (by
      simpa only [← standardRootGapSegment_eq_segment] using hz)
    convert hh using 1; ring
  have hroot : AnalyticOnNhd ℂ (normalizedStandardRoot t ((2*d)^2)) U :=
    fun z hz => normalizedStandardRoot_analyticAt_of_slit _ _ _ (hmid z hz) (hslit z hz)
  have hf : ContinuousOn f U := fun z hz =>
    ((hroot z hz).continuousAt.inv₀ (standardRoot_ne_zero_off_gap t d z hz)).continuousWithinAt
  have hg : ContinuousOn g U := fun z hz =>
    ((continuousAt_id.sub continuousAt_const).inv₀ (sub_ne_zero.mpr (hmid z hz).symm)).continuousWithinAt
  have hp := Γ.integral_eq_zero_of_primitive (fun z => f z+g z)
    (standardRootLogCorrection t ((2*d)^2)) U (hf.add hg)
    (fun z hz => hasDerivAt_standardRootLogCorrection _ _ _ (hmid z hz) (hslit z hz)) hΓ
  rw [Γ.integral_add f g hf hg hΓ] at hp
  exact eq_neg_of_add_eq_zero_left hp

theorem standardRootEllipseLoop_winding_one (t d : ℂ) (hd : d ≠ 0)
    (r : ℝ) (hr : 1 < r) :
    (standardRootEllipseLoop t d r (by linarith)).windingIntegral t = 1 := by
  let Γ := standardRootEllipseLoop t d r (by linarith)
  have hΓ : Γ.Inside (standardRootGapSegment t d)ᶜ :=
    standardRootEllipseLoop_inside _ _ _ _ (fun x _ =>
      standardRootEllipseMap_not_mem_gap t d r x hd hr)
  have he : Γ.integral (fun z => (normalizedStandardRoot t ((2*d)^2) z)⁻¹) =
      -(2*(Real.pi : ℂ))*I := by
    simpa [Γ,intervalIntegral.integral_const] using
      standardRootEllipseLoop_weighted_integral t d r hr hd (fun _ => 1)
  have hp := standardRoot_inv_loop_integral_eq_neg_pole t d Γ hΓ
  rw [he] at hp
  change (2*Real.pi*I : ℂ)⁻¹*Γ.integral (fun z => (z-t)⁻¹) = 1
  have hv : Γ.integral (fun z => (z-t)⁻¹) = (2*Real.pi*I : ℂ) := by linear_combination hp
  rw [hv,inv_mul_cancel₀ (by simp [Real.pi_ne_zero])]

end NLS.ComplexAnalysis
