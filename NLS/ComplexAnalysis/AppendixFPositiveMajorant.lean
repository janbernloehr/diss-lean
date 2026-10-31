import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.SpecialFunctions.Integrability.Basic
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-! # A positive majorant for the moving square-root quotient in F.2

The absolute value in the lower distance makes the weight valid on
both sides of the moving singular point. Values at that single point
are handled separately in integral applications.
-/
noncomputable section
open Complex
namespace NLS.ComplexAnalysis

/-- Every square-root branch has the same lower norm bound. -/
theorem appendixF_square_root_norm_lower (t : ℝ) (ht : 0 ≤ t) (ε w : ℂ)
    (hw : w^2 = (t:ℂ)^2-ε^2) :
    Real.sqrt (t+‖ε‖)*Real.sqrt |t-‖ε‖| ≤ ‖w‖ := by
  have hn := abs_norm_sub_norm_le ((t:ℂ)^2) (ε^2)
  have htN : ‖(t:ℂ)‖ = t := by rw [Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg ht]
  rw [norm_pow,norm_pow,htN,← hw, norm_pow] at hn
  have he : |t^2-‖ε‖^2| = (t+‖ε‖)*|t-‖ε‖| := by
    rw [show t^2-‖ε‖^2 = (t+‖ε‖)*(t-‖ε‖) by ring,abs_mul,abs_of_nonneg (by positivity : 0 ≤ t+‖ε‖)]
  rw [he] at hn
  have hs := Real.sqrt_le_sqrt hn
  rwa [Real.sqrt_mul (by positivity : 0 ≤ t+‖ε‖),Real.sqrt_sq (norm_nonneg w)] at hs

/-- The corrected scalar majorant bounds the actual quotient away from its one moving singular point. -/
theorem appendixF_quotient_le_positive_majorant (t : ℝ) (ht : 0 ≤ t) (ε a w : ℂ)
    (ha : ‖a‖ ≤ ‖ε‖) (hw : w^2 = (t:ℂ)^2-ε^2) (hne : t ≠ ‖ε‖) :
    ‖((t:ℂ)+a)/w‖ ≤ Real.sqrt (t+‖ε‖)/Real.sqrt |t-‖ε‖| := by
  have hD : 0 < Real.sqrt |t-‖ε‖| := Real.sqrt_pos.mpr (abs_pos.mpr (sub_ne_zero.mpr hne))
  have hA : 0 < t+‖ε‖ := by
    have hn := norm_nonneg ε
    by_contra h
    have hz : t = 0 := by linarith
    have he : ‖ε‖ = 0 := by linarith
    exact hne (hz.trans he.symm)
  have hsA := Real.sqrt_pos.mpr hA
  have hlower := appendixF_square_root_norm_lower t ht ε w hw
  have hwpos : 0 < ‖w‖ := (mul_pos hsA hD).trans_le hlower
  have hnum : ‖(t:ℂ)+a‖ ≤ t+‖ε‖ := by
    have h := norm_add_le (t:ℂ) a
    rw [Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg ht] at h
    linarith
  rw [norm_div]
  refine (div_le_div_of_nonneg_right hnum hwpos.le).trans ?_
  apply (div_le_div_iff₀ hwpos hD).mpr
  have h := mul_le_mul_of_nonneg_left hlower hsA.le
  nlinarith [Real.sq_sqrt hA.le]

/-- The majorant is controlled by an integrable inverse square-root weight plus one. -/
theorem appendixF_positive_majorant_le (e t : ℝ) (he : 0 ≤ e) (ht : 0 ≤ t) :
    Real.sqrt (t+e)/Real.sqrt |t-e| ≤ 1+Real.sqrt (2*e)/Real.sqrt |t-e| := by
  by_cases hzero : t = e
  · simp [hzero]
  have hD : 0 < Real.sqrt |t-e| := Real.sqrt_pos.mpr (abs_pos.mpr (sub_ne_zero.mpr hzero))
  have hA : t+e ≤ |t-e|+2*e := by linarith [le_abs_self (t-e)]
  have hs : Real.sqrt (t+e) ≤ Real.sqrt |t-e|+Real.sqrt (2*e) := by
    have h1 := Real.sq_sqrt (show 0 ≤ t+e by positivity)
    have h2 := Real.sq_sqrt (abs_nonneg (t-e))
    have h3 := Real.sq_sqrt (show 0 ≤ 2*e by positivity)
    have hn1 := Real.sqrt_nonneg (t+e)
    have hn2 := Real.sqrt_nonneg |t-e|
    have hn3 := Real.sqrt_nonneg (2*e)
    nlinarith [mul_nonneg hn2 hn3]
  apply (div_le_iff₀ hD).mpr
  have hd : (1+Real.sqrt (2*e)/Real.sqrt |t-e|)*Real.sqrt |t-e| =
      Real.sqrt |t-e|+Real.sqrt (2*e) := by field_simp
  rw [hd]
  exact hs

open Set MeasureTheory

/-- The positive endpoint inverse-square-root weight has integral exactly twice the square root. -/
theorem appendixF_inverse_sqrt_interval (b : ℝ) (hb : 0 ≤ b) :
    IntervalIntegrable (fun t : ℝ => (Real.sqrt t)⁻¹) volume 0 b ∧
      (∫ t in (0:ℝ)..b, (Real.sqrt t)⁻¹) = 2*Real.sqrt b := by
  have he (t : ℝ) (ht : 0 ≤ t) : t^(-1/2:ℝ) = (Real.sqrt t)⁻¹ := by
    rw [show (-1/2:ℝ) = -(1/2) by norm_num,Real.rpow_neg ht,← Real.sqrt_eq_rpow]
  have hint := intervalIntegral.intervalIntegrable_rpow' (a := 0) (b := b)
    (by norm_num : (-1:ℝ) < -1/2)
  constructor
  · apply hint.congr
    intro t ht
    rw [uIoc_of_le hb] at ht
    exact he t ht.1.le
  · rw [← intervalIntegral.integral_congr (fun t ht => he t
      (by rw [uIcc_of_le hb] at ht; exact ht.1))]
    rw [integral_rpow (Or.inl (by norm_num : (-1:ℝ) < -1/2))]
    norm_num [← Real.sqrt_eq_rpow]
    ring

/-- The moving inverse-square-root singularity is integrable, with an exact norm bound. -/
theorem appendixF_inverse_sqrt_distance_interval (e : ℝ) (he : 0 ≤ e) (he1 : e ≤ 1) :
    IntervalIntegrable (fun t : ℝ => (Real.sqrt |t-e|)⁻¹) volume 0 1 ∧
      (∫ t in (0:ℝ)..1, (Real.sqrt |t-e|)⁻¹) =
        2*(Real.sqrt e+Real.sqrt (1-e)) := by
  have he0 := appendixF_inverse_sqrt_interval e he
  have he1' := appendixF_inverse_sqrt_interval (1-e) (by linarith)
  have hleft : IntervalIntegrable (fun t : ℝ => (Real.sqrt (e-t))⁻¹) volume 0 e := by
    simpa using (he0.1.comp_sub_left e).symm
  have hright : IntervalIntegrable (fun t : ℝ => (Real.sqrt (t-e))⁻¹) volume e 1 := by
    simpa using he1'.1.comp_sub_right e
  have eqleft (t : ℝ) (ht : t ≤ e) : |t-e| = e-t := by rw [abs_of_nonpos (by linarith)]; ring
  have eqright (t : ℝ) (ht : e ≤ t) : |t-e| = t-e := abs_of_nonneg (by linarith)
  have hl : IntervalIntegrable (fun t : ℝ => (Real.sqrt |t-e|)⁻¹) volume 0 e :=
    hleft.congr (fun t ht => by rw [uIoc_of_le he] at ht; rw [eqleft t ht.2])
  have hr : IntervalIntegrable (fun t : ℝ => (Real.sqrt |t-e|)⁻¹) volume e 1 :=
    hright.congr (fun t ht => by rw [uIoc_of_le he1] at ht; rw [eqright t ht.1.le])
  refine ⟨hl.trans hr,?_⟩
  rw [← intervalIntegral.integral_add_adjacent_intervals hl hr]
  have il : (∫ t in (0:ℝ)..e, (Real.sqrt |t-e|)⁻¹) = 2*Real.sqrt e := by
    calc
      _ = ∫ t in (0:ℝ)..e, (Real.sqrt (e-t))⁻¹ := by
        apply intervalIntegral.integral_congr
        intro t ht
        rw [uIcc_of_le he] at ht
        simp only [eqleft t ht.2]
      _ = 2*Real.sqrt e := by
        rw [intervalIntegral.integral_comp_sub_left (fun t : ℝ => (Real.sqrt t)⁻¹) e]
        simpa using he0.2
  have ir : (∫ t in e..1, (Real.sqrt |t-e|)⁻¹) = 2*Real.sqrt (1-e) := by
    calc
      _ = ∫ t in e..1, (Real.sqrt (t-e))⁻¹ := by
        apply intervalIntegral.integral_congr
        intro t ht
        rw [uIcc_of_le he1] at ht
        simp only [eqright t ht.1]
      _ = 2*Real.sqrt (1-e) := by
        rw [intervalIntegral.integral_comp_sub_right (fun t : ℝ => (Real.sqrt t)⁻¹) e]
        simpa using he1'.2
  rw [il,ir]
  ring

/-- The corrected moving majorant is integrable on the whole unit interval. -/
theorem appendixF_positive_majorant_integrable (e : ℝ) (he : 0 ≤ e) (he1 : e ≤ 1) :
    IntervalIntegrable (fun t : ℝ => Real.sqrt (t+e)/Real.sqrt |t-e|) volume 0 1 := by
  have hw := (appendixF_inverse_sqrt_distance_interval e he he1).1
  have hc : Continuous (fun t : ℝ => Real.sqrt (t+e)) :=
    Real.continuous_sqrt.comp (continuous_id.add continuous_const)
  simpa only [div_eq_mul_inv,mul_comm] using hw.mul_continuousOn hc.continuousOn

/-- The majorant's L1 error has the explicit bound four times sqrt(2e). -/
theorem appendixF_positive_majorant_L1_bound (e : ℝ) (he : 0 ≤ e) (he1 : e ≤ 1) :
    (∫ t in (0:ℝ)..1, |Real.sqrt (t+e)/Real.sqrt |t-e|-1|) ≤ 4*Real.sqrt (2*e) := by
  have hg := appendixF_positive_majorant_integrable e he he1
  have hw := appendixF_inverse_sqrt_distance_interval e he he1
  have hint := (hg.sub (intervalIntegrable_const (c := (1:ℝ)))).abs
  have hbound := hw.1.const_mul (Real.sqrt (2*e))
  have hi := intervalIntegral.integral_mono_ae_restrict zero_le_one hint hbound (by
    filter_upwards [ae_restrict_mem measurableSet_Icc, (volume.restrict (Icc (0:ℝ) 1)).ae_ne e] with t ht hte
    have hD : 0 < Real.sqrt |t-e| := Real.sqrt_pos.mpr (abs_pos.mpr (sub_ne_zero.mpr hte))
    have hA : |t-e| ≤ t+e := abs_le.mpr ⟨by linarith [ht.1],by linarith⟩
    have hge : 1 ≤ Real.sqrt (t+e)/Real.sqrt |t-e| := by
      apply (le_div_iff₀ hD).mpr
      simpa only [one_mul] using Real.sqrt_le_sqrt hA
    rw [abs_of_nonneg (sub_nonneg.mpr hge)]
    have hu := appendixF_positive_majorant_le e t he ht.1
    simp only [div_eq_mul_inv] at hu ⊢
    linarith)
  rw [intervalIntegral.integral_const_mul,hw.2] at hi
  have heS := Real.sqrt_le_one.mpr he1
  have heS' := Real.sqrt_le_one.mpr (show 1-e ≤ 1 by linarith)
  have hpos := Real.sqrt_nonneg (2*e)
  nlinarith

/-- The positive moving majorants converge to one in L1 as their singularities approach zero. -/
theorem appendixF_positive_majorant_tendsto_L1 {ι : Type*} {l : Filter ι}
    (e : ι → ℝ) (he : Filter.Tendsto e l (nhds 0))
    (hrange : ∀ᶠ i in l, 0 ≤ e i ∧ e i ≤ 1) :
    Filter.Tendsto (fun i => ∫ t in (0:ℝ)..1,
      |Real.sqrt (t+e i)/Real.sqrt |t-e i|-1|) l (nhds 0) := by
  apply squeeze_zero' (Filter.Eventually.of_forall (fun i =>
    intervalIntegral.integral_nonneg_of_forall zero_le_one (fun _ => abs_nonneg _))) ?_
    (by simpa only [mul_zero,Real.sqrt_zero] using ((he.const_mul 2).sqrt.const_mul 4))
  filter_upwards [hrange] with i hi
  exact appendixF_positive_majorant_L1_bound (e i) hi.1 hi.2

end NLS.ComplexAnalysis
