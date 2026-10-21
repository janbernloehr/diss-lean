import NLS.SequenceSpaces.LogarithmicSpectralWeights
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

noncomputable section
set_option autoImplicit false
open Set Filter Topology
namespace NLS.SpectralWeight

/-- A positive logarithmic denominator makes the profile sublinear. -/
theorem logarithmicProfile_div_self_tendsto_zero (σ : ℝ) (hσ : 0 < σ) :
    Tendsto (fun x : ℝ => logarithmicProfile σ x/x) atTop (𝓝 0) := by
  have hshift : Tendsto (fun x : ℝ => 1+x) atTop atTop := tendsto_atTop_add_const_left atTop 1 tendsto_id
  have hpow := (tendsto_rpow_atTop hσ).comp (Real.tendsto_log_atTop.comp hshift)
  have h := (tendsto_atTop_add_const_left atTop 1 hpow).inv_tendsto_atTop
  apply h.congr'
  filter_upwards [eventually_gt_atTop (0:ℝ)] with x hx
  dsimp only [Pi.inv_apply, Function.comp_apply]
  unfold logarithmicProfile
  field_simp

private theorem log_denominator_div_rpow_tendsto_zero (σ t : ℝ) (ht : 0 < t) :
    Tendsto (fun x : ℝ => (1+(Real.log (1+x))^σ)/x^t) atTop (𝓝 0) := by
  have hshift : Tendsto (fun x : ℝ => 1+x) atTop atTop := tendsto_atTop_add_const_left atTop 1 tendsto_id
  have hl := (isLittleO_log_rpow_rpow_atTop σ ht).tendsto_div_nhds_zero.comp hshift
  have h1 := ((tendsto_rpow_atTop ht).comp hshift).inv_tendsto_atTop
  have hbase : Tendsto (fun x : ℝ => (1+(Real.log (1+x))^σ)/(1+x)^t) atTop (𝓝 0) := by
    simpa only [add_div,one_div,zero_add,Pi.inv_apply,Function.comp_apply] using h1.add hl
  have hratio : Tendsto (fun x : ℝ => (1+x)/x) atTop (𝓝 (1:ℝ)) := by
    have h : Tendsto (fun x : ℝ => 1+x⁻¹) atTop (𝓝 (1:ℝ)) := by
      simpa only [add_zero] using (tendsto_const_nhds (x := (1:ℝ))).add tendsto_inv_atTop_zero
    apply h.congr'
    filter_upwards [eventually_gt_atTop (0:ℝ)] with x hx
    field_simp
    ring
  have hprod := hbase.mul (hratio.rpow_const (p := t) (Or.inl one_ne_zero))
  simp only [Real.one_rpow,zero_mul] at hprod
  apply hprod.congr'
  filter_upwards [eventually_gt_atTop (0:ℝ)] with x hx
  rw [Real.div_rpow (by linarith) hx.le]
  field_simp

/-- The logarithmic profile grows faster than every fixed sublinear power. -/
theorem logarithmicProfile_div_rpow_tendsto_atTop (σ ρ : ℝ) (hρ : ρ < 1) :
    Tendsto (fun x : ℝ => logarithmicProfile σ x/x^ρ) atTop atTop := by
  have hs := log_denominator_div_rpow_tendsto_zero σ (1-ρ) (sub_pos.mpr hρ)
  have hpos : ∀ᶠ x : ℝ in atTop, 0 < (1+(Real.log (1+x))^σ)/x^(1-ρ) := by
    filter_upwards [eventually_gt_atTop (0:ℝ)] with x hx
    exact div_pos (add_pos_of_pos_of_nonneg zero_lt_one
      (Real.rpow_nonneg (Real.log_nonneg (by linarith)) σ)) (Real.rpow_pos_of_pos hx _)
  have hwithin : Tendsto (fun x : ℝ => (1+(Real.log (1+x))^σ)/x^(1-ρ)) atTop (𝓝[>] 0) :=
    tendsto_nhdsWithin_iff.mpr ⟨hs,hpos⟩
  apply hwithin.inv_tendsto_nhdsGT_zero.congr'
  filter_upwards [eventually_gt_atTop (0:ℝ)] with x hx
  have hid : x^(1-ρ)*x^ρ=x := by
    rw [← Real.rpow_add hx,sub_add_cancel,Real.rpow_one]
  unfold logarithmicProfile
  simp only [Pi.inv_apply,inv_div]
  have hxρ : x^ρ ≠ 0 := (Real.rpow_pos_of_pos hx ρ).ne'
  have hden : 1+(Real.log (1+x))^σ ≠ 0 := ne_of_gt
    (add_pos_of_pos_of_nonneg zero_lt_one (Real.rpow_nonneg (Real.log_nonneg (by linarith)) σ))
  field_simp
  exact hid

/-- Every positive Abel exponential eventually dominates a logarithmic exponential. -/
theorem eventually_logarithmic_exp_lt_abel (a b σ : ℝ) (hb : 0 < b) (hσ : 0 < σ) :
    ∀ᶠ x : ℝ in atTop, Real.exp (a*logarithmicProfile σ x) < Real.exp (b*x) := by
  have h := (logarithmicProfile_div_self_tendsto_zero σ hσ).const_mul a
  simp only [mul_zero] at h
  filter_upwards [h.eventually (gt_mem_nhds hb),eventually_gt_atTop (0:ℝ)] with x hx hpos
  apply Real.exp_lt_exp.mpr
  apply (div_lt_iff₀ hpos).mp
  simpa only [mul_div_assoc] using hx

/-- Every fixed Gevrey power is eventually dominated by a positive logarithmic exponential. -/
theorem eventually_gevrey_exp_lt_logarithmic (a b σ ρ : ℝ) (ha : 0 < a) (hρ : ρ < 1) :
    ∀ᶠ x : ℝ in atTop, Real.exp (b*x^ρ) < Real.exp (a*logarithmicProfile σ x) := by
  have h := logarithmicProfile_div_rpow_tendsto_atTop σ ρ hρ
  filter_upwards [h.eventually (eventually_gt_atTop (b/a)),eventually_gt_atTop (0:ℝ)] with x hx hpos
  apply Real.exp_lt_exp.mpr
  have hp : 0 < x^ρ := Real.rpow_pos_of_pos hpos _
  have hh := (div_lt_div_iff₀ ha hp).mp hx
  simpa only [mul_comm a] using hh

end NLS.SpectralWeight
