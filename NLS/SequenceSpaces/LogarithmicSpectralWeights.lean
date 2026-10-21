import NLS.SequenceSpaces.ExponentialSpectralWeights
import Mathlib.Analysis.Convex.SpecificFunctions.Basic

noncomputable section
set_option autoImplicit false
open Set
namespace NLS.SpectralWeight

/-- The radial exponent in the logarithmically weakened Abel weight on p.105. -/
def logarithmicProfile (σ x : ℝ) : ℝ := x/(1+(Real.log (1+x))^σ)

theorem logarithmicProfile_nonneg (σ x : ℝ) (hx : 0 ≤ x) :
    0 ≤ logarithmicProfile σ x := by
  unfold logarithmicProfile
  exact div_nonneg hx (add_nonneg zero_le_one
    (Real.rpow_nonneg (Real.log_nonneg (by linarith)) σ))

/-- Logarithmic concavity controls the quotient in the intermediate weight. -/
theorem logarithmicProfile_monotone (σ : ℝ) (hσ : 0 ≤ σ) (hσ1 : σ ≤ 1) :
    MonotoneOn (logarithmicProfile σ) (Ici 0) := by
  intro x hx y hy hxy
  change 0 ≤ x at hx
  change 0 ≤ y at hy
  by_cases hy0 : y=0
  · have hx0 : x=0 := by linarith
    simp only [hx0,hy0,le_refl]
  have hypos : 0 < y := lt_of_le_of_ne hy (Ne.symm hy0)
  have hα : 0 ≤ x/y := div_nonneg hx hy
  have hα1 : x/y ≤ 1 := (div_le_one hypos).mpr hxy
  have hlx : 0 ≤ Real.log (1+x) := Real.log_nonneg (by linarith)
  have hly : 0 ≤ Real.log (1+y) := Real.log_nonneg (by linarith)
  have hlog := strictConcaveOn_log_Ioi.concaveOn.2
    (show 1+y ∈ Ioi 0 by change 0<1+y; linarith)
    (show (1:ℝ) ∈ Ioi 0 by norm_num) hα (sub_nonneg.mpr hα1)
    (by ring : x/y+(1-x/y)=1)
  simp only [smul_eq_mul,Real.log_one,mul_zero,add_zero] at hlog
  have he : x/y*(1+y)+(1-x/y)*1 = 1+x := by field_simp; ring
  rw [he] at hlog
  have hp := Real.rpow_le_rpow (mul_nonneg hα hly) hlog hσ
  rw [Real.mul_rpow hα hly] at hp
  have hscale : (x/y)*(Real.log (1+y))^σ ≤ (Real.log (1+x))^σ :=
    (mul_le_mul_of_nonneg_right (Real.self_le_rpow_of_le_one hα hα1 hσ1)
      (Real.rpow_nonneg hly σ)).trans hp
  have hs : x*(Real.log (1+y))^σ ≤ (Real.log (1+x))^σ*y :=
    (div_le_iff₀ hypos).mp (by simpa only [div_mul_eq_mul_div] using hscale)
  unfold logarithmicProfile
  apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
  nlinarith

/-- The logarithmic denominator makes the radial exponent subadditive. -/
theorem logarithmicProfile_add_le (σ : ℝ) (hσ : 0 ≤ σ)
    (x : ℝ) (hx : 0 ≤ x) (y : ℝ) (hy : 0 ≤ y) :
    logarithmicProfile σ (x+y) ≤ logarithmicProfile σ x+logarithmicProfile σ y := by
  have hden (t : ℝ) (ht : 0 ≤ t) : 0 < 1+(Real.log (1+t))^σ :=
    add_pos_of_pos_of_nonneg zero_lt_one (Real.rpow_nonneg (Real.log_nonneg (by linarith)) σ)
  have hdx : (Real.log (1+x))^σ ≤ (Real.log (1+(x+y)))^σ :=
    Real.rpow_le_rpow (Real.log_nonneg (by linarith))
      (Real.log_le_log (by linarith) (by linarith)) hσ
  have hdy : (Real.log (1+y))^σ ≤ (Real.log (1+(x+y)))^σ :=
    Real.rpow_le_rpow (Real.log_nonneg (by linarith))
      (Real.log_le_log (by linarith) (by linarith)) hσ
  unfold logarithmicProfile
  rw [add_div]
  apply add_le_add
  · apply (div_le_div_iff₀ (hden (x+y) (add_nonneg hx hy)) (hden x hx)).mpr
    nlinarith
  · apply (div_le_div_iff₀ (hden (x+y) (add_nonneg hx hy)) (hden y hy)).mpr
    nlinarith

/-- The p.105 logarithmic intermediate weight is an actual member of M. -/
def logarithmic (s a σ : ℝ) (hs : 0 ≤ s) (ha : 0 ≤ a)
    (hσ : 0 ≤ σ) (hσ1 : σ ≤ 1) : SpectralWeight :=
  (sobolev s hs).mul (expProfile (fun x => a*logarithmicProfile σ x)
    (fun x hx => mul_nonneg ha (logarithmicProfile_nonneg σ x hx))
    (fun x hx y hy hxy => mul_le_mul_of_nonneg_left
      (logarithmicProfile_monotone σ hσ hσ1 hx hy hxy) ha)
    (fun x hx y hy => by
      simpa only [mul_add] using mul_le_mul_of_nonneg_left
        (logarithmicProfile_add_le σ hσ x hx y hy) ha))

@[simp] theorem logarithmic_apply (s a σ : ℝ)
    (hs : 0 ≤ s) (ha : 0 ≤ a) (hσ : 0 ≤ σ) (hσ1 : σ ≤ 1) (n : ℤ) :
    logarithmic s a σ hs ha hσ hσ1 n =
      (1+|(n:ℝ)|)^s*Real.exp (a*|(n:ℝ)|/(1+(Real.log (1+|(n:ℝ)|))^σ)) := by
  simp only [logarithmic,mul_apply,sobolev_apply,Weight.sobolev_apply,
    expProfile_apply,logarithmicProfile,mul_div_assoc]

theorem hasLinearFactor_logarithmic (s a σ : ℝ)
    (hs : 1 ≤ s) (ha : 0 ≤ a) (hσ : 0 ≤ σ) (hσ1 : σ ≤ 1) :
    (logarithmic s a σ (zero_le_one.trans hs) ha hσ hσ1).HasLinearFactor :=
  (hasLinearFactor_sobolev s hs).mul_right _

end NLS.SpectralWeight
