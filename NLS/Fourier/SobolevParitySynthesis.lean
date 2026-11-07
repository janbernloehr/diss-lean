import NLS.Fourier.SobolevEnergy
import NLS.Fourier.PeriodOneCoefficients

/-! Fourier parity gives actual physical period-one/antiperiod-one H1
representatives and the EXACT unit-interval L2 normalization. -/
noncomputable section
open Set MeasureTheory
open scoped ENNReal
namespace NLS.Fourier
open NLS.ZakharovShabat

/-- Physical one-step Fourier phases agree on every single parity class. -/
theorem wave_one_eq_of_parity (k r : ℤ) (h : k%2=r%2) : wave k 1=wave r 1 := by
  by_cases hr : r%2=0
  · have hk : k=2*(k/2) := by omega
    have he : r=2*(r/2) := by omega
    rw [hk,he,wave_even_at_one,wave_even_at_one]
  · have hk : k=2*(k/2)+1 := by omega
    have he : r=2*(r/2)+1 := by omega
    rw [hk,he,wave_odd_at_one,wave_odd_at_one]

/-- The original physical phase at displacement ONE has exact norm ONE. -/
theorem norm_wave_one (r : ℤ) : ‖wave r 1‖=1 := by
  by_cases hr : r%2=0
  · have he : r=2*(r/2) := by omega
    rw [he,wave_even_at_one,norm_one]
  · have he : r=2*(r/2)+1 := by omega
    rw [he,wave_odd_at_one,norm_neg,norm_one]

/-- The actual continuous H1 representative has the exact physical
period-one/antiperiod-one translation law at EVERY real point. -/
theorem sobolevSynthesis_translate_one_of_parity (r : ℤ) (a : ScalarDomain 2)
    (ha : ∀ k : ℤ, k%2 ≠ r%2 → a.val k=0) (x : ℝ) :
    sobolevSynthesis (by simp) a ((x+1:ℝ) : AddCircle (2:ℝ))=
      wave r 1*sobolevSynthesis (by simp) a (x : AddCircle (2:ℝ)) := by
  have hx (y : ℝ) : HasSum (fun k : ℤ => a.val k*wave k y)
      (sobolevSynthesis (by simp) a (y : AddCircle (2:ℝ))) := by
    have h := (ContinuousMap.evalCLM ℂ (y : AddCircle (2:ℝ))).hasSum (hasSum_sobolevSynthesis (by simp) a)
    simpa only [ContinuousLinearMap.comp_apply,ContinuousMap.evalCLM_apply,ContinuousMap.smul_apply,
      smul_eq_mul,fourier_two_eq_wave] using h
  calc
    _ = ∑' k : ℤ, a.val k*wave k (x+1) := (hx (x+1)).tsum_eq.symm
    _ = ∑' k : ℤ, wave r 1*(a.val k*wave k x) := by
      apply tsum_congr
      intro k
      by_cases hk : k%2=r%2
      · rw [wave_add_argument,wave_one_eq_of_parity k r hk]
        ring
      · rw [ha k hk,zero_mul,zero_mul,mul_zero]
    _ = wave r 1*(∑' k : ℤ, a.val k*wave k x) := tsum_mul_left
    _ = _ := by rw [(hx x).tsum_eq]

/-- For either physical parity, the ORIGINAL normalized period-two L2 norm
is exactly the UNNORMALIZED unit-interval norm, with NO factor two lost. -/
theorem integral_sq_sobolevSynthesis_unit_of_parity (r : ℤ) (a : ScalarDomain 2)
    (ha : ∀ k : ℤ, k%2 ≠ r%2 → a.val k=0) :
    (∫ x in (0:ℝ)..1, ‖sobolevSynthesis (by simp) a (x : AddCircle (2:ℝ))‖^2)=‖scalarInclusion a‖^2 := by
  let g := fun x : ℝ => ‖sobolevSynthesis (by simp) a (x : AddCircle (2:ℝ))‖^2
  have hg : Continuous g := (continuous_sobolevSynthesis (by simp) a).norm.pow 2
  have hper (x : ℝ) : g (x+1)=g x := by
    have h := congrArg (fun z : ℂ => ‖z‖^2) (sobolevSynthesis_translate_one_of_parity r a ha x)
    simpa only [g,norm_mul,norm_wave_one,one_mul] using h
  have hshift : (∫ x in (1:ℝ)..2, g x)=(∫ x in (0:ℝ)..1, g x) := by
    have h := intervalIntegral.integral_comp_add_right (a := (0:ℝ)) (b := 1) g 1
    simp only [zero_add,one_add_one_eq_two,hper] at h
    exact h.symm
  have hsplit : (∫ x in (0:ℝ)..1, g x)+(∫ x in (1:ℝ)..2, g x)=(∫ x in (0:ℝ)..2, g x) :=
    intervalIntegral.integral_add_adjacent_intervals (hg.intervalIntegrable 0 1) (hg.intervalIntegrable 1 2)
  rw [hshift] at hsplit
  have hfull := integral_sq_sobolevSynthesis a
  change (∫ x in (0:ℝ)..2, g x)=2*‖scalarInclusion a‖^2 at hfull
  change (∫ x in (0:ℝ)..1, g x)=‖scalarInclusion a‖^2
  nlinarith

end NLS.Fourier
