import NLS.Fourier.IntervalH1Reflection
import NLS.Fourier.SignedSobolevExtension

/-! # Signed extension of the full classical interval H¹ domain -/
noncomputable section
set_option autoImplicit false
open Set Complex MeasureTheory
namespace NLS.Fourier

/-- The signed extension Fourier formula requires only integrability on [0,1]. -/
theorem periodTwoCoefficient_signedDouble_of_intervalIntegrable (ε : ℂ) {f : ℝ → ℂ}
    (hf : IntervalIntegrable f volume 0 1) (n : ℤ) :
    periodTwoCoefficient (signedDouble ε f) n = (1+ε*wave (-n) 1)*halfCoefficient f n := by
  let g := fun x => signedDouble ε f x * wave (-n) x
  have h₀ : IntervalIntegrable g volume 0 1 :=
    (hf.mul_continuousOn (continuous_wave (-n)).continuousOn).congr (fun x hx => by
      have hx' : x ≤ 1 := (show x ∈ Ioc (0 : ℝ) 1 from by simpa using hx).2
      simp only [g,signedDouble_left ε f hx'])
  have hshift : IntervalIntegrable (fun x => f (x-1)) volume 1 2 := by
    simpa only [zero_add,one_add_one_eq_two] using hf.comp_sub_right 1
  have h₁ : IntervalIntegrable g volume 1 2 :=
    ((hshift.const_mul ε).mul_continuousOn (continuous_wave (-n)).continuousOn).congr (fun x hx => by
      have hx' : 1 < x := (show x ∈ Ioc (1 : ℝ) 2 from by simpa using hx).1
      simp only [g,signedDouble_right ε f hx'])
  have hleft : (∫ x in (0 : ℝ)..1, g x) = ∫ x in (0 : ℝ)..1, f x*wave (-n) x := by
    apply intervalIntegral.integral_congr
    intro x hx
    simp only [g,signedDouble_left ε f (show x ≤ 1 from (uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1) ▸ hx).2)]
  have hright : (∫ x in (1 : ℝ)..2, g x) = ε*wave (-n) 1 * ∫ x in (0 : ℝ)..1, f x*wave (-n) x := by
    rw [← show (∫ x in (0 : ℝ)..1, g (x+1)) = ∫ x in (1 : ℝ)..2, g x by
      simpa only [zero_add,one_add_one_eq_two] using intervalIntegral.integral_comp_add_right (a := 0) (b := 1) g 1]
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr_ae
    filter_upwards with x hx
    have hx' : 0 < x := (show x ∈ Ioc (0 : ℝ) 1 from by simpa using hx).1
    simp only [g,signedDouble_right ε f (show 1 < x+1 by linarith),add_sub_cancel_right,wave_add_argument]
    ring
  change (1/2 : ℂ)*(∫ x in (0 : ℝ)..2, g x) = _
  rw [← intervalIntegral.integral_add_adjacent_intervals h₀ h₁,hleft,hright]
  unfold halfCoefficient
  ring

/-- Opposite Fourier parity cancels for arbitrary integrable original interval inputs. -/
theorem periodTwoCoefficient_signedDouble_parity_of_intervalIntegrable (r : ℤ) {f : ℝ → ℂ}
    (hf : IntervalIntegrable f volume 0 1) (n : ℤ) (hn : n%2 ≠ r%2) :
    periodTwoCoefficient (signedDouble (wave r 1) f) n = 0 := by
  rw [periodTwoCoefficient_signedDouble_of_intervalIntegrable (wave r 1) hf n,← wave_add]
  have he : r + -n = 2*((r-n)/2)+1 := by omega
  rw [he,wave_odd_at_one]
  ring

/-- The endpoint identity suffices for absolute continuity of the actual H¹ signed extension. -/
theorem absolutelyContinuous_signedDouble_of_intervalH1 (ε : ℂ) {f : ℝ → ℂ}
    (hf : HasIntervalH1Regularity f) (hend : f 1 = ε*f 0) :
    AbsolutelyContinuousOnInterval (signedDouble ε f) 0 2 := by
  rw [signedDouble_eq_folded]
  exact absolutelyContinuous_folded ε hf hf.reflect (by simpa using hend)

/-- The actual derivative remains in L² for the full interval H¹ class. -/
theorem memLp_deriv_signedDouble_of_intervalH1 (ε : ℂ) {f : ℝ → ℂ}
    (hf : HasIntervalH1Regularity f) (hend : f 1 = ε*f 0) :
    MemLp (deriv (signedDouble ε f)) 2 (volume.restrict (Ioc 0 2)) := by
  rw [signedDouble_eq_folded]
  exact memLp_deriv_folded ε hf hf.reflect (by simpa using hend)

/-- Original normalized Fourier coordinates of the classical signed interval domain. -/
def signedSobolevCoefficients (r : ℤ) (f : ℝ → ℂ) (hf : HasIntervalH1Regularity f)
    (hend : f 1 = wave r 1*f 0) : ZakharovShabat.ScalarDomain 2 :=
  sobolevCoefficients
    (periodicSobolevLift (signedDouble (wave r 1) f)
      (absolutelyContinuous_signedDouble_of_intervalH1 (wave r 1) hf hend)
      (signedDouble_matching_endpoints (wave r 1) (wave_one_sq r) hend))
    (hasPeriodicH1Regularity_periodicSobolevLift _
      (absolutelyContinuous_signedDouble_of_intervalH1 (wave r 1) hf hend)
      (memLp_deriv_signedDouble_of_intervalH1 (wave r 1) hf hend)
      (signedDouble_matching_endpoints (wave r 1) (wave_one_sq r) hend))

@[simp] theorem signedSobolevCoefficients_apply (r : ℤ) (f : ℝ → ℂ)
    (hf : HasIntervalH1Regularity f) (hend : f 1 = wave r 1*f 0) (n : ℤ) :
    (signedSobolevCoefficients r f hf hend).val n =
      periodTwoCoefficient (signedDouble (wave r 1) f) n := by
  unfold signedSobolevCoefficients
  rw [sobolevCoefficients_apply,fourierCoeff_periodicSobolevLift]

/-- Every coefficient of the opposite parity vanishes, without extra smoothness assumptions. -/
theorem signedSobolevCoefficients_parity (r : ℤ) (f : ℝ → ℂ)
    (hf : HasIntervalH1Regularity f) (hend : f 1 = wave r 1*f 0) (n : ℤ) (hn : n%2 ≠ r%2) :
    (signedSobolevCoefficients r f hf hend).val n = 0 := by
  rw [signedSobolevCoefficients_apply]
  exact periodTwoCoefficient_signedDouble_parity_of_intervalIntegrable r
    hf.1.continuousOn.intervalIntegrable n hn

/-- Synthesis reconstructs the actual signed extension, including both endpoints and the join. -/
theorem sobolevSynthesis_signedSobolevCoefficients (r : ℤ) (f : ℝ → ℂ)
    (hf : HasIntervalH1Regularity f) (hend : f 1 = wave r 1*f 0) {x : ℝ}
    (hx : x ∈ Icc (0 : ℝ) 2) :
    sobolevSynthesis (by simp) (signedSobolevCoefficients r f hf hend)
      (x : AddCircle (2 : ℝ)) = signedDouble (wave r 1) f x := by
  unfold signedSobolevCoefficients
  rw [sobolevSynthesis_sobolevCoefficients]
  exact periodicSobolevLift_apply _ _ _ hx

end NLS.Fourier
