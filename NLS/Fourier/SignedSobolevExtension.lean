import NLS.Fourier.PeriodicSobolevLift
import NLS.ZakharovShabat.PhysicalParity
import Mathlib.Analysis.Calculus.ContDiff.Deriv

/-!
# Signed extension of classical functions to the full period

A function on the unit interval whose endpoint multiplier is a sign extends
by signed translation to a periodic Sobolev function on the doubled interval.
Its original Fourier integrals have exactly the corresponding parity support.
-/

noncomputable section
open Set Complex MeasureTheory
namespace NLS.Fourier

/-- Repeat the unit interval with a prescribed scalar multiplier. -/
def signedDouble (ε : ℂ) (f : ℝ → ℂ) (x : ℝ) : ℂ :=
  if x ≤ 1 then f x else ε * f (x-1)

@[simp] theorem signedDouble_left (ε : ℂ) (f : ℝ → ℂ) {x : ℝ} (hx : x ≤ 1) :
    signedDouble ε f x = f x := if_pos hx

@[simp] theorem signedDouble_right (ε : ℂ) (f : ℝ → ℂ) {x : ℝ} (hx : 1 < x) :
    signedDouble ε f x = ε * f (x-1) := if_neg (not_le.mpr hx)

/-- The signed repetition is a fold of the reflected original function. -/
theorem signedDouble_eq_folded (ε : ℂ) (f : ℝ → ℂ) :
    signedDouble ε f = folded ε f (fun x => f (1-x)) := by
  funext x
  simp only [signedDouble,folded]
  split_ifs
  · rfl
  · rw [show 1-(2-x) = x-1 by ring]

/-- A continuously differentiable scalar function has classical interval Sobolev regularity. -/
theorem hasIntervalH1Regularity_of_contDiff {f : ℝ → ℂ} (hf : ContDiff ℝ 1 f) :
    HasIntervalH1Regularity f := by
  refine ⟨hf.contDiffOn.absolutelyContinuousOnInterval,?_⟩
  have hc := (contDiff_one_iff_deriv.mp hf).2
  have hi : IntegrableOn (deriv f) (Ioc 0 1) volume :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num)).mp (hc.intervalIntegrable 0 1)
  apply (memLp_two_iff_integrable_sq_norm hi.aestronglyMeasurable).mpr
  exact (intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num)).mp
    ((hc.norm.pow 2).intervalIntegrable 0 1)

/-- Endpoint matching makes the signed extension absolutely continuous across its join. -/
theorem absolutelyContinuous_signedDouble (ε : ℂ) {f : ℝ → ℂ} (hf : ContDiff ℝ 1 f)
    (hend : f 1 = ε * f 0) : AbsolutelyContinuousOnInterval (signedDouble ε f) 0 2 := by
  rw [signedDouble_eq_folded]
  exact absolutelyContinuous_folded ε (hasIntervalH1Regularity_of_contDiff hf)
    (hasIntervalH1Regularity_of_contDiff (hf.comp (contDiff_const.sub contDiff_id))) (by simpa using hend)

/-- The derivative of the joined signed extension remains square integrable. -/
theorem memLp_deriv_signedDouble (ε : ℂ) {f : ℝ → ℂ} (hf : ContDiff ℝ 1 f)
    (hend : f 1 = ε * f 0) : MemLp (deriv (signedDouble ε f)) 2 (volume.restrict (Ioc 0 2)) := by
  rw [signedDouble_eq_folded]
  exact memLp_deriv_folded ε (hasIntervalH1Regularity_of_contDiff hf)
    (hasIntervalH1Regularity_of_contDiff (hf.comp (contDiff_const.sub contDiff_id))) (by simpa using hend)

/-- A sign multiplier makes the two endpoints of the doubled interval agree. -/
theorem signedDouble_matching_endpoints (ε : ℂ) (hε : ε^2 = 1) {f : ℝ → ℂ}
    (hend : f 1 = ε*f 0) : signedDouble ε f 0 = signedDouble ε f 2 := by
  simp only [signedDouble_left ε f (by norm_num : (0 : ℝ) ≤ 1),
    signedDouble_right ε f (by norm_num : (1 : ℝ) < 2),show (2 : ℝ)-1 = 1 by norm_num,hend]
  rw [← mul_assoc,← pow_two,hε,one_mul]

/-- The actual normalized Fourier integral of signed repetition splits into its two halves. -/
theorem periodTwoCoefficient_signedDouble (ε : ℂ) {f : ℝ → ℂ}
    (hf : Continuous f) (n : ℤ) :
    periodTwoCoefficient (signedDouble ε f) n = (1+ε*wave (-n) 1)*halfCoefficient f n := by
  let g := fun x => signedDouble ε f x * wave (-n) x
  have h₀ : IntervalIntegrable g volume 0 1 :=
    ((hf.mul (continuous_wave (-n))).intervalIntegrable 0 1).congr (fun x hx => by
      have hx' : x ≤ 1 := (show x ∈ Ioc (0 : ℝ) 1 from by simpa using hx).2
      simp only [g,signedDouble_left ε f hx',Pi.mul_apply])
  have hc1 : Continuous (fun x : ℝ => ε*f (x-1)*wave (-n) x) := by fun_prop
  have h₁ : IntervalIntegrable g volume 1 2 :=
    (hc1.intervalIntegrable 1 2).congr (fun x hx => by
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

/-- The unit phase is a sign, for every integer including negative parity labels. -/
theorem wave_one_sq (r : ℤ) : (wave r 1)^2 = 1 := by
  rw [pow_two,← wave_add,show r+r = 2*r by ring,wave_even_at_one]

/-- Opposite Fourier parity cancels in the actual two-half integral. -/
theorem periodTwoCoefficient_signedDouble_parity (r : ℤ) {f : ℝ → ℂ}
    (hf : Continuous f) (n : ℤ) (hn : n%2 ≠ r%2) :
    periodTwoCoefficient (signedDouble (wave r 1) f) n = 0 := by
  rw [periodTwoCoefficient_signedDouble (wave r 1) hf n,← wave_add]
  have he : r + -n = 2*((r-n)/2)+1 := by omega
  rw [he,wave_odd_at_one]
  ring

/-- Signed endpoint solutions have original weighted Fourier coordinates with exactly the required support. -/
theorem exists_parity_sobolev_extension (r : ℤ) {f : ℝ → ℂ} (hf : ContDiff ℝ 1 f)
    (hend : f 1 = wave r 1 * f 0) :
    ∃ a : ZakharovShabat.ScalarDomain 2,
      (∀ n : ℤ, n%2 ≠ r%2 → a.val n = 0) ∧
      ∀ x ∈ Icc (0 : ℝ) 2,
        sobolevSynthesis (by simp) a (x : AddCircle (2 : ℝ)) = signedDouble (wave r 1) f x := by
  obtain ⟨a,ha,hs⟩ := exists_weighted_representation_of_interval _
    (absolutelyContinuous_signedDouble (wave r 1) hf hend)
    (memLp_deriv_signedDouble (wave r 1) hf hend)
    (signedDouble_matching_endpoints (wave r 1) (wave_one_sq r) hend)
  refine ⟨a,?_,hs⟩
  intro n hn
  rw [ha]
  exact periodTwoCoefficient_signedDouble_parity r hf.continuous n hn

end NLS.Fourier
