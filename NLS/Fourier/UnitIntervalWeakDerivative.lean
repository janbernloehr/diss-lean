import NLS.Fourier.AbsoluteContinuousCoefficients
import NLS.Fourier.UnitIntervalL2Equiv
import NLS.FunctionalAnalysis.LocallyIntegrablePrimitive

/-! # Interval weak derivatives with the actual endpoint defect

The Fourier derivative equation for an interval function includes a constant
coefficient defect. This is the difference of endpoint values, rather than
an extra periodicity condition. L2 data and an L1 forcing suffice to recover
an absolutely continuous representative on the entire closed unit interval.
-/
noncomputable section
open Set Complex MeasureTheory
open scoped ENNReal
namespace NLS.Fourier
open NLS.FunctionalAnalysis

/-- Integration by parts retains the endpoint jump at EVERY unit frequency. -/
theorem unitFourierCoefficient_deriv_of_ac {f : ℝ → ℂ}
    (hf : AbsolutelyContinuousOnInterval f 0 1)
    (hfi : IntervalIntegrable (deriv f) volume 0 1) (n : ℤ) :
    unitFourierCoefficient (deriv f) n =
      2*I*(Real.pi:ℂ)*n*unitFourierCoefficient f n + (f 1-f 0) := by
  have hw := (contDiff_wave (-(2*n))).contDiffOn.absolutelyContinuousOnInterval
    (a := (0:ℝ)) (b := 1)
  have hwi : IntervalIntegrable (deriv (wave (-(2*n)))) volume 0 1 := by
    rw [deriv_wave]
    exact (continuous_const.mul (continuous_wave (-(2*n)))).intervalIntegrable 0 1
  have h := integral_mul_deriv_eq_complex hf hw hfi hwi
  have hw1 : wave (-(2*n)) 1 = 1 := by
    rw [show -(2*n) = 2*(-n) by ring, wave_even_at_one]
  simp only [deriv_wave, hw1, wave_at_zero, mul_one] at h
  have he : (fun t => f t*(I*(Real.pi:ℂ)*(-(2*n):ℤ)*wave (-(2*n)) t)) =
      fun t => -(2*I*(Real.pi:ℂ)*n)*(f t*wave (-(2*n)) t) := by
    funext t
    push_cast
    ring
  rw [he, intervalIntegral.integral_const_mul] at h
  unfold unitFourierCoefficient
  linear_combination h

/-- The unit coefficient normalization agrees with the actual unit L2 equivalence. -/
theorem unitFourierCoefficient_eq_intervalFourierCoefficient (f : ℝ → ℂ) (n : ℤ) :
    unitFourierCoefficient f n = intervalFourierCoefficient 1 f n :=
  (unitFourierCoefficient_eq_fourierCoeffOn f n).trans
    (intervalFourierCoefficient_eq_fourierCoeffOn (by norm_num) f n).symm

theorem unitFourierCoefficient_congr_ae {f g : ℝ → ℂ}
    (h : f =ᵐ[volume.restrict (Ioc 0 1)] g) (n : ℤ) :
    unitFourierCoefficient f n = unitFourierCoefficient g n := by
  rw [unitFourierCoefficient_eq_fourierCoeffOn, unitFourierCoefficient_eq_fourierCoeffOn]
  exact congrFun (fourierCoeffOn_congr_ae (by norm_num) h) n

/-- Constants occupy exactly the central frequency, with no scaling factor. -/
theorem unitFourierCoefficient_const (c : ℂ) (n : ℤ) :
    unitFourierCoefficient (fun _ => c) n = if n = 0 then c else 0 := by
  unfold unitFourierCoefficient
  rw [intervalIntegral.integral_const_mul]
  change c*unitIntegral (-(2*n)) = _
  rw [show -(2*n) = 2*(-n) by ring, unitIntegral_even]
  by_cases hn : n = 0 <;> simp only [hn, neg_zero, ite_true, mul_one,
    neg_eq_zero, ite_false, mul_zero]

/-- Actual unit Fourier integrals are additive on interval L1 inputs. -/
theorem unitFourierCoefficient_add (f g : ℝ → ℂ)
    (hf : IntervalIntegrable f volume 0 1) (hg : IntervalIntegrable g volume 0 1) (n : ℤ) :
    unitFourierCoefficient (fun x => f x+g x) n =
      unitFourierCoefficient f n+unitFourierCoefficient g n := by
  unfold unitFourierCoefficient
  simp only [add_mul]
  exact intervalIntegral.integral_add
    (hf.mul_continuousOn (continuous_wave _).continuousOn)
    (hg.mul_continuousOn (continuous_wave _).continuousOn)

/-- Adding a constant changes only the zero coefficient of any integrable input. -/
theorem unitFourierCoefficient_add_const (f : ℝ → ℂ)
    (hf : IntervalIntegrable f volume 0 1) (c : ℂ) (n : ℤ) :
    unitFourierCoefficient (fun x => f x+c) n =
      unitFourierCoefficient f n + if n = 0 then c else 0 := by
  unfold unitFourierCoefficient
  simp only [add_mul]
  have hi1 : IntervalIntegrable (fun x => f x*wave (-(2*n)) x) volume 0 1 :=
    hf.mul_continuousOn (continuous_wave _).continuousOn
  have hi2 : IntervalIntegrable (fun x => c*wave (-(2*n)) x) volume 0 1 :=
    (continuous_const.mul (continuous_wave _)).intervalIntegrable 0 1
  rw [intervalIntegral.integral_add hi1 hi2]
  exact congrArg (fun z => (∫ x in (0:ℝ)..1, f x*wave (-(2*n)) x)+z)
    (unitFourierCoefficient_const c n)

/-- A constant Fourier defect is exactly the allowed endpoint jump. Only
L2 data and interval L1 forcing are assumed; the derivative need not be periodic. -/
theorem exists_ac_unitInterval_representative_of_fourier_equation
    (f g : ℝ → ℂ) (hf : MemLp f 2 (volume.restrict (Ioc 0 1)))
    (hg : IntervalIntegrable g volume 0 1) (c : ℂ)
    (he : ∀ n : ℤ, 2*I*(Real.pi:ℂ)*n*unitFourierCoefficient f n =
      unitFourierCoefficient g n+c) :
    ∃ F : ℝ → ℂ, Continuous F ∧ AbsolutelyContinuousOnInterval F 0 1 ∧
      f =ᵐ[volume.restrict (Ioc 0 1)] F ∧
      (∀ᵐ x ∂volume.restrict (Ioc 0 1), HasDerivAt F (g x) x) ∧ F 1-F 0 = -c := by
  let g0 := (Ioc (0:ℝ) 1).indicator g
  have hg0 : Integrable g0 volume :=
    ((intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num)).mp hg).integrable_indicator
      measurableSet_Ioc
  have hgg : g0 =ᵐ[volume.restrict (Ioc 0 1)] g := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx
    exact indicator_of_mem hx g
  let G := fun x : ℝ => ∫ t in (0:ℝ)..x, g0 t
  have hGc : Continuous G := continuous_local_primitive hg0.locallyIntegrable 0
  have hGa : AbsolutelyContinuousOnInterval G 0 1 :=
    absolutelyContinuousOnInterval_local_primitive hg0.locallyIntegrable 0 0 1
  have hGd : ∀ᵐ x : ℝ, HasDerivAt G (g0 x) x := by
    filter_upwards [_root_.LocallyIntegrable.ae_hasDerivAt_integral hg0.locallyIntegrable]
      with x hx
    exact hx 0
  have hactual : deriv G =ᵐ[volume] g0 := by
    filter_upwards [hGd] with x hx
    exact hx.deriv
  have hGi : IntervalIntegrable (deriv G) volume 0 1 :=
    (hg0.intervalIntegrable).congr_ae (ae_restrict_of_ae hactual.symm)
  have hcoeff (n : ℤ) : unitFourierCoefficient g n =
      2*I*(Real.pi:ℂ)*n*unitFourierCoefficient G n+(G 1-G 0) := by
    rw [← unitFourierCoefficient_congr_ae hgg,
      ← unitFourierCoefficient_congr_ae (ae_restrict_of_ae hactual),
      unitFourierCoefficient_deriv_of_ac hGa hGi]
  have hjump : G 1-G 0 = -c := by
    have hz := he 0
    rw [hcoeff 0] at hz
    simp only [Int.cast_zero, mul_zero, zero_mul, zero_add] at hz
    linear_combination -hz
  let d := unitFourierCoefficient f 0-unitFourierCoefficient G 0
  let F := fun x => G x+d
  have hFc : Continuous F := hGc.add continuous_const
  have hFa : AbsolutelyContinuousOnInterval F 0 1 := by
    simpa only [add_comm] using absolutelyContinuousOnInterval_const_add hGa d
  have hFcoeff (n : ℤ) : unitFourierCoefficient F n = unitFourierCoefficient f n := by
    rw [unitFourierCoefficient_add_const G (hGc.intervalIntegrable 0 1) d n]
    by_cases hn : n = 0
    · simp only [hn, ite_true, d]
      ring
    · rw [if_neg hn, add_zero]
      have h := he n
      rw [hcoeff n, hjump] at h
      have hnonzero : 2*I*(Real.pi:ℂ)*(n:ℂ) ≠ 0 := by
        exact mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num) I_ne_zero)
          (ofReal_ne_zero.mpr Real.pi_ne_zero)) (by exact_mod_cast hn)
      apply (mul_left_cancel₀ hnonzero)
      linear_combination -h
  have hFm := memLp_two_interval hFc 0 1 (by norm_num)
  have hclasses : hf.toLp f = hFm.toLp F := by
    apply unitL2_ext_coefficients
    intro n
    rw [← unitFourierCoefficient_eq_intervalFourierCoefficient,
      ← unitFourierCoefficient_eq_intervalFourierCoefficient,
      unitFourierCoefficient_congr_ae hf.coeFn_toLp,
      unitFourierCoefficient_congr_ae hFm.coeFn_toLp]
    exact (hFcoeff n).symm
  refine ⟨F, hFc, hFa, ?_, ?_, ?_⟩
  · exact hf.coeFn_toLp.symm.trans (hclasses ▸ hFm.coeFn_toLp)
  · filter_upwards [ae_restrict_of_ae hGd, hgg] with x hx hgx
    simpa only [hgx] using hx.add_const d
  · change (G 1+d)-(G 0+d) = -c
    linear_combination hjump

end NLS.Fourier
