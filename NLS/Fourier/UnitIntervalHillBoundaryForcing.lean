import NLS.Fourier.AbsoluteContinuousCoefficients

noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology MeasureTheory
open scoped ENNReal Classical

namespace NLS.Fourier



/-- The half-interval coefficient retains its exact, frequency-dependent
boundary jump. The derivative is only specified almost everywhere. -/
theorem halfCoefficient_of_ac_hasDerivAt {f g : ℝ → ℂ}
    (hf : AbsolutelyContinuousOnInterval f 0 1)
    (hg : IntervalIntegrable g volume 0 1)
    (hfg : ∀ᵐ x ∂volume.restrict (Ioc (0 : ℝ) 1), HasDerivAt f (g x) x) (n : ℤ) :
    halfCoefficient g n = I*(Real.pi : ℂ)*n*halfCoefficient f n +
      (f 1*wave (-n) 1-f 0)/2 := by
  have hder : (deriv f) =ᵐ[volume.restrict (Ioc (0 : ℝ) 1)] g :=
    hfg.mono (fun _ hx => hx.deriv)
  have hfi : IntervalIntegrable (deriv f) volume 0 1 :=
    hg.congr_ae (by simpa only [uIoc_of_le (by norm_num : (0 : ℝ) ≤ 1)] using hder.symm)
  have hw := (contDiff_wave (-n)).contDiffOn.absolutelyContinuousOnInterval
    (a := (0 : ℝ)) (b := 1)
  have hwi : IntervalIntegrable (deriv (wave (-n))) volume 0 1 := by
    rw [deriv_wave]
    exact (continuous_const.mul (continuous_wave (-n))).intervalIntegrable 0 1
  have h := FunctionalAnalysis.integral_mul_deriv_eq_complex hf hw hfi hwi
  have he : (fun x => f x * deriv (wave (-n)) x) =
      fun x => -(I*(Real.pi : ℂ)*n)*(f x*wave (-n) x) := by
    funext x
    rw [deriv_wave]
    push_cast
    ring
  have hcongr : (∫ x in (0 : ℝ)..1, deriv f x*wave (-n) x) =
      ∫ x in (0 : ℝ)..1, g x*wave (-n) x := by
    apply intervalIntegral.integral_congr_ae_restrict
    rw [uIoc_of_le (by norm_num : (0 : ℝ) ≤ 1)]
    filter_upwards [hder] with x hx
    rw [hx]
  rw [he,intervalIntegral.integral_const_mul,hcongr,wave_at_zero,mul_one] at h
  unfold halfCoefficient
  linear_combination (1/2 : ℂ)*h

/-- The Fourier form of a rough scalar Hill equation includes both position
and derivative jumps. No periodic endpoint matching is assumed. -/
theorem halfCoefficient_hill_equation_with_boundary
    (Q f g : ℝ → ℂ) (energy : ℂ)
    (hf : AbsolutelyContinuousOnInterval f 0 1)
    (hg : AbsolutelyContinuousOnInterval g 0 1)
    (hQf : IntervalIntegrable (fun x => Q x*f x) volume 0 1)
    (hfg : ∀ᵐ x ∂volume.restrict (Ioc (0 : ℝ) 1), HasDerivAt f (g x) x)
    (hgQ : ∀ᵐ x ∂volume.restrict (Ioc (0 : ℝ) 1),
      HasDerivAt g ((Q x-energy)*f x) x) (n : ℤ) :
    (energy-(Real.pi : ℂ)^2*(n : ℂ)^2)*halfCoefficient f n =
      halfCoefficient (fun x => Q x*f x) n -
        (g 1*wave (-n) 1-g 0)/2 -
        (I*(Real.pi : ℂ)*n)*(f 1*wave (-n) 1-f 0)/2 := by
  have hfi : IntervalIntegrable f volume 0 1 := hf.continuousOn.intervalIntegrable
  have hgi : IntervalIntegrable g volume 0 1 := hg.continuousOn.intervalIntegrable
  have hprod : IntervalIntegrable (fun x => (Q x-energy)*f x) volume 0 1 := by
    convert hQf.sub (hfi.const_mul energy) using 1
    funext x
    ring
  have h1 := halfCoefficient_of_ac_hasDerivAt hf hgi hfg n
  have h2 := halfCoefficient_of_ac_hasDerivAt hg hprod hgQ n
  have he : halfCoefficient (fun x => (Q x-energy)*f x) n =
      halfCoefficient (fun x => Q x*f x) n-energy*halfCoefficient f n := by
    unfold halfCoefficient
    have hp : (fun x => (Q x-energy)*f x*wave (-n) x) =
        fun x => Q x*f x*wave (-n) x-energy*(f x*wave (-n) x) := by funext x; ring
    rw [hp,intervalIntegral.integral_sub
      (hQf.mul_continuousOn (continuous_wave (-n)).continuousOn)
      ((hfi.mul_continuousOn (continuous_wave (-n)).continuousOn).const_mul energy),
      intervalIntegral.integral_const_mul]
    ring
  rw [he,h1] at h2
  have hI : (I : ℂ)^2 = -1 := I_sq
  linear_combination -h2 - (Real.pi : ℂ)^2*(n : ℂ)^2*halfCoefficient f n*(hI)

/-- A Dirichlet solution has only the derivative-jump forcing term. -/
theorem halfCoefficient_hill_dirichlet_boundary_forcing
    (Q f g : ℝ → ℂ) (energy : ℂ)
    (hf : AbsolutelyContinuousOnInterval f 0 1)
    (hg : AbsolutelyContinuousOnInterval g 0 1)
    (hQf : IntervalIntegrable (fun x => Q x*f x) volume 0 1)
    (hfg : ∀ᵐ x ∂volume.restrict (Ioc (0 : ℝ) 1), HasDerivAt f (g x) x)
    (hgQ : ∀ᵐ x ∂volume.restrict (Ioc (0 : ℝ) 1),
      HasDerivAt g ((Q x-energy)*f x) x)
    (h0 : f 0=0) (h1 : f 1=0) (n : ℤ) :
    (energy-(Real.pi : ℂ)^2*(n : ℂ)^2)*halfCoefficient f n =
      halfCoefficient (fun x => Q x*f x) n-(g 1*wave (-n) 1-g 0)/2 := by
  simpa only [h0,h1,zero_mul,sub_self,mul_zero,zero_div,sub_zero] using
    halfCoefficient_hill_equation_with_boundary Q f g energy hf hg hQf hfg hgQ n

end NLS.Fourier
