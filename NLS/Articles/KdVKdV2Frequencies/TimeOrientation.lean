import NLS.Articles.KdVKdV2Frequencies.SmoothKdVIdentities
import NLS.Articles.KdVKdV2Frequencies.SignedPhaseFlow
import NLS.Fourier.DistributionModulation

/-! # The actual PDE fixes the Fourier time orientation

With the paper's Fourier coefficient convention, the linearizations of
(1) and (2) at zero have positive imaginary frequencies at positive modes.
The negative exponent printed on PDF p. 3 is inconsistent with these PDEs;
the positive exponent in (80)/(91) has the physical orientation.
-/
noncomputable section
set_option autoImplicit false
open Complex
open scoped ENNReal
open NLS.Fourier
namespace NLS.Articles.KdVKdV2Frequencies

/-- The physical linearized KdV operator acts by positive `i (2 pi n)^3`
on the n-th unit-period Fourier wave. -/
theorem linearKdV_unit_wave (n : ℤ) (x : ℝ) :
    -iteratedDeriv 3 (wave (2*n)) x =
      I*(2*(n:ℂ)*Real.pi)^3*wave (2*n) x := by
  rw [iteratedDeriv_wave]
  push_cast
  simp only [mul_pow,I_pow_three]
  ring

/-- The physical linearized KdV2 operator has the same positive time
orientation and the fifth-order free frequency. -/
theorem linearKdV2_unit_wave (n : ℤ) (x : ℝ) :
    iteratedDeriv 5 (wave (2*n)) x =
      I*(2*(n:ℂ)*Real.pi)^5*wave (2*n) x := by
  rw [iteratedDeriv_wave]
  push_cast
  simp only [mul_pow,I_pow_eq_pow_mod,show 5%4=1 from rfl,pow_one]
  ring

/-- This is the derivative of the actual nonlinear KdV field along a
Fourier perturbation of zero, rather than an assumed linear model. -/
theorem hasDerivAt_kdvRHS_zero_unit_wave (n : ℤ) (x : ℝ) :
    HasDerivAt (fun s : ℂ => kdvRHS (fun y => s*wave (2*n) y) x)
      (I*(2*(n:ℂ)*Real.pi)^3*wave (2*n) x) 0 := by
  have h1 := (hasDerivAt_id (0:ℂ)).mul_const (wave (2*n) x)
  have hd1 := (hasDerivAt_id (0:ℂ)).mul_const (iteratedDeriv 1 (wave (2*n)) x)
  have hd3 := (hasDerivAt_id (0:ℂ)).mul_const (iteratedDeriv 3 (wave (2*n)) x)
  have h := hd3.neg.add ((h1.mul hd1).const_mul 6)
  simpa only [Pi.add_def,Pi.neg_def,Pi.mul_def,kdvRHS,iteratedDeriv_const_mul_field,id_eq,mul_zero,zero_mul,
    add_zero,zero_add,one_mul,linearKdV_unit_wave,mul_assoc] using h

/-- The same positive fifth-order frequency is obtained by differentiating
all terms of the actual nonlinear KdV2 field at the zero potential. -/
theorem hasDerivAt_kdv2RHS_zero_unit_wave (n : ℤ) (x : ℝ) :
    HasDerivAt (fun s : ℂ => kdv2RHS (fun y => s*wave (2*n) y) x)
      (I*(2*(n:ℂ)*Real.pi)^5*wave (2*n) x) 0 := by
  have h0 := (hasDerivAt_id (0:ℂ)).mul_const (wave (2*n) x)
  have h1 := (hasDerivAt_id (0:ℂ)).mul_const (iteratedDeriv 1 (wave (2*n)) x)
  have h2 := (hasDerivAt_id (0:ℂ)).mul_const (iteratedDeriv 2 (wave (2*n)) x)
  have h3 := (hasDerivAt_id (0:ℂ)).mul_const (iteratedDeriv 3 (wave (2*n)) x)
  have h5 := (hasDerivAt_id (0:ℂ)).mul_const (iteratedDeriv 5 (wave (2*n)) x)
  have h := ((h5.sub ((h0.mul h3).const_mul 10)).sub ((h1.mul h2).const_mul 20)).add
    (((h0.pow 2).mul h1).const_mul 30)
  simpa only [Pi.add_def,Pi.sub_def,Pi.mul_def,Pi.pow_def,kdv2RHS,
    iteratedDeriv_const_mul_field,id_eq,mul_zero,zero_mul,add_zero,zero_add,sub_zero,
    one_mul,pow_two,linearKdV2_unit_wave,mul_assoc] using h

/-- Already at the first nonzero Fourier mode, the physical linearized
KdV field disagrees with the negative-time exponent printed on p. 3. -/
theorem linearKdV_first_wave_ne_negative :
    -iteratedDeriv 3 (wave 2) 0 ≠ -I*(2*(Real.pi:ℂ))^3 := by
  rw [show (2:ℤ)=2*1 from rfl,linearKdV_unit_wave]
  simp only [Int.cast_one,mul_one,wave_at_zero]
  have hn : I*(2*(Real.pi:ℂ))^3≠0 :=
    mul_ne_zero I_ne_zero (pow_ne_zero 3 (mul_ne_zero (by norm_num) (ofReal_ne_zero.mpr Real.pi_ne_zero)))
  intro he
  apply hn
  linear_combination he/2

/-- The signed coordinate-flow interface uses the physical positive
Fourier orientation on every positive mode. -/
theorem coordinateFlow_positive_component {p : ℝ≥0∞} [Fact (1≤p)]
    (w : Weight) (Ω : (ℤ → ℝ) → ℕ → ℝ) (t : ℝ)
    (a : SignedCoordinates w p) (n : ℕ) (hn : 1≤n) :
    (coordinateFlow w Ω t a).val.val (n:ℤ)=
      exp ((((t*Ω (WeightedCoeff.squaredAmplitudes a.val) n):ℝ):ℂ)*I)*a.val.val (n:ℤ) := by
  change (WeightedCoeff.actionPhaseFlow w (fun A => signedHamiltonianFrequency (Ω A)) t a.val).val (n:ℤ)=_
  rw [WeightedCoeff.actionPhaseFlow_apply]
  have hn0 : (0:ℤ)<(n:ℤ) := by omega
  simp only [signedHamiltonianFrequency,if_pos hn0,Int.natAbs_natCast]

/-- Its actual scalar time derivative has the same positive sign as
the physical PDE linearization. No frequency regularity is assumed. -/
theorem hasDerivAt_coordinateFlow_positive_component {p : ℝ≥0∞} [Fact (1≤p)]
    (w : Weight) (Ω : (ℤ → ℝ) → ℕ → ℝ) (t : ℝ)
    (a : SignedCoordinates w p) (n : ℕ) (hn : 1≤n) :
    HasDerivAt (fun s : ℝ => (coordinateFlow w Ω s a).val.val (n:ℤ))
      (I*(Ω (WeightedCoeff.squaredAmplitudes a.val) n:ℂ)*(coordinateFlow w Ω t a).val.val (n:ℤ)) t := by
  let ω := Ω (WeightedCoeff.squaredAmplitudes a.val) n
  have harg := (((hasDerivAt_id t).mul_const ω).ofReal_comp).mul_const I
  have hh := harg.cexp.mul_const (a.val.val (n:ℤ))
  simp_rw [coordinateFlow_positive_component w Ω _ a n hn]
  change HasDerivAt (fun s : ℝ => exp (((s*ω:ℝ):ℂ)*I)*a.val.val (n:ℤ))
    (I*(ω:ℂ)*(exp (((t*ω:ℝ):ℂ)*I)*a.val.val (n:ℤ))) t
  have he : I*(ω:ℂ)*(exp (((t*ω:ℝ):ℂ)*I)*a.val.val (n:ℤ)) =
      exp (((t*ω:ℝ):ℂ)*I)*(((1*ω:ℝ):ℂ)*I)*a.val.val (n:ℤ) := by
    rw [one_mul]
    ring
  rw [he]
  exact hh

end NLS.Articles.KdVKdV2Frequencies
