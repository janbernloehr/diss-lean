import NLS.Fourier.UnitIntervalWeakDerivative
import NLS.Fourier.UnitIntervalEnergyBound
import NLS.Poisson.GardnerBivector
import NLS.Fourier.IntervalBilinearParseval

noncomputable section
set_option autoImplicit false
open Set Complex Filter Topology MeasureTheory
open scoped ENNReal

namespace NLS.Fourier



/-- Actual unit Fourier coefficients of an absolutely continuous closed
curve with a continuous prescribed derivative obey the exact unit-period
spatial multiplier, without requiring a chosen global C1 extension. -/
theorem unitFourierCoefficient_ac_periodic_prescribed_derivative
    (f g : ℝ → ℂ) (hf : AbsolutelyContinuousOnInterval f 0 1) (hg : Continuous g)
    (hd : ∀ᵐ x ∂volume.restrict (Ioc (0 : ℝ) 1), HasDerivAt f (g x) x)
    (hp : f 1=f 0) (k : ℤ) :
    unitFourierCoefficient g k=2*I*(Real.pi : ℂ)*k*unitFourierCoefficient f k := by
  have he : deriv f=ᵐ[volume.restrict (Ioc (0 : ℝ) 1)] g := by
    filter_upwards [hd] with x hx
    exact hx.deriv
  have hdi : IntervalIntegrable (deriv f) volume 0 1 :=
    (hg.intervalIntegrable 0 1).congr_ae (by
      simpa only [uIoc_of_le (by norm_num : (0 : ℝ)≤1)] using he.symm)
  rw [← unitFourierCoefficient_congr_ae he k,unitFourierCoefficient_deriv_of_ac hf hdi k,
    hp,sub_self,add_zero]

/-- The original unit Fourier integrals of every closed AC curve with a
continuous prescribed derivative belong to the actual weighted H1 space. -/
theorem memlp_sobolev_one_unitFourierCoefficient_of_ac
    (f g : ℝ → ℂ) (hf : Continuous f) (hfa : AbsolutelyContinuousOnInterval f 0 1)
    (hg : Continuous g)
    (hd : ∀ᵐ x ∂volume.restrict (Ioc (0 : ℝ) 1), HasDerivAt f (g x) x)
    (hp : f 1=f 0) :
    Memℓp (fun k : ℤ => (Weight.sobolev 1 k : ℂ)*unitFourierCoefficient f k) 2 := by
  have hfM : Memℓp (unitFourierCoefficient f) 2 := by
    rw [show unitFourierCoefficient f=intervalFourierCoefficient 1 f from
      funext (unitFourierCoefficient_eq_intervalFourierCoefficient f)]
    exact memlp_unitIntervalFourierCoefficient f hf
  have hgM : Memℓp (unitFourierCoefficient g) 2 := by
    rw [show unitFourierCoefficient g=intervalFourierCoefficient 1 g from
      funext (unitFourierCoefficient_eq_intervalFourierCoefficient g)]
    exact memlp_unitIntervalFourierCoefficient g hg
  have hm := hfM.norm.add (hgM.norm.const_mul (2*Real.pi)⁻¹)
  apply hm.mono'
  intro k
  have he := congrArg norm (unitFourierCoefficient_ac_periodic_prescribed_derivative f g hfa hg hd hp k)
  simp only [norm_mul,Complex.norm_ofNat,norm_I,mul_one,Complex.norm_real,
    Real.norm_eq_abs,abs_of_pos Real.pi_pos,Complex.norm_intCast] at he
  simp only [Pi.add_apply]
  rw [norm_mul,Complex.norm_real,Real.norm_eq_abs,Weight.sobolev_apply,Real.rpow_one,
    abs_of_pos (by positivity : 0<1+|(k : ℝ)|),Real.norm_eq_abs,
    abs_of_nonneg (by positivity : 0≤‖unitFourierCoefficient f k‖+(2*Real.pi)⁻¹*‖unitFourierCoefficient g k‖)]
  have hmul : (2*Real.pi)⁻¹*(2*Real.pi)=1 := inv_mul_cancel₀ (by positivity)
  rw [he]
  have hprod : (2*Real.pi)⁻¹*(2*Real.pi*|(k : ℝ)| *‖unitFourierCoefficient f k‖)=
      |(k : ℝ)| *‖unitFourierCoefficient f k‖ := by
    calc
      _ = ((2*Real.pi)⁻¹*(2*Real.pi))*(|(k : ℝ)| *‖unitFourierCoefficient f k‖) := by ring
      _ = _ := by rw [hmul,one_mul]
  rw [hprod]
  nlinarith

/-- Bundle the literal unit Fourier integrals, retaining their H1 weights. -/
def acPeriodicUnitCoefficients
    (f g : ℝ → ℂ) (hf : Continuous f) (hfa : AbsolutelyContinuousOnInterval f 0 1)
    (hg : Continuous g)
    (hd : ∀ᵐ x ∂volume.restrict (Ioc (0 : ℝ) 1), HasDerivAt f (g x) x)
    (hp : f 1=f 0) : WeightedCoeff (Weight.sobolev 1) 2 :=
  ⟨unitFourierCoefficient f,memlp_sobolev_one_unitFourierCoefficient_of_ac f g hf hfa hg hd hp⟩

/-- Fourier and physical Gardner pairings agree for original AC cotangents
and their prescribed continuous derivatives. All coefficients are literal
unit integrals, and the spatial factor is exactly 2*pi*k. -/
theorem gardnerBivector_eq_integral_of_ac_coefficients
    (a b : WeightedCoeff (Weight.sobolev 1) 2) (f g g1 : ℝ → ℂ)
    (hf : Continuous f) (_hg : Continuous g) (hg1 : Continuous g1)
    (hga : AbsolutelyContinuousOnInterval g 0 1)
    (hdg : ∀ᵐ x ∂volume.restrict (Ioc (0 : ℝ) 1), HasDerivAt g (g1 x) x)
    (hgp : g 1=g 0)
    (ha : ∀ k : ℤ, a.val k=unitFourierCoefficient f k)
    (hb : ∀ k : ℤ, b.val k=unitFourierCoefficient g k) :
    NLS.Poisson.gardnerBivector a b=∫ x in (0 : ℝ)..1, f x*g1 x := by
  have he := tsum_bilinear_unitFourierCoefficient hf hg1
  simp only [unitFourierCoefficient_ac_periodic_prescribed_derivative g g1 hga hg1 hdg hgp] at he
  rw [NLS.Poisson.gardnerBivector_eq_tsum,←he,
    ← (Equiv.neg ℤ).tsum_eq (fun k : ℤ => unitFourierCoefficient f (-k)*
      (2*I*(Real.pi : ℂ)*k*unitFourierCoefficient g k))]
  apply tsum_congr
  intro k
  simp only [ha,hb,Equiv.neg_apply,neg_neg,Int.cast_neg]
  ring

end NLS.Fourier
