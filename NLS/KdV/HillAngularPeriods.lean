import NLS.KdV.HillAbelianCosinePeriods
import NLS.ComplexAnalysis.RealAffineComplexPrimitive
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic

noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology
open NLS.ComplexAnalysis NLS.ZakharovShabat MeasureTheory
open scoped ENNReal ComplexConjugate

namespace NLS.KdV



variable (q : WeightedCoeff SpectralWeight.one.toWeight 2)
    (hq : SpectralWeight.one.toCoeff q ∈ Coeff.paritySubspace 0)
    (hr : IsRealHillPotential (SpectralWeight.one.toCoeff q))

theorem continuous_hillAbelianCosineDifferential_real (n : ℕ) (hn : 1 ≤ n) (k : ℕ) (hk : 1 ≤ k) :
    Continuous (fun θ : ℝ => hillAbelianCosineDifferential q hq hr n hn k (θ:ℂ)) := by
  apply continuous_iff_continuousAt.mpr
  intro θ
  exact ContinuousAt.comp (f := Complex.ofReal)
    (analyticAt_hillAbelianCosineDifferential_real q hq hr n hn k hk θ).continuousAt
    Complex.continuous_ofReal.continuousAt

theorem periodic_hillAbelianCosineDifferential_real (n : ℕ) (hn : 1 ≤ n) (k : ℕ) :
    Function.Periodic (fun θ : ℝ => hillAbelianCosineDifferential q hq hr n hn k (θ:ℂ)) (2*Real.pi) := by
  intro θ
  simp only [hillAbelianCosineDifferential,cosineGapPoint,ofReal_add,ofReal_mul,ofReal_ofNat,Complex.cos_add_two_pi]

theorem hillAbelianCosineDifferential_two_pi_sub (n : ℕ) (hn : 1 ≤ n) (k : ℕ) (θ : ℝ) :
    hillAbelianCosineDifferential q hq hr n hn k ((2*Real.pi-θ : ℝ) : ℂ) =
      hillAbelianCosineDifferential q hq hr n hn k (θ:ℂ) := by
  simp only [hillAbelianCosineDifferential,cosineGapPoint,ofReal_sub,ofReal_mul,ofReal_ofNat,Complex.cos_two_pi_sub]

theorem integral_hillAbelianCosineDifferential_two_pi (n : ℕ) (hn : 1 ≤ n) (k : ℕ) (hk : 1 ≤ k) :
    (∫ θ in (0 : ℝ)..2*Real.pi, hillAbelianCosineDifferential q hq hr n hn k (θ:ℂ)) =
      (2*(Real.pi : ℂ))*(if k=n then 1 else 0) := by
  let f : ℝ → ℂ := fun θ => hillAbelianCosineDifferential q hq hr n hn k (θ:ℂ)
  have hint (a b : ℝ) : IntervalIntegrable f volume a b :=
    (continuous_hillAbelianCosineDifferential_real q hq hr n hn k hk).intervalIntegrable a b
  have hreflect : (∫ θ in Real.pi..2*Real.pi, f θ) = ∫ θ in (0:ℝ)..Real.pi, f θ := by
    have h := intervalIntegral.integral_comp_sub_left f (2*Real.pi) (a := Real.pi) (b := 2*Real.pi)
    simpa only [f,hillAbelianCosineDifferential_two_pi_sub,sub_self,show 2*Real.pi-Real.pi = Real.pi by ring] using h
  rw [← intervalIntegral.integral_add_adjacent_intervals (hint 0 Real.pi) (hint Real.pi (2*Real.pi)),hreflect]
  change (∫ θ in (0:ℝ)..Real.pi, hillAbelianCosineDifferential q hq hr n hn k (θ:ℂ)) + _ = _
  rw [integral_hillAbelianCosineDifferential q hq hr n hn k hk]
  ring

theorem hillAbelianCosinePrimitive_real_eq_intervalIntegral (n : ℕ) (hn : 1 ≤ n) (k : ℕ) (θ : ℝ) :
    hillAbelianCosinePrimitive q hq hr n hn k (θ:ℂ) =
      ∫ t in Real.pi..θ, hillAbelianCosineDifferential q hq hr n hn k (t:ℂ) :=
  real_affine_complex_integral_eq_intervalIntegral _ Real.pi θ

theorem hillAbelianCosinePrimitive_real_add_int_period (n : ℕ) (hn : 1 ≤ n) (k : ℕ) (hk : 1 ≤ k)
    (θ : ℝ) (j : ℤ) :
    hillAbelianCosinePrimitive q hq hr n hn k ((θ+j • (2*Real.pi) : ℝ):ℂ) =
      hillAbelianCosinePrimitive q hq hr n hn k (θ:ℂ)+(j:ℂ)*(2*(Real.pi:ℂ))*(if k=n then 1 else 0) := by
  let f : ℝ → ℂ := fun t => hillAbelianCosineDifferential q hq hr n hn k (t:ℂ)
  have hint (a b : ℝ) : IntervalIntegrable f volume a b :=
    (continuous_hillAbelianCosineDifferential_real q hq hr n hn k hk).intervalIntegrable a b
  have hp : Function.Periodic f (2*Real.pi) := periodic_hillAbelianCosineDifferential_real q hq hr n hn k
  rw [hillAbelianCosinePrimitive_real_eq_intervalIntegral,hillAbelianCosinePrimitive_real_eq_intervalIntegral]
  rw [← intervalIntegral.integral_add_adjacent_intervals (hint Real.pi θ) (hint θ (θ+j • (2*Real.pi)))]
  rw [hp.intervalIntegral_add_zsmul_eq j θ hint,hp.intervalIntegral_add_eq θ 0]
  simp only [zero_add]
  change (∫ t in Real.pi..θ, f t)+j • (∫ t in (0:ℝ)..2*Real.pi,
    hillAbelianCosineDifferential q hq hr n hn k (t:ℂ)) = _
  rw [integral_hillAbelianCosineDifferential_two_pi q hq hr n hn k hk]
  simp only [f,zsmul_eq_mul,mul_assoc]

end NLS.KdV
