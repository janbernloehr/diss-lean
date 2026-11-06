import NLS.KdV.HillOriginalMassDivergence
import NLS.KdV.HillL2SquareCircleAsymptotics
import NLS.KdV.HillContinuousPotentialMass
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic

/-! # The actual physical quadratic invariant at rough source limits

Parseval and unit periodicity identify the classical quadratic invariant
with one half of the ORIGINAL period-two Fourier L2 norm. Consequently
every real continuous physical approximation of a non-L2 rough datum has
diverging actual H_0, without any local spectral chart hypothesis.
-/

noncomputable section
set_option autoImplicit false
open Set Filter Topology MeasureTheory
open NLS.Fourier
namespace NLS.KdV

/-- Exact unit-period normalization of the original physical Fourier norm. -/
theorem norm_sq_hillContinuousCoefficients_eq_integral_norm_sq
    (Q : C(AddCircle (2 : ℝ), ℂ))
    (hp : Function.Periodic (fun x : ℝ => Q (x : AddCircle (2 : ℝ))) 1) :
    ‖hillContinuousCoefficients Q‖^2=
      ∫ x in (0 : ℝ)..1, ‖Q (x : AddCircle (2 : ℝ))‖^2 := by
  let f : ℝ → ℂ := fun x => Q (x : AddCircle (2 : ℝ))
  have hf : Continuous f := Q.continuous.comp (by fun_prop)
  have hm := memLp_two_interval hf 0 2 (by norm_num)
  have heq : periodTwoL2Coefficients f hm=
      SpectralWeight.one.toCoeff (hillContinuousCoefficients Q) := by
    ext k
    rw [periodTwoL2Coefficients_apply, SpectralWeight.toCoeff_apply,
      hillContinuousCoefficients_apply]
    exact periodTwoCoefficient_circle Q k
  have hn : ‖SpectralWeight.one.toCoeff (hillContinuousCoefficients Q)‖=
      ‖hillContinuousCoefficients Q‖ := by
    have he : SpectralWeight.one.toCoeff (hillContinuousCoefficients Q)=
        WeightedCoeff.weightEquiv SpectralWeight.one.toWeight 2 (hillContinuousCoefficients Q) := by
      ext k
      simp only [SpectralWeight.toCoeff_apply, WeightedCoeff.weightEquiv_apply,
        SpectralWeight.one_apply, Complex.ofReal_one, one_mul]
    rw [he]
    rfl
  have hper : Function.Periodic (fun x => ‖f x‖^2) 1 := by
    intro x
    exact congrArg (fun z : ℂ => ‖z‖^2) (hp x)
  have hdouble := hper.intervalIntegral_add_zsmul_eq (2 : ℤ) 0
    (fun a b => (hf.norm.pow 2).intervalIntegrable a b)
  have he := norm_sq_periodTwoL2Coefficients f hm
  rw [heq, hn] at he
  have hd : (∫ x in (0 : ℝ)..2, ‖f x‖^2)=
      2*(∫ x in (0 : ℝ)..1, ‖f x‖^2) := by
    simpa only [zsmul_eq_mul, Int.cast_ofNat, zero_add, mul_one] using hdouble
  rw [hd] at he
  dsimp only [f] at he
  linarith

/-- The actual real H_0 is one half of the ORIGINAL physical squared norm. -/
theorem classicalQuadraticInvariant_re_eq_half_hillContinuousCoefficients_norm_sq
    (Q : C(AddCircle (2 : ℝ), ℂ))
    (hr : ∀ x : AddCircle (2 : ℝ), (Q x).im=0)
    (hp : Function.Periodic (fun x : ℝ => Q (x : AddCircle (2 : ℝ))) 1) :
    (classicalQuadraticInvariant (fun x : ℝ => Q (x : AddCircle (2 : ℝ)))).re=
      (1/2 : ℝ)*‖hillContinuousCoefficients Q‖^2 := by
  rw [classicalQuadraticInvariant_re_eq_half_integral_norm_sq _ (fun x => hr _),
    norm_sq_hillContinuousCoefficients_eq_integral_norm_sq Q hp]

/-- EVERY original real continuous physical approximation of a genuinely
non-L2 rough source has diverging actual classical quadratic invariant. -/
theorem tendsto_classicalQuadraticInvariant_re_atTop_of_nonL2_hminus_limit
    {ι : Type*} {l : Filter ι} (q : PeriodOneHminusOne) (hq : ¬ Memℓp q.val 2)
    (Q : ι → C(AddCircle (2 : ℝ), ℂ))
    (hr : ∀ i x, (Q i x).im=0)
    (hp : ∀ i, Function.Periodic (fun x : ℝ => Q i (x : AddCircle (2 : ℝ))) 1)
    (ht : Tendsto (fun i => hillOriginalHminusSource (hillContinuousCoefficients (Q i)))
      l (𝓝 q)) :
    Tendsto (fun i => (classicalQuadraticInvariant
      (fun x : ℝ => Q i (x : AddCircle (2 : ℝ)))).re) l atTop := by
  simp_rw [classicalQuadraticInvariant_re_eq_half_hillContinuousCoefficients_norm_sq
    _ (hr _) (hp _)]
  exact tendsto_original_half_L2_norm_sq_atTop_of_nonL2_hminus_limit q hq _ ht

end NLS.KdV
