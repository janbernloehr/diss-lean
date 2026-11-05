import NLS.KdV.HillMiuraL2Discriminant
import NLS.ZakharovShabat.ClassicalDiagonalZeroTrace
import NLS.ZakharovShabat.SourceAntiDiscriminantIdentity
import NLS.Fourier.PeriodOneTrigPairing

/-! The actual diagonal L² Dirac trace at zero is twice the hyperbolic
cosine of the raw zero Fourier coefficient. Finite physical monodromy and
continuity in the original Hilbert coefficient norm determine the formula. -/
noncomputable section
set_option autoImplicit false
open Set Complex NLS.ZakharovShabat NLS.Fourier
open scoped ENNReal
namespace NLS.KdV

theorem hillMiuraDiagonal_ofFinsupp (a : ℤ →₀ ℂ) :
    hillMiuraDiagonal (Coeff.ofFinsupp a) = CoeffPair.ofFinsupp (a,a) := by
  apply (CoeffPair.toMax 2).injective
  apply Prod.ext
  · ext k
    change (hillMiuraDiagonal (Coeff.ofFinsupp a)).fst k = _
    rw [hillMiuraDiagonal_fst]
    rfl
  · ext k
    change (hillMiuraDiagonal (Coeff.ofFinsupp a)).snd k = _
    rw [hillMiuraDiagonal_snd]
    rfl

theorem hillMiuraFrequencyTrace_zero_ofFinsupp (a : ℤ →₀ ℂ) :
    hillMiuraFrequencyTrace (Coeff.ofFinsupp a) 0 = 2*cosh (a 0) := by
  rw [hillMiuraFrequencyTrace,hillMiuraDiagonal_ofFinsupp,
    canonicalDiscriminant_finite_eq_classical]
  rw [classicalDiscriminant_diagonal_zero (finiteSourceCurve (a,a))
    (polynomial a) (continuous_polynomial a) (fun _ => rfl)]
  have hm : (∫ s in (0:ℝ)..1, polynomial a s) = a 0 := by
    rw [← periodOneSynthesis_ofFinsupp]
    exact integral_periodOneSynthesis (Coeff.ofFinsupp a)
  rw [hm]

/-- No real-type or mean-zero assumption is needed for the exact formula. -/
theorem hillMiuraFrequencyTrace_zero (u : Coeff 2) :
    hillMiuraFrequencyTrace u 0 = 2*cosh (u 0) := by
  have hL : Continuous (fun a : Coeff 2 => hillMiuraFrequencyTrace a 0) := by
    have hc : Continuous (fun p : ℂ × Coeff 2 => hillMiuraFrequencyTrace p.2 p.1) :=
      analyticOnNhd_hillMiuraFrequencyTrace_joint.continuous
    have hm : Continuous (fun a : Coeff 2 => ((0:ℂ),a)) :=
      continuous_const.prodMk continuous_id
    simpa only [Function.comp_def] using hc.comp hm
  have hR : Continuous (fun a : Coeff 2 => 2*cosh (a 0)) :=
    continuous_const.mul (Complex.continuous_cosh.comp
      (lp.evalCLM ℂ (fun _ : ℤ => ℂ) 2 0).continuous)
  have he := (Coeff.denseRange_ofFinsupp (p := 2) (by simp)).equalizer hL hR (by
    funext a
    change hillMiuraFrequencyTrace (Coeff.ofFinsupp a) 0 =
      2*cosh ((Coeff.ofFinsupp (p := 2) a) 0)
    exact hillMiuraFrequencyTrace_zero_ofFinsupp a)
  exact congrFun he u

theorem hillMiuraL2Discriminant_zero (u : Coeff 2) :
    hillMiuraL2Discriminant u 0 = 2*cosh (u 0) := by
  rw [hillMiuraL2Discriminant,Complex.sqrt_zero,hillMiuraFrequencyTrace_zero]

end NLS.KdV
