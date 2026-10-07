import NLS.Fourier.LocalNLSInteraction
import NLS.ComplexAnalysis.ScalarDuhamel

/-! # Local solutions of the original Fourier NLS equation

The constructed interaction solution gives a norm-continuous weighted Fourier
curve. Every original mode satisfies the quadratic Schrödinger term plus the
actual cubic convolution, including at the endpoints as a one-sided derivative.
-/
noncomputable section
open Set Complex
namespace NLS.Fourier

/-- The linear symbol of i∂ₓ² on the period-one Fourier basis. -/
def nlsLinearSymbol (n : ℤ) : ℂ := -I*((2*Real.pi*(n : ℝ))^2 : ℝ)

@[simp] theorem nlsFreeFlow_apply (w : Weight) (time : ℝ) (a : WeightedCoeff w 1) (n : ℤ) :
    (nlsFreeFlow w time a).val n = exp (nlsLinearSymbol n * time)*a.val n := by
  rw [nlsFreeFlow,WeightedCoeff.phaseFlow_apply]
  congr 2
  simp only [nlsLinearSymbol,ofReal_mul,ofReal_neg,ofReal_pow]
  ring

/-- The nonlinear field uses literal convolution of the original coefficients. -/
theorem cubicNLS_apply (w : SpectralWeight) (a : WeightedCoeff w.toWeight 1) (n : ℤ) :
    (cubicNLS w a).val n = (-2*I : ℂ) *
      ∑' k : ℤ, (∑' j : ℤ, a.val (n-k-j)*a.val j) * (starRingEnd ℂ) (a.val (-k)) := by
  simp only [cubicNLS,WeightedCoeff.smul_val,
    SpectralWeight.convolution_apply,nlsConjugate_apply]

/-- Restoring free evolution recovers the cubic term in the original equation. -/
theorem nlsFreeFlow_nlsInteraction (w : SpectralWeight) (time : ℝ) (a : WeightedCoeff w.toWeight 1) :
    nlsFreeFlow w.toWeight time (nlsInteraction w time a) =
      cubicNLS w (nlsFreeFlow w.toWeight time a) := by
  rw [nlsInteraction,nlsFreeFlow_add,add_neg_cancel,nlsFreeFlow_zero]

/-- Transforming an interaction solution yields the original mode equations. -/
theorem hasDerivWithinAt_nlsFreeFlow_of_interaction
    (w : SpectralWeight) (v : ℝ → WeightedCoeff w.toWeight 1) (S : Set ℝ) (time : ℝ)
    (hv : HasDerivWithinAt v (nlsInteraction w time (v time)) S time) (n : ℤ) :
    HasDerivWithinAt (fun r => (nlsFreeFlow w.toWeight r (v r)).val n)
      (nlsLinearSymbol n*(nlsFreeFlow w.toWeight time (v time)).val n +
        (cubicNLS w (nlsFreeFlow w.toWeight time (v time))).val n) S time := by
  let ev : WeightedCoeff w.toWeight 1 →L[ℂ] ℂ :=
    (lp.evalCLM ℂ (fun _ : ℤ => ℂ) 1 n).comp w.toCoeff
  have hval : HasDerivWithinAt (fun r => (v r).val n) ((nlsInteraction w time (v time)).val n) S time := by
    have h := (ev.restrictScalars ℝ).hasFDerivAt.comp_hasDerivWithinAt time hv
    change HasDerivWithinAt (fun r => w.toCoeff (v r) n)
      (w.toCoeff (nlsInteraction w time (v time)) n) S time at h
    simpa only [SpectralWeight.toCoeff_apply] using h

  have hd := (NLS.ComplexAnalysis.hasDerivAt_complex_exp_mul (nlsLinearSymbol n) time).hasDerivWithinAt.mul hval
  have hc := congrArg (fun a : WeightedCoeff w.toWeight 1 => a.val n)
    (nlsFreeFlow_nlsInteraction w time (v time))
  rw [nlsFreeFlow_apply] at hc
  simp only [nlsFreeFlow_apply]
  convert! hd using 1
  rw [← hc]
  ring

/-- Local Fourier NLS existence for every weighted ℓ¹ initial datum. The
curve is continuous in that full norm and solves every original mode equation. -/
theorem exists_local_fourierNLS (w : SpectralWeight) (a : WeightedCoeff w.toWeight 1) :
    ∃ T > 0, ∃ u : ℝ → WeightedCoeff w.toWeight 1, u 0 = a ∧
      ContinuousOn u (Icc (-T) T) ∧
      ∀ time ∈ Icc (-T) T, ∀ n : ℤ,
        HasDerivWithinAt (fun r => (u r).val n)
          (nlsLinearSymbol n*(u time).val n + (cubicNLS w (u time)).val n) (Icc (-T) T) time := by
  obtain ⟨T,hT,v,hv0,hv⟩ := exists_local_nlsInteraction w a
  let u := fun time => nlsFreeFlow w.toWeight time (v time)
  have hvcont : ContinuousOn v (Icc (-T) T) := fun time ht => (hv time ht).continuousWithinAt
  have hg : ContinuousOn (fun time => (time,v time)) (Icc (-T) T) := continuousOn_id.prodMk hvcont
  have hc := (continuous_nlsFreeFlow w.toWeight).comp_continuousOn hg
  have hu : ContinuousOn u (Icc (-T) T) := by
    simpa only [Function.comp_def,u] using hc
  refine ⟨T,hT,u,?_,hu,?_⟩
  · simpa only [u,nlsFreeFlow_zero] using hv0
  · intro time ht n
    exact hasDerivWithinAt_nlsFreeFlow_of_interaction w v _ time (hv time ht) n

end NLS.Fourier
