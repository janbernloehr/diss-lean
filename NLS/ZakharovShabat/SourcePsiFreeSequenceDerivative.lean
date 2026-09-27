import NLS.ZakharovShabat.SourcePsiFreeQuotientContinuity
import NLS.ZakharovShabat.SourcePsiFreeOperator

/-!
# Fréchet derivative of the sequence-valued free psi equation

The free-source contour equation factors as `2a` plus a remainder
bounded by `2‖a‖‖Q(a)-1‖ₚ`. Continuity of the quotient-error sequence
at zero makes that remainder little-o of `‖a‖`, so the actual
sequence-valued map has the same derivative as its scalar rows.
-/

noncomputable section
open Set Metric Complex Filter Topology
open scoped ENNReal
namespace NLS.ZakharovShabat

/-- The free-source psi equation is Fréchet differentiable as a map
between deleted-coordinate `ℓᵖ` spaces, with derivative `2 · id`. -/
theorem hasFDerivAt_sourcePsiFreeEquationSequence_zero
    {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (hp : p ≠ ⊤) (hp1 : 1 < p) (n : ℤ)
    (R : ℝ) (hR : 0 < R) (hRquarter : R ≤ Real.pi/4) :
    HasFDerivAt
      (sourcePsiFreeEquationSequence hp hp1 n R hR hRquarter)
      (sourcePsiFreeJacobianOperator n)
      (0 : DeletedCoeff p n) := by
  let E : DeletedCoeff p n → Coeff p := fun a =>
    sourcePsiFreeQuotientError hp hp1 (a : Coeff p)
  have hE : ContinuousAt E 0 := by
    have hsub : ContinuousAt (fun a : DeletedCoeff p n => (a : Coeff p)) 0 :=
      ((lp.evalCLM ℂ (fun _ : ℤ => ℂ) p n).ker.subtypeL).continuous.continuousAt
    simpa only [E, Function.comp_def] using
      (continuousAt_sourcePsiFreeQuotientError_zero hp hp1).comp
        (f := fun a : DeletedCoeff p n => (a : Coeff p)) hsub
  have hEzero : E 0 = 0 := by simp [E]
  have hupper : Tendsto (fun a : DeletedCoeff p n => 2*‖E a‖)
      (𝓝 0) (𝓝 0) := by
    have hc : ContinuousAt (fun a : DeletedCoeff p n => 2*‖E a‖) 0 :=
      continuousAt_const.mul hE.norm
    simpa [hEzero] using hc.tendsto
  apply (hasFDerivAt_iff_tendsto).2
  apply squeeze_zero (fun a => by positivity) ?_ hupper
  intro a
  rw [sourcePsiFreeEquationSequence_zero hp hp1 n R hR hRquarter,
    sourcePsiFreeJacobianOperator_apply]
  simp only [sub_zero]
  by_cases ha : a = 0
  · subst a
    simp
  · have hanorm : ‖a‖ ≠ 0 := norm_ne_zero_iff.mpr ha
    have hrem := norm_sourcePsiFreeEquationSequence_sub_linear_le
      hp hp1 n a R hR hRquarter
    calc
      ‖a‖⁻¹ * ‖sourcePsiFreeEquationSequence hp hp1 n R hR hRquarter a -
        (2 : ℂ) • a‖ ≤
          ‖a‖⁻¹ * (2*‖E a‖*‖a‖) :=
        mul_le_mul_of_nonneg_left hrem (by positivity)
      _ = 2*‖E a‖ := by
        field_simp [hanorm]

/-- The Fréchet derivative of the actual sequence-valued free psi
contour equation is the invertible diagonal operator from Lemma 12.5. -/
theorem fderiv_sourcePsiFreeEquationSequence_zero
    {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (hp : p ≠ ⊤) (hp1 : 1 < p) (n : ℤ)
    (R : ℝ) (hR : 0 < R) (hRquarter : R ≤ Real.pi/4) :
    fderiv ℂ (sourcePsiFreeEquationSequence hp hp1 n R hR hRquarter)
      (0 : DeletedCoeff p n) = sourcePsiFreeJacobianOperator n :=
  (hasFDerivAt_sourcePsiFreeEquationSequence_zero
    hp hp1 n R hR hRquarter).fderiv

end NLS.ZakharovShabat
