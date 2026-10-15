import NLS.SequenceSpaces.PhaseRotation
import NLS.ComplexAnalysis.ScalarDuhamel
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-! # Strong derivatives of diagonal phase flows

A possibly unbounded frequency multiplier generates a norm-differentiable
orbit whenever its coefficient velocity belongs to the same finite-exponent
space. The scalar fundamental theorem and bounded coordinate evaluations
give the Banach-space integral identity and derivative.
-/
noncomputable section
open Complex MeasureTheory intervalIntegral
open scoped ENNReal
namespace NLS.Coeff
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The generator-domain condition suffices; the frequencies need not be bounded. -/
theorem hasDerivAt_phaseFlow (hp : p ≠ ⊤) (freq : ℤ → ℝ) (a v : Coeff p)
    (hv : ∀ n, v n = I * (freq n : ℂ) * a n) (t : ℝ) :
    HasDerivAt (fun r => phaseFlow freq r a) (phaseFlow freq t v) t := by
  let f : ℝ → Coeff p := fun r => phaseFlow freq r a
  let g : ℝ → Coeff p := fun r => phaseFlow freq r v
  have hg : Continuous g := (continuous_phaseFlow hp freq).comp
    (continuous_id.prodMk continuous_const)
  have hd (r : ℝ) (n : ℤ) : HasDerivAt (fun s => f s n) (g r n) r := by
    have h := (ComplexAnalysis.hasDerivAt_complex_exp_mul (I * (freq n : ℂ)) r).mul_const (a n)
    have he (s : ℝ) : I * (freq n : ℂ) * s = ((s * freq n : ℝ) : ℂ) * I := by
      push_cast
      ring
    simp_rw [he] at h
    simpa only [f, g, phaseFlow_apply, hv, mul_assoc, mul_left_comm, mul_comm] using! h
  have hint (r : ℝ) : f r = a + ∫ s in (0 : ℝ)..r, g s := by
    ext n
    let L := lp.evalCLM ℂ (fun _ : ℤ => ℂ) p n
    change L (f r) = L (a + ∫ s in (0 : ℝ)..r, g s)
    rw [map_add, ← L.intervalIntegral_comp_comm (hg.intervalIntegrable 0 r)]
    have hi := integral_eq_sub_of_hasDerivAt (fun s _ => hd s n)
      ((L.continuous.comp hg).intervalIntegrable 0 r)
    change (f r) n = a n + ∫ s in (0 : ℝ)..r, (g s) n
    rw [hi]
    simp only [f, phaseFlow_zero]
    abel
  have h := (integral_hasDerivAt_right (hg.intervalIntegrable 0 t)
    hg.stronglyMeasurable.stronglyMeasurableAtFilter hg.continuousAt).const_add a
  simpa only [← hint] using h

end NLS.Coeff
