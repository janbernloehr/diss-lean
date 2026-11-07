import NLS.KdV.PseudomeasureMultiplication
import NLS.KdV.SingularHillPhysical

/-! # Global endpoint regularity of the physical inhomogeneous Hill equation

This is the regularity assertion of Appendix C, Lemma C.2, at every complex
spectral parameter. It has no tail cutoff or spectral strip hypothesis.
-/
noncomputable section
open scoped ENNReal
namespace NLS.KdV
open NLS.Fourier NLS.Fourier.SmoothPeriodicTest NLS.Fourier.PeriodicFourierLebesgue

/-- A Hill second moment recovers two derivatives in every signed spectral
weight and every Banach exponent, including infinity. -/
theorem memlp_endpoint_gain_two_of_hillMoment {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (w : SpectralWeight) (r : ℝ) (a : WeightedCoeff (w.negativeSobolev r) p)
    (hm : Memℓp (fun k => (w.negativeSobolev r k:ℂ)*(freeHillValue k:ℂ)*a.val k) p) :
    Memℓp (fun k => (w.negativeSobolev (r-2) k:ℂ)*a.val k) p := by
  apply ((a.property.norm.add hm.norm).const_mul (2:ℝ)).mono
  intro k
  have hv : 0 ≤ freeHillValue k := by unfold freeHillValue; positivity
  change ‖(w.negativeSobolev (r-2) k:ℂ)*a.val k‖ ≤
    (2:ℝ)*(‖(w.negativeSobolev r k:ℂ)*a.val k‖ +
      ‖(w.negativeSobolev r k:ℂ)*(freeHillValue k:ℂ)*a.val k‖)
  simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos ((w.negativeSobolev (r-2)).positive k),
    abs_of_pos ((w.negativeSobolev r).positive k), abs_of_nonneg hv]
  rw [w.negativeSobolev_sub r 2 k]
  have h := mul_le_mul_of_nonneg_left (sobolev_two_le_freeHillValue k)
    (mul_nonneg ((w.negativeSobolev r).positive k).le (norm_nonneg (a.val k)))
  nlinarith

/-- Every H1 input is already an endpoint datum of order -r, for r>=0. -/
def H1EndpointInclusion (r : ℝ) (hr : 0 ≤ r) :
    FourierLebesgueSpace (2:ℝ) 1 2 →L[ℂ] WeightedCoeff (SpectralWeight.one.negativeSobolev r) ⊤ :=
  (WeightedCoeff.inclusionCLM _ _ (fun k => by
    simpa only [SpectralWeight.negativeSobolev_eq_product, SpectralWeight.one_apply, one_mul] using
      Weight.sobolev_mono (by linarith : -r ≤ 1) k)).comp
    ((WeightedCoeff.exponentInclusion _ (by simp : (2:ℝ≥0∞) ≤ ⊤)).comp
      (sobolevCoefficients 1 2).toContinuousLinearEquiv.toContinuousLinearMap)

@[simp] theorem H1EndpointInclusion_apply (r : ℝ) (hr : 0 ≤ r)
    (f : FourierLebesgueSpace (2:ℝ) 1 2) (k : ℤ) :
    (H1EndpointInclusion r hr f).val k = f.val (mode (-k)) := by
  simp only [H1EndpointInclusion, ContinuousLinearMap.comp_apply, WeightedCoeff.inclusionCLM_apply,
    WeightedCoeff.exponentInclusion_apply]
  rfl

/-- Appendix C.2's full regularity conclusion, without restricting lambda or
assuming an improved regularity class for the physical solution. -/
theorem singularHill_inhomogeneous_memlp (r : ℝ) (hr : 0 ≤ r) (hr1 : r < 1/2)
    (q g : WeightedCoeff (SpectralWeight.one.negativeSobolev r) ⊤)
    (z : ℂ) (f : FourierLebesgueSpace (2:ℝ) 1 2)
    (hf : singularHillOperator (endpointHillHminusOne SpectralWeight.one r hr1 q) f -
      z • singularHillDomainInclusion f = endpointHillHminusOne SpectralWeight.one r hr1 g) :
    Memℓp (fun k => (SpectralWeight.one.negativeSobolev (r-2) k:ℂ)*f.val (mode (-k))) ⊤ := by
  let a := H1EndpointInclusion r hr f
  let b := g + z • a - endpointH1Multiplication r hr hr1 q f
  have hb (k : ℤ) : (freeHillValue k:ℂ)*a.val k = b.val k := by
    have he := congrArg (fun u : FourierLebesgueSpace (2:ℝ) (-1) 2 => u.val (mode (-k))) hf
    change (singularHillOperator (endpointHillHminusOne SpectralWeight.one r hr1 q) f).val (mode (-k)) -
      z*(singularHillDomainInclusion f).val (mode (-k)) =
        (endpointHillHminusOne SpectralWeight.one r hr1 g).val (mode (-k)) at he
    rw [singularHillOperator_coefficient, singularHillDomainInclusion_coefficient,
      endpointHillHminusOne_coefficient] at he
    simp only [endpointHillHminusOne_coefficient] at he
    dsimp only [b]
    simp only [WeightedCoeff.add_val, WeightedCoeff.sub_val, WeightedCoeff.smul_val,
      endpointH1Multiplication_apply]
    simp only [a, H1EndpointInclusion_apply]
    linear_combination he
  have hm : Memℓp (fun k => (SpectralWeight.one.negativeSobolev r k:ℂ)*
      (freeHillValue k:ℂ)*a.val k) ⊤ := by
    have h := b.property
    change Memℓp (fun k => (SpectralWeight.one.negativeSobolev r k:ℂ)*b.val k) ⊤ at h
    convert h using 1
    funext k
    rw [← hb k]
    ring
  simpa only [a, H1EndpointInclusion_apply] using
    memlp_endpoint_gain_two_of_hillMoment SpectralWeight.one r a hm

/-- The improved solution as an actual endpoint datum, with unchanged raw coefficients. -/
def singularHillRegularityLift (r : ℝ) (hr : 0 ≤ r) (hr1 : r < 1/2)
    (q g : WeightedCoeff (SpectralWeight.one.negativeSobolev r) ⊤)
    (z : ℂ) (f : FourierLebesgueSpace (2:ℝ) 1 2)
    (hf : singularHillOperator (endpointHillHminusOne SpectralWeight.one r hr1 q) f -
      z • singularHillDomainInclusion f = endpointHillHminusOne SpectralWeight.one r hr1 g) :
    WeightedCoeff (SpectralWeight.one.negativeSobolev (r-2)) ⊤ :=
  ⟨fun k => f.val (mode (-k)), singularHill_inhomogeneous_memlp r hr hr1 q g z f hf⟩

/-- The regularity gain preserves the entire physical smooth-test distribution. -/
theorem singularHillRegularityLift_val (r : ℝ) (hr : 0 ≤ r) (hr1 : r < 1/2)
    (q g : WeightedCoeff (SpectralWeight.one.negativeSobolev r) ⊤)
    (z : ℂ) (f : FourierLebesgueSpace (2:ℝ) 1 2)
    (hf : singularHillOperator (endpointHillHminusOne SpectralWeight.one r hr1 q) f -
      z • singularHillDomainInclusion f = endpointHillHminusOne SpectralWeight.one r hr1 g) :
    (endpointHillDistribution SpectralWeight.one (r-2) (singularHillRegularityLift r hr hr1 q g z f hf)).val =
      f.val := by
  apply Distribution.ext_coefficients
  intro k
  rw [endpointHillDistribution_coefficient]
  rfl

end NLS.KdV
