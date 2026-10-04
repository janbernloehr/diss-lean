import NLS.ZakharovShabat.ClassicalResidualStability
import NLS.ZakharovShabat.NLSWKBCarrierBounds

/-! # All-order comparison with the actual fundamental solution

The finite Hamiltonian approximation and the true initial-value solution
with the same initial vector differ by the expected inverse-frequency
order, uniformly on the physical period along the real spectral axis.
-/
noncomputable section
open Set Complex MeasureTheory NLS.LinearVolterra NLS.ComplexAnalysis
open scoped ContDiff
namespace NLS.ZakharovShabat

/-- Restrict a pair of continuous physical potentials to one period. -/
def classicalPotentialOfFunctions (a b : ℝ → ℂ) (ha : Continuous a) (hb : Continuous b) : Curve (ℂ × ℂ) :=
  ⟨fun t => (a t,b t),(ha.comp continuous_subtype_val).prodMk (hb.comp continuous_subtype_val)⟩

@[simp] theorem classicalPotentialOfFunctions_apply (a b : ℝ → ℂ)
    (ha : Continuous a) (hb : Continuous b) (t : Icc (0 : ℝ) 1) :
    classicalPotentialOfFunctions a b ha hb t = (a t,b t) := rfl

/-- Every truncation order gives an actual, uniform initial-value solution
error of that order. The true solution has the approximation's initial vector. -/
theorem exists_nlsWKBVector_solution_error_bound (a b : ℝ → ℂ)
    (ha : ContDiff ℝ ∞ a) (hb : ContDiff ℝ ∞ b) (N : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ r : ℝ, 1 ≤ |r| → ∀ t : Icc (0 : ℝ) 1,
      ‖nlsWKBVector a b N r t -
        classicalSolution (classicalPotentialOfFunctions a b ha.continuous hb.continuous) r
          (nlsWKBVector a b N r 0) t‖ ≤ C/(2*|r|)^N := by
  let Φ := classicalPotentialOfFunctions a b ha.continuous hb.continuous
  obtain ⟨D,hD,hres⟩ := exists_nlsWKBVector_residual_bound a b ha hb N
  obtain ⟨B,hB,hcarrier⟩ := exists_nlsWKBCarrier_real_bounds a b ha hb N
  refine ⟨4*(Real.exp ‖Φ‖)^2*(D*B),by positivity,?_⟩
  intro r hr t
  have hz : (r : ℂ) ≠ 0 := by
    apply ofReal_ne_zero.mpr
    exact abs_pos.mp (by linarith)
  have hu : Continuous (nlsWKBVector a b N r) :=
    (show Differentiable ℝ _ from fun x => (hasDerivAt_nlsWKBVector a b ha hb N r hz x).differentiableAt).continuous
  have hc : Continuous (nlsWKBCarrier a b N r) :=
    (show Differentiable ℝ _ from fun x => (hasDerivAt_nlsWKBCarrier a b ha hb N r x).differentiableAt).continuous
  have hq : Continuous (fun x : ℝ => (nlsRiccatiResidualPolynomial a b N).eval₂
      (Pi.evalRingHom (fun _ : ℝ => ℂ) x) (2*I*(r : ℂ))⁻¹) :=
    (continuous_polynomial_function_eval _ (continuous_coeff_nlsRiccatiResidualPolynomial a b ha hb N)).comp
      (continuous_id.prodMk continuous_const)
  let f : ℝ → ℂ × ℂ := fun x => (0,I*(nlsRiccatiResidualPolynomial a b N).eval₂
    (Pi.evalRingHom (fun _ : ℝ => ℂ) x) (2*I*(r : ℂ))⁻¹*nlsWKBCarrier a b N r x)
  have hf : Continuous f := continuous_const.prodMk ((continuous_const.mul hq).mul hc)
  let g : Curve (ℂ × ℂ) := ⟨fun s => f s,hf.comp continuous_subtype_val⟩
  have hd (s : Icc (0 : ℝ) 1) : HasDerivAt (nlsWKBVector a b N r)
      (classicalODECoefficient (Φ s) r (nlsWKBVector a b N r s)+g s) s :=
    hasDerivAt_nlsWKBVector a b ha hb N r hz s
  have hg (s : Icc (0 : ℝ) 1) : ‖g s‖ ≤ (D*B)/(2*|r|)^N := by
    have h := hres s s.property (r : ℂ) (by simpa only [Complex.norm_real,Real.norm_eq_abs] using hr)
    rw [(hd s).deriv] at h
    simp only [Φ,classicalPotentialOfFunctions_apply,add_sub_cancel_left] at h
    simp only [Complex.norm_real,Real.norm_eq_abs] at h
    exact h.trans ((mul_le_mul_of_nonneg_left (hcarrier s s.property r hr).1 (by positivity)).trans_eq (by ring))
  have h := norm_sub_classicalSolution_real_le_of_residual Φ g r _ hu hd ((D*B)/(2*|r|)^N) (by positivity) hg t
  exact h.trans_eq (by ring)

/-- The exact monodromy initial-value map has a Hamiltonian approximate
eigenvector to every order, for periodic smooth potentials. -/
theorem exists_nlsWKBVector_endpoint_error_bound (a b : ℝ → ℂ)
    (ha : ContDiff ℝ ∞ a) (hb : ContDiff ℝ ∞ b)
    (hpa : Function.Periodic a 1) (hpb : Function.Periodic b 1) (N : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ r : ℝ, 1 ≤ |r| →
      ‖classicalSolution (classicalPotentialOfFunctions a b ha.continuous hb.continuous) r
          (nlsWKBVector a b N r 0) 1 -
        exp (-I*r+∑ k ∈ Finset.range N, I*classicalNLSHamiltonian a b (k+1)/(2*r)^(k+1)) •
          nlsWKBVector a b N r 0‖ ≤ C/(2*|r|)^N := by
  obtain ⟨C,hC,hbound⟩ := exists_nlsWKBVector_solution_error_bound a b ha hb N
  refine ⟨C,hC,?_⟩
  intro r hr
  have h := hbound r hr ⟨1,⟨zero_le_one,le_rfl⟩⟩
  rw [norm_sub_rev,nlsWKBVector_one a b ha hb hpa hpb] at h
  exact h

end NLS.ZakharovShabat
