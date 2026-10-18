import NLS.ZakharovShabat.ClassicalStripResidualStability
import NLS.ZakharovShabat.NLSWKBCarrierStripBounds
import NLS.ZakharovShabat.NLSWKBComparison

/-! # WKB comparison on complex spectral strips

Every smooth truncation order controls the actual initial-value solution and, for periodic potentials, its monodromy endpoint.
-/

noncomputable section
open Set Complex MeasureTheory NLS.LinearVolterra NLS.ComplexAnalysis
open scoped ContDiff
namespace NLS.ZakharovShabat

/-- Every truncation order gives an actual, uniform initial-value solution
error of that order. The true solution has the approximation's initial vector. -/
theorem exists_nlsWKBVector_strip_solution_error_bound (a b : ℝ → ℂ)
    (ha : ContDiff ℝ ∞ a) (hb : ContDiff ℝ ∞ b) (N : ℕ) (H : ℝ) :
    ∃ C : ℝ, 0 < C ∧ ∀ z : ℂ, 1 ≤ ‖z‖ → |z.im| ≤ H → ∀ t : Icc (0 : ℝ) 1,
      ‖nlsWKBVector a b N z t -
        classicalSolution (classicalPotentialOfFunctions a b ha.continuous hb.continuous) z
          (nlsWKBVector a b N z 0) t‖ ≤ C/(2*‖z‖)^N := by
  let Φ := classicalPotentialOfFunctions a b ha.continuous hb.continuous
  obtain ⟨D,hD,hres⟩ := exists_nlsWKBVector_residual_bound a b ha hb N
  obtain ⟨B,hB,hcarrier⟩ := exists_nlsWKBCarrier_strip_bounds a b ha hb N H
  refine ⟨4*(Real.exp (‖Φ‖+H))^2*(D*B),by positivity,?_⟩
  intro z hr hstrip t
  have hz : z ≠ 0 := norm_pos_iff.mp (by linarith)
  have hu : Continuous (nlsWKBVector a b N z) :=
    (show Differentiable ℝ _ from fun x => (hasDerivAt_nlsWKBVector a b ha hb N z hz x).differentiableAt).continuous
  have hc : Continuous (nlsWKBCarrier a b N z) :=
    (show Differentiable ℝ _ from fun x => (hasDerivAt_nlsWKBCarrier a b ha hb N z x).differentiableAt).continuous
  have hq : Continuous (fun x : ℝ => (nlsRiccatiResidualPolynomial a b N).eval₂
      (Pi.evalRingHom (fun _ : ℝ => ℂ) x) (2*I*z)⁻¹) :=
    (continuous_polynomial_function_eval _ (continuous_coeff_nlsRiccatiResidualPolynomial a b ha hb N)).comp
      (continuous_id.prodMk continuous_const)
  let f : ℝ → ℂ × ℂ := fun x => (0,I*(nlsRiccatiResidualPolynomial a b N).eval₂
    (Pi.evalRingHom (fun _ : ℝ => ℂ) x) (2*I*z)⁻¹*nlsWKBCarrier a b N z x)
  have hf : Continuous f := continuous_const.prodMk ((continuous_const.mul hq).mul hc)
  let g : Curve (ℂ × ℂ) := ⟨fun s => f s,hf.comp continuous_subtype_val⟩
  have hd (s : Icc (0 : ℝ) 1) : HasDerivAt (nlsWKBVector a b N z)
      (classicalODECoefficient (Φ s) z (nlsWKBVector a b N z s)+g s) s :=
    hasDerivAt_nlsWKBVector a b ha hb N z hz s
  have hg (s : Icc (0 : ℝ) 1) : ‖g s‖ ≤ (D*B)/(2*‖z‖)^N := by
    have h := hres s s.property z hr
    rw [(hd s).deriv] at h
    simp only [Φ,classicalPotentialOfFunctions_apply,add_sub_cancel_left] at h
    exact h.trans ((mul_le_mul_of_nonneg_left (hcarrier s s.property z hr hstrip).1 (by positivity)).trans_eq (by ring))
  have h := norm_sub_classicalSolution_strip_le_of_residual Φ g z H hstrip _ hu hd ((D*B)/(2*‖z‖)^N) (by positivity) hg t
  exact h.trans_eq (by ring)

/-- The exact monodromy initial-value map has a Hamiltonian approximate
eigenvector to every order, for periodic smooth potentials. -/
theorem exists_nlsWKBVector_strip_endpoint_error_bound (a b : ℝ → ℂ)
    (ha : ContDiff ℝ ∞ a) (hb : ContDiff ℝ ∞ b)
    (hpa : Function.Periodic a 1) (hpb : Function.Periodic b 1) (N : ℕ) (H : ℝ) :
    ∃ C : ℝ, 0 < C ∧ ∀ z : ℂ, 1 ≤ ‖z‖ → |z.im| ≤ H →
      ‖classicalSolution (classicalPotentialOfFunctions a b ha.continuous hb.continuous) z
          (nlsWKBVector a b N z 0) 1 -
        exp (-I*z+∑ k ∈ Finset.range N, I*classicalNLSHamiltonian a b (k+1)/(2*z)^(k+1)) •
          nlsWKBVector a b N z 0‖ ≤ C/(2*‖z‖)^N := by
  obtain ⟨C,hC,hbound⟩ := exists_nlsWKBVector_strip_solution_error_bound a b ha hb N H
  refine ⟨C,hC,?_⟩
  intro z hr hstrip
  have h := hbound z hr hstrip ⟨1,⟨zero_le_one,le_rfl⟩⟩
  rw [norm_sub_rev,nlsWKBVector_one a b ha hb hpa hpb] at h
  exact h

end NLS.ZakharovShabat
