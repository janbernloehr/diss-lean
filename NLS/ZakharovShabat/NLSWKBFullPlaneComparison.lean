import NLS.ZakharovShabat.ClassicalWeightedResidualStability
import NLS.ZakharovShabat.NLSWKBCarrierWeightedBounds
import NLS.ZakharovShabat.NLSWKBComparison

/-! # All-order WKB error with its natural exponential growth

The constant is independent of frequency on the whole complex plane.
The error retains exp(abs(Im(z))*t), allowing both signed WKB columns.
-/

noncomputable section
open Set Complex MeasureTheory NLS.LinearVolterra NLS.ComplexAnalysis
open scoped ContDiff
namespace NLS.ZakharovShabat

theorem exists_nlsWKBVector_full_plane_solution_error_bound (a b : ℝ → ℂ)
    (ha : ContDiff ℝ ∞ a) (hb : ContDiff ℝ ∞ b) (N : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ z : ℂ, 1 ≤ ‖z‖ → ∀ t : Icc (0 : ℝ) 1,
      ‖nlsWKBVector a b N z t -
        classicalSolution (classicalPotentialOfFunctions a b ha.continuous hb.continuous) z
          (nlsWKBVector a b N z 0) t‖ ≤
        C / (2 * ‖z‖) ^ N * Real.exp (|z.im| * t.val) := by
  let Φ := classicalPotentialOfFunctions a b ha.continuous hb.continuous
  obtain ⟨D, hD, hres⟩ := exists_nlsWKBVector_residual_bound a b ha hb N
  obtain ⟨B, hB, hcarrier⟩ := exists_nlsWKBCarrier_weighted_bounds a b ha hb N
  refine ⟨D * B * Real.exp ‖Φ‖, by positivity, ?_⟩
  intro z hz t
  have hz0 : z ≠ 0 := norm_pos_iff.mp (by linarith)
  let U := nlsWKBVector a b N z
  let V := classicalSolution Φ z (U 0)
  have hU : Continuous U :=
    (show Differentiable ℝ _ from fun x =>
      (hasDerivAt_nlsWKBVector a b ha hb N z hz0 x).differentiableAt).continuous
  have hV : Continuous V := continuous_classicalSolution Φ z (U 0)
  have hc : Continuous (nlsWKBCarrier a b N z) :=
    (show Differentiable ℝ _ from fun x =>
      (hasDerivAt_nlsWKBCarrier a b ha hb N z x).differentiableAt).continuous
  have hq : Continuous (fun x : ℝ => (nlsRiccatiResidualPolynomial a b N).eval₂
      (Pi.evalRingHom (fun _ : ℝ => ℂ) x) (2*I*z)⁻¹) :=
    (continuous_polynomial_function_eval _ (continuous_coeff_nlsRiccatiResidualPolynomial a b ha hb N)).comp
      (continuous_id.prodMk continuous_const)
  let f : ℝ → ℂ × ℂ := fun x => (0, I * (nlsRiccatiResidualPolynomial a b N).eval₂
    (Pi.evalRingHom (fun _ : ℝ => ℂ) x) (2*I*z)⁻¹ * nlsWKBCarrier a b N z x)
  have hf : Continuous f := continuous_const.prodMk ((continuous_const.mul hq).mul hc)
  let g : Curve (ℂ × ℂ) := ⟨fun s => f s, hf.comp continuous_subtype_val⟩
  have hdu (s : Icc (0 : ℝ) 1) :
      HasDerivAt U (classicalODECoefficient (Φ s) z (U s) + g s) s :=
    hasDerivAt_nlsWKBVector a b ha hb N z hz0 s
  have hd (s : Icc (0 : ℝ) 1) : HasDerivAt (fun x => U x - V x)
      (classicalODECoefficient (Φ s) z (U s - V s) + g s) s := by
    convert! (hdu s).sub (hasDerivAt_classicalSolution Φ z (U 0) s) using 1
    simp only [map_sub]
    abel
  have hg (s : Icc (0 : ℝ) 1) :
      ‖g s‖ ≤ (D * B / (2 * ‖z‖) ^ N) * Real.exp (|z.im| * s.val) := by
    have h := hres s s.property z hz
    rw [(hdu s).deriv] at h
    simp only [Φ, classicalPotentialOfFunctions_apply, U, add_sub_cancel_left] at h
    have hh := mul_le_mul_of_nonneg_left (hcarrier s s.property z hz).1
      (show 0 ≤ D / (2 * ‖z‖) ^ N by positivity)
    calc
      ‖g s‖ ≤ D / (2 * ‖z‖) ^ N * ‖nlsWKBCarrier a b N z s‖ := h
      _ ≤ D / (2 * ‖z‖) ^ N * (B * Real.exp (z.im * s.val)) := hh
      _ ≤ _ := by
        have he : Real.exp (z.im*s.val)≤Real.exp (|z.im| * s.val) :=
          Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right (le_abs_self _) s.property.1)
        have hh := mul_le_mul_of_nonneg_left he (show 0≤D*B/(2*‖z‖)^N by positivity)
        exact (show D/(2*‖z‖)^N*(B*Real.exp (z.im*s.val)) =
          (D*B/(2*‖z‖)^N)*Real.exp (z.im*s.val) by ring) ▸ hh
  have h := norm_zero_initial_forced_le_exp_weight Φ g z (fun x => U x - V x)
    (hU.sub hV) (by simp [V]) hd (D * B / (2 * ‖z‖) ^ N) (by positivity) hg t
  exact h.trans_eq (by dsimp [U, V, Φ]; ring)

theorem exists_nlsWKBVector_full_plane_endpoint_error_bound (a b : ℝ → ℂ)
    (ha : ContDiff ℝ ∞ a) (hb : ContDiff ℝ ∞ b)
    (hpa : Function.Periodic a 1) (hpb : Function.Periodic b 1) (N : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ z : ℂ, 1 ≤ ‖z‖ →
      ‖classicalSolution (classicalPotentialOfFunctions a b ha.continuous hb.continuous) z
          (nlsWKBVector a b N z 0) 1 -
        exp (-I*z + ∑ k ∈ Finset.range N,
          I * classicalNLSHamiltonian a b (k+1) / (2*z)^(k+1)) •
          nlsWKBVector a b N z 0‖ ≤ C / (2 * ‖z‖) ^ N * Real.exp |z.im| := by
  obtain ⟨C, hC, hbound⟩ := exists_nlsWKBVector_full_plane_solution_error_bound a b ha hb N
  refine ⟨C, hC, ?_⟩
  intro z hz
  have h := hbound z hz ⟨1, ⟨zero_le_one, le_rfl⟩⟩
  rw [norm_sub_rev, nlsWKBVector_one a b ha hb hpa hpb] at h
  simpa only [mul_one] using h

end NLS.ZakharovShabat
