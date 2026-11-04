import NLS.ZakharovShabat.NLSWKBWeightedComparison
import NLS.ZakharovShabat.NLSHamiltonianDiscriminantAsymptotics
import NLS.ComplexAnalysis.UnimodularWeightedTraceError

/-! # Physical Hamiltonian trace asymptotics on the full upper half-plane

All frequency coordinates share one constant at each truncation order.
The error has exactly the free exponential growth exp(Im z), including
arbitrarily large imaginary frequency. No exterior primitive expansion
is assumed in obtaining this estimate for the actual monodromy trace.
-/

noncomputable section
open Set Complex NLS.LinearVolterra NLS.ComplexAnalysis
open scoped ContDiff
namespace NLS.ZakharovShabat

theorem exists_classicalDiscriminant_upper_hamiltonian_error_bound (a b : ℝ → ℂ)
    (ha : ContDiff ℝ ∞ a) (hb : ContDiff ℝ ∞ b)
    (hpa : Function.Periodic a 1) (hpb : Function.Periodic b 1) (N : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ z : ℂ, 1 ≤ ‖z‖ → 0 ≤ z.im →
      ‖classicalDiscriminant (classicalPotentialOfFunctions a b ha.continuous hb.continuous) z -
        2*cos (I*nlsHamiltonianPhase a b N z)‖ ≤
          C / (2 * ‖z‖) ^ N * Real.exp z.im := by
  let Φ := classicalPotentialOfFunctions a b ha.continuous hb.continuous
  obtain ⟨D, hD, herr⟩ := exists_nlsWKBVector_upper_endpoint_error_bound a b ha hb hpa hpb N
  obtain ⟨B, hB, hcarrier⟩ := exists_nlsWKBCarrier_weighted_bounds a b ha hb N
  let M := Real.exp ‖Φ‖
  refine ⟨(B + 2*M) * D * B, by dsimp [M]; positivity, ?_⟩
  intro z hz him
  let m := exp (nlsHamiltonianPhase a b N z)
  let v := -I * nlsRiccatiApproximation a b N (2*I*z)⁻¹ 0
  have hm : m = nlsWKBCarrier a b N z 1 := (nlsWKBCarrier_one a b ha hb N z).symm
  have hmb := hcarrier 1 ⟨zero_le_one, le_rfl⟩ z hz
  rw [← hm] at hmb
  simp only [mul_one] at hmb
  have hcol : ‖classicalSolution Φ z (0,1) 1‖ ≤ M * Real.exp z.im := by
    have h := norm_classicalSolution_le_exp_im Φ z (0,1) ⟨1, ⟨zero_le_one, le_rfl⟩⟩
    simpa only [Prod.norm_def, norm_zero, norm_one, max_eq_right zero_le_one,
      one_mul, abs_of_nonneg him, mul_one, Real.exp_add, M, mul_comm] using h
  have he := herr z hz him
  have hv : nlsWKBVector a b N z 0 = (1,v) := by simp [nlsWKBVector, v]
  change ‖classicalSolution Φ z (nlsWKBVector a b N z 0) 1 -
    m • nlsWKBVector a b N z 0‖ ≤ _ at he
  rw [hv, classicalSolution_one_snd Φ z v ⟨1, ⟨zero_le_one, le_rfl⟩⟩] at he
  have hdet := det_classicalMonodromy Φ z
  simp only [classicalMonodromy, classicalFundamentalMatrix, Matrix.det_fin_two_of] at hdet
  have ht := norm_unimodular_trace_error_le_separate_bounds
    (classicalSolution Φ z (1,0) 1).1 (classicalSolution Φ z (0,1) 1).1
    (classicalSolution Φ z (1,0) 1).2 (classicalSolution Φ z (0,1) 1).2 m v
    hdet (exp_ne_zero _) (M * Real.exp z.im) (B * Real.exp z.im)
    (B * Real.exp (-z.im)) (D / (2 * ‖z‖) ^ N * Real.exp z.im)
    (by dsimp [M]; positivity) (by positivity) (by positivity)
    ((norm_fst_le _).trans hcol) ((norm_snd_le _).trans hcol) hmb.1 hmb.2 (by
      simpa only [Prod.norm_def, Prod.fst_add, Prod.snd_add, Prod.fst_sub, Prod.snd_sub,
        Prod.smul_fst, Prod.smul_snd, smul_eq_mul, mul_one, one_mul, mul_comm] using he)
  have hphase : 2*cos (I*nlsHamiltonianPhase a b N z) = m + m⁻¹ := by
    rw [mul_comm I, cos_mul_I, two_cosh, exp_neg]
  rw [hphase]
  simp only [classicalDiscriminant, classicalMonodromy, classicalFundamentalMatrix,
    Matrix.trace_fin_two, Matrix.of_apply]
  change ‖(classicalSolution Φ z (1,0) 1).1 +
    (classicalSolution Φ z (0,1) 1).2 - (m + m⁻¹)‖ ≤ _
  apply ht.trans_eq
  rw [Real.exp_neg]
  field_simp

end NLS.ZakharovShabat
