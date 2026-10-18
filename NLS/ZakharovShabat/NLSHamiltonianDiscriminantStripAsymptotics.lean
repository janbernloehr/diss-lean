import NLS.ZakharovShabat.NLSWKBStripComparison
import NLS.ZakharovShabat.NLSHamiltonianDiscriminantAsymptotics
import NLS.ZakharovShabat.ClassicalEndpointGradientBounds

/-! # Hamiltonian discriminant asymptotics on complex strips

The actual discriminant has an all-order Hamiltonian phase approximation for fixed smooth periodic complex potentials.
-/

noncomputable section
open Set Complex NLS.LinearVolterra NLS.ComplexAnalysis
open scoped ContDiff
namespace NLS.ZakharovShabat

/-- Every smooth periodic complex potential has the all-order discriminant
asymptotics required to identify the Hamiltonian Laurent coefficients. -/
theorem exists_classicalDiscriminant_hamiltonian_strip_error_bound (a b : ℝ → ℂ)
    (ha : ContDiff ℝ ∞ a) (hb : ContDiff ℝ ∞ b)
    (hpa : Function.Periodic a 1) (hpb : Function.Periodic b 1) (N : ℕ) (H : ℝ) :
    ∃ C : ℝ, 0 < C ∧ ∀ z : ℂ, 1 ≤ ‖z‖ → |z.im| ≤ H →
      ‖classicalDiscriminant (classicalPotentialOfFunctions a b ha.continuous hb.continuous) z -
        2*cos (I*nlsHamiltonianPhase a b N z)‖ ≤ C/(2*‖z‖)^N := by
  let Φ := classicalPotentialOfFunctions a b ha.continuous hb.continuous
  obtain ⟨D,hD,herr⟩ := exists_nlsWKBVector_strip_endpoint_error_bound a b ha hb hpa hpb N H
  obtain ⟨B,hB,hcarrier⟩ := exists_nlsWKBCarrier_strip_bounds a b ha hb N H
  let M := Real.exp (‖Φ‖+H)
  refine ⟨(B+2*M)*D*B,by dsimp [M]; positivity,?_⟩
  intro z hr hstrip
  let m := exp (nlsHamiltonianPhase a b N z)
  let v := -I*nlsRiccatiApproximation a b N (2*I*z)⁻¹ 0
  have hm : m = nlsWKBCarrier a b N z 1 := (nlsWKBCarrier_one a b ha hb N z).symm
  have hmb := (hcarrier 1 ⟨zero_le_one,le_rfl⟩ z hr hstrip)
  rw [← hm] at hmb
  have hcol : ‖classicalSolution Φ z (0,1) 1‖ ≤ M := by
    exact norm_classicalSolution_unit_strip_le ‖Φ‖ H Φ le_rfl z hstrip
      (0,1) (by simp) ⟨1,⟨zero_le_one,le_rfl⟩⟩
  have he := herr z hr hstrip
  have hv : nlsWKBVector a b N z 0 = (1,v) := by simp [nlsWKBVector,v]
  change ‖classicalSolution Φ z (nlsWKBVector a b N z 0) 1-m • nlsWKBVector a b N z 0‖ ≤ _ at he
  rw [hv,classicalSolution_one_snd Φ z v ⟨1,⟨zero_le_one,le_rfl⟩⟩] at he
  have hdet := det_classicalMonodromy Φ z
  simp only [classicalMonodromy,classicalFundamentalMatrix,Matrix.det_fin_two_of] at hdet
  have ht := norm_unimodular_trace_error_le
    (classicalSolution Φ z (1,0) 1).1 (classicalSolution Φ z (0,1) 1).1
    (classicalSolution Φ z (1,0) 1).2 (classicalSolution Φ z (0,1) 1).2 m v
    hdet (exp_ne_zero _) M B (D/(2*‖z‖)^N) (Real.exp_pos _).le hB.le (by positivity)
    ((norm_fst_le _).trans hcol) ((norm_snd_le _).trans hcol) hmb.1 hmb.2 (by
      simpa only [Prod.norm_def,Prod.fst_add,Prod.snd_add,Prod.fst_sub,Prod.snd_sub,Prod.smul_fst,Prod.smul_snd,
        smul_eq_mul,mul_one,one_mul,mul_comm] using he)
  have hphase : 2*cos (I*nlsHamiltonianPhase a b N z) = m+m⁻¹ := by
    rw [mul_comm I,cos_mul_I,two_cosh,exp_neg]
  rw [hphase]
  simp only [classicalDiscriminant,classicalMonodromy,classicalFundamentalMatrix,Matrix.trace_fin_two,Matrix.of_apply]
  change ‖(classicalSolution Φ z (1,0) 1).1+(classicalSolution Φ z (0,1) 1).2-(m+m⁻¹)‖ ≤ _
  exact ht.trans_eq (by ring)

end NLS.ZakharovShabat
