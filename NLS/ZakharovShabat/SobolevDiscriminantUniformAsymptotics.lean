import NLS.ZakharovShabat.SobolevWKBUniformEndpoint
import NLS.ZakharovShabat.NLSHamiltonianDiscriminantAsymptotics

/-! # Uniform Sobolev discriminant asymptotics

The actual discriminant differs from its Hamiltonian phase approximation by C/(2 norm(z))^N uniformly on Hs balls and horizontal strips, for smooth periodic representatives and N <= s. Sharp sampled Fourier remainders are not asserted.
-/

noncomputable section
open Set Complex NLS.LinearVolterra NLS.ComplexAnalysis
open scoped ContDiff
namespace NLS.ZakharovShabat

/-- The actual discriminant has a Hamiltonian approximation uniform on an
original Hs ball and a complex spectral strip at every order N <= s. -/
theorem exists_uniform_classicalDiscriminant_hamiltonian_strip_error_bound
    (s N : ℕ) (hs : 1 ≤ s) (hNs : N ≤ s) (R : ℝ) (hR : 0 ≤ R) (H : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ ab : SobolevSource s, ‖ab‖ ≤ R → ∀ a b : ℝ → ℂ,
      ∀ ha : ContDiff ℝ ∞ a, ∀ hb : ContDiff ℝ ∞ b,
      Function.Periodic a 1 → Function.Periodic b 1 →
      (∀ j, ab.1.val j = NLS.Fourier.periodOneCoefficient a j) →
      (∀ j, ab.2.val j = NLS.Fourier.periodOneCoefficient b j) →
      ∀ z : ℂ, 1 ≤ ‖z‖ → |z.im| ≤ H →
        ‖classicalDiscriminant (classicalPotentialOfFunctions a b ha.continuous hb.continuous) z-
          2*cos (I*nlsHamiltonianPhase a b N z)‖ ≤ C/(2*‖z‖)^N := by
  obtain ⟨D,hD,herr⟩ := exists_uniform_nlsWKBVector_strip_endpoint_error_bound s N hs hNs R hR H
  obtain ⟨B,hB,hcarrier⟩ := exists_uniform_nlsWKBCarrier_strip_bounds s N hs hNs R hR H
  obtain ⟨A,hA,haB⟩ := exists_uniform_first_potential_pointwise_bound s hs R hR
  let M := Real.exp (A+H)
  refine ⟨(B+2*M)*D*B,by dsimp [M]; positivity,?_⟩
  intro ab hab a b ha hb hpa hpb hca hcb z hr hstrip
  let Φ := classicalPotentialOfFunctions a b ha.continuous hb.continuous
  have hΦ : ‖Φ‖ ≤ A := by
    apply (ContinuousMap.norm_le _ hA).mpr
    intro x
    change ‖(a x,b x)‖ ≤ A
    apply norm_prod_le_iff.mpr
    exact ⟨haB ab hab a b ha hb hpa hpb hca hcb x,
      haB (ab.2,ab.1) (by simpa only [Prod.norm_def,max_comm] using hab)
        b a hb ha hpb hpa hcb hca x⟩
  let m := exp (nlsHamiltonianPhase a b N z)
  let v := -I*nlsRiccatiApproximation a b N (2*I*z)⁻¹ 0
  have hm : m = nlsWKBCarrier a b N z 1 := (nlsWKBCarrier_one a b ha hb N z).symm
  have hmb := (hcarrier ab hab a b ha hb hpa hpb hca hcb 1 ⟨zero_le_one,le_rfl⟩ z hr hstrip)
  rw [← hm] at hmb
  have hcol : ‖classicalSolution Φ z (0,1) 1‖ ≤ M := by
    exact norm_classicalSolution_unit_strip_le A H Φ hΦ z hstrip
      (0,1) (by simp) ⟨1,⟨zero_le_one,le_rfl⟩⟩
  have he := herr ab hab a b ha hb hpa hpb hca hcb z hr hstrip
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
