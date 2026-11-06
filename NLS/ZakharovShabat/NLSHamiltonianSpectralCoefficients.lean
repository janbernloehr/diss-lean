import NLS.ZakharovShabat.NLSHamiltonianSampledPhase
import NLS.ComplexAnalysis.SampledPhaseCoefficients

/-! # All smooth Hamiltonians from literal spectral coefficient limits

The recursively extracted trace coefficients equal the physical
Hamiltonians at every smooth complex periodic profile. Neither finite
gap nor convergence of the full Laurent series is assumed.
-/
noncomputable section
open Set Complex Filter Topology NLS.ComplexAnalysis
open scoped ContDiff
namespace NLS.ZakharovShabat

theorem nlsHamiltonianCorrection_succ_at_inv (a b : ℝ → ℂ) (n : ℕ) (z : ℂ) :
    nlsHamiltonianCorrection a b (n+1) z⁻¹ = nlsHamiltonianCorrection a b n z⁻¹+
      I*classicalNLSHamiltonian a b (n+1)/(2*z)^(n+1) := by
  simp only [nlsHamiltonianCorrection,Finset.sum_range_succ]
  congr 1
  simp only [mul_pow,div_eq_mul_inv,inv_pow,mul_inv_rev]
  ring

theorem nlsHamiltonianCorrection_eq_fin_sum (a b : ℝ → ℂ) (n : ℕ) (z : ℂ) :
    nlsHamiltonianCorrection a b n z⁻¹ =
      ∑ k : Fin n, I*classicalNLSHamiltonian a b (k.val+1)/(2*z)^(k.val+1) := by
  rw [Fin.sum_univ_eq_sum_range
    (fun k => I*classicalNLSHamiltonian a b (k+1)/(2*z)^(k+1)) n]
  unfold nlsHamiltonianCorrection
  apply Finset.sum_congr rfl
  intro k _
  simp only [mul_pow,div_eq_mul_inv,inv_pow,mul_inv_rev]
  ring

/-- An actual scaled limit extracts the next physical Hamiltonian
coefficient after subtraction of the preceding finite correction. -/
theorem tendsto_extracted_phase_coefficient (a b : ℝ → ℂ)
    (ha : ContDiff ℝ ∞ a) (hb : ContDiff ℝ ∞ b)
    (hpa : Function.Periodic a 1) (hpb : Function.Periodic b 1) (n : ℕ) :
    Tendsto (fun j => (2*(sampleFrequency j : ℂ))^(n+1)*
      (sampledTracePhase (fun r => classicalDiscriminant
        (classicalPotentialOfFunctions a b ha.continuous hb.continuous) r) j-
        nlsHamiltonianCorrection a b n (sampleFrequency j : ℂ)⁻¹))
      atTop (𝓝 (I*classicalNLSHamiltonian a b (n+1))) := by
  let A := sampledTracePhase (fun r => classicalDiscriminant
    (classicalPotentialOfFunctions a b ha.continuous hb.continuous) r)
  obtain ⟨C,_,hC⟩ := exists_nlsHamiltonian_extracted_phase_error a b ha hb hpa hpb (n+2)
  have herr : Tendsto (fun j => (2*(sampleFrequency j : ℂ))^(n+1)*
      (A j-nlsHamiltonianCorrection a b (n+2) (sampleFrequency j : ℂ)⁻¹)) atTop (𝓝 0) :=
    sampled_scaled_error_tendsto _ (n+1) C hC
  have hnext : Tendsto (fun j => I*classicalNLSHamiltonian a b (n+2)/(2*(sampleFrequency j : ℂ)))
      atTop (𝓝 0) := by
    have hh := sampleFrequency_inv_tendsto.const_mul (I*classicalNLSHamiltonian a b (n+2)/2)
    simp only [mul_zero] at hh
    apply hh.congr'
    apply Eventually.of_forall
    intro j
    simp only [div_eq_mul_inv,mul_inv_rev]
    ring
  have hs := (herr.add (tendsto_const_nhds (x := I*classicalNLSHamiltonian a b (n+1)))).add hnext
  simp only [zero_add,add_zero] at hs
  apply hs.congr'
  apply Eventually.of_forall
  intro j
  change (2*(sampleFrequency j : ℂ))^(n+1)*
      (A j-nlsHamiltonianCorrection a b (n+2) (sampleFrequency j : ℂ)⁻¹)+
      I*classicalNLSHamiltonian a b (n+1)+I*classicalNLSHamiltonian a b (n+2)/(2*(sampleFrequency j : ℂ)) =
    (2*(sampleFrequency j : ℂ))^(n+1)*(A j-nlsHamiltonianCorrection a b n (sampleFrequency j : ℂ)⁻¹)
  rw [show n+2 = (n+1)+1 by omega,nlsHamiltonianCorrection_succ_at_inv,
    nlsHamiltonianCorrection_succ_at_inv]
  have hz : (sampleFrequency j : ℂ) ≠ 0 := ofReal_ne_zero.mpr (sampleFrequency_pos j).ne'
  field_simp [hz]
  simp only [pow_succ]
  ring

/-- Recursive coefficient extraction uses only the actual monodromy trace.
This identifies every order on every smooth complex periodic source. -/
theorem sampledPhaseCoefficient_classicalDiscriminant (a b : ℝ → ℂ)
    (ha : ContDiff ℝ ∞ a) (hb : ContDiff ℝ ∞ b)
    (hpa : Function.Periodic a 1) (hpb : Function.Periodic b 1) (n : ℕ) :
    sampledPhaseCoefficient (fun r => classicalDiscriminant
      (classicalPotentialOfFunctions a b ha.continuous hb.continuous) r) n =
        I*classicalNLSHamiltonian a b (n+1) := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    rw [sampledPhaseCoefficient]
    have hsum (j : ℕ) :
        (∑ k : Fin n, sampledPhaseCoefficient (fun r => classicalDiscriminant
          (classicalPotentialOfFunctions a b ha.continuous hb.continuous) r) k.val/
            (2*(sampleFrequency j : ℂ))^(k.val+1)) =
          nlsHamiltonianCorrection a b n (sampleFrequency j : ℂ)⁻¹ := by
      rw [nlsHamiltonianCorrection_eq_fin_sum]
      apply Finset.sum_congr rfl
      intro k _
      rw [ih k.val k.isLt]
    simp_rw [hsum]
    exact (tendsto_extracted_phase_coefficient a b ha hb hpa hpb n).limUnder_eq

end NLS.ZakharovShabat
