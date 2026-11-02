import NLS.ComplexAnalysis.DiscriminantSamples
import NLS.ZakharovShabat.NLSHamiltonianPrimitiveCoefficients

/-! # Discriminant phase samples for arbitrary smooth complex profiles

There is no finite-gap assumption and no analyticity at inverse frequency
zero. A fixed local inverse extracts the actual small phase from the
physical trace. Every finite Hamiltonian correction approximates it to
the corresponding inverse-frequency order.
-/
noncomputable section
open Set Complex Filter Topology NLS.ComplexAnalysis
open scoped ContDiff
namespace NLS.ZakharovShabat

theorem classicalDiscriminant_samples_tendsto (a b : ℝ → ℂ)
    (ha : ContDiff ℝ ∞ a) (hb : ContDiff ℝ ∞ b)
    (hpa : Function.Periodic a 1) (hpb : Function.Periodic b 1) :
    Tendsto (fun j => classicalDiscriminant
      (classicalPotentialOfFunctions a b ha.continuous hb.continuous) (sampleFrequency j)) atTop (𝓝 0) := by
  let P := fun j => nlsHamiltonianCorrection a b 1 (sampleFrequency j : ℂ)⁻¹
  have hP : Tendsto P atTop (𝓝 0) := by
    simpa only [Function.comp_def,nlsHamiltonianCorrection_zero] using!
      (analyticAt_nlsHamiltonianCorrection a b 1 0).continuousAt.tendsto.comp sampleFrequency_inv_tendsto
  obtain ⟨C,_,hC⟩ := exists_classicalDiscriminant_hamiltonian_error_bound a b ha hb hpa hpb 1
  have hbound : ∀ᶠ j in atTop,
      ‖classicalDiscriminant (classicalPotentialOfFunctions a b ha.continuous hb.continuous)
        (sampleFrequency j)‖ ≤ C/(2*sampleFrequency j)+2*‖sinh (P j)‖ := by
    filter_upwards [sampleFrequency_tendsto.eventually (eventually_ge_atTop 1)] with j hj
    have he := hC (sampleFrequency j) (by rw [abs_of_pos (sampleFrequency_pos j)]; exact hj)
    have hphase : 2*cos (I*nlsHamiltonianPhase a b 1 (sampleFrequency j)) =
        2*cosh (-I*(sampleFrequency j : ℂ)+P j) := by
      rw [mul_comm I,cos_mul_I,nlsHamiltonianPhase_eq_correction]
    rw [hphase,abs_of_pos (sampleFrequency_pos j),pow_one] at he
    have hn : ‖2*cosh (-I*(sampleFrequency j : ℂ)+P j)‖ = 2*‖sinh (P j)‖ := by
      rw [cosh_add,cosh_sampleFrequency,zero_mul,zero_add]
      change ‖2*(sampleCarrier j*sinh (P j))‖ = _
      rw [norm_mul,norm_mul,norm_sampleCarrier,one_mul,norm_ofNat]
    exact (norm_le_norm_sub_add _ _).trans (add_le_add he hn.le)
  have hfirst : Tendsto (fun j => C/(2*sampleFrequency j)) atTop (𝓝 0) := by
    simpa only [div_eq_mul_inv,mul_zero] using!
      (sampleFrequency_tendsto.const_mul_atTop (by norm_num : (0:ℝ) < 2)).inv_tendsto_atTop.const_mul C
  have hsecond : Tendsto (fun j => 2*‖sinh (P j)‖) atTop (𝓝 0) := by
    simpa only [sinh_zero,norm_zero,mul_zero,Function.comp_def] using!
      ((continuous_sinh.tendsto 0).comp hP).norm.const_mul 2
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  exact squeeze_zero' (Eventually.of_forall (fun _ => norm_nonneg _)) hbound
    (by simpa using hfirst.add hsecond)

/-- The error estimate only requires a small phase sequence recovering
the actual trace, so it applies to infinite-gap profiles as well. -/
theorem exists_nlsHamiltonian_sampled_phase_sequence_error (a b : ℝ → ℂ)
    (ha : ContDiff ℝ ∞ a) (hb : ContDiff ℝ ∞ b)
    (hpa : Function.Periodic a 1) (hpb : Function.Periodic b 1)
    (A : ℕ → ℂ) (hA : Tendsto A atTop (𝓝 0))
    (he : ∀ᶠ j in atTop, 2*cosh (-I*(sampleFrequency j : ℂ)+A j) =
      classicalDiscriminant (classicalPotentialOfFunctions a b ha.continuous hb.continuous) (sampleFrequency j))
    (N : ℕ) : ∃ C : ℝ, 0 < C ∧ ∀ᶠ j in atTop,
      ‖A j-nlsHamiltonianCorrection a b N (sampleFrequency j : ℂ)⁻¹‖ ≤
        C*‖(sampleFrequency j : ℂ)⁻¹‖^N := by
  obtain ⟨ε,hε,hlocal⟩ := exists_norm_phase_sub_le_discriminant_error
  have htP : Tendsto (fun j => nlsHamiltonianCorrection a b N (sampleFrequency j : ℂ)⁻¹)
      atTop (𝓝 0) := by
    simpa only [Function.comp_def,nlsHamiltonianCorrection_zero] using!
      (analyticAt_nlsHamiltonianCorrection a b N 0).continuousAt.tendsto.comp sampleFrequency_inv_tendsto
  obtain ⟨C,hC,hbound⟩ := exists_classicalDiscriminant_hamiltonian_error_bound a b ha hb hpa hpb N
  refine ⟨C/2^N,by positivity,?_⟩
  filter_upwards [he,sampleFrequency_tendsto.eventually (eventually_ge_atTop 1),
    hA.eventually (Metric.ball_mem_nhds (0 : ℂ) hε),
    htP.eventually (Metric.ball_mem_nhds (0 : ℂ) hε)] with j hej hrj hAj hPj
  have hloc := hlocal (sampleFrequency j) _ _ (cos_sampleFrequency j)
    (by simpa using hAj) (by simpa using hPj)
  rw [hej] at hloc
  have heq : 2*cos (I*nlsHamiltonianPhase a b N (sampleFrequency j)) =
      2*cosh (-I*(sampleFrequency j : ℂ)+nlsHamiltonianCorrection a b N (sampleFrequency j : ℂ)⁻¹) := by
    rw [mul_comm I,cos_mul_I,nlsHamiltonianPhase_eq_correction]
  have hboundj := hbound (sampleFrequency j)
    (by rw [abs_of_pos (sampleFrequency_pos j)]; exact hrj)
  rw [heq] at hboundj
  apply (hloc.trans hboundj).trans_eq
  rw [norm_inv,Complex.norm_real,Real.norm_eq_abs,mul_pow,inv_pow]
  ring

/-- These are actual trace-only phase samples, rather than a phase
postulated to have a Hamiltonian expansion. -/
theorem exists_nlsHamiltonian_extracted_phase_error (a b : ℝ → ℂ)
    (ha : ContDiff ℝ ∞ a) (hb : ContDiff ℝ ∞ b)
    (hpa : Function.Periodic a 1) (hpb : Function.Periodic b 1) (N : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ j in atTop,
      ‖sampledTracePhase (fun r => classicalDiscriminant
        (classicalPotentialOfFunctions a b ha.continuous hb.continuous) r) j-
          nlsHamiltonianCorrection a b N (sampleFrequency j : ℂ)⁻¹‖ ≤
        C*‖(sampleFrequency j : ℂ)⁻¹‖^N := by
  have hT := classicalDiscriminant_samples_tendsto a b ha hb hpa hpb
  exact exists_nlsHamiltonian_sampled_phase_sequence_error a b ha hb hpa hpb _
    (sampledTracePhase_tendsto _ hT) (sampledTracePhase_trace _ hT) N

end NLS.ZakharovShabat
