import NLS.ComplexAnalysis.DiscriminantSamples

/-! # Recursive spectral coefficient extraction from sampled phases

The coefficient at each order is a literal limit after subtracting the
previous coefficients. No Hamiltonian or coefficient sequence is an
input to the construction.
-/
noncomputable section
open Set Complex Filter Topology
namespace NLS.ComplexAnalysis

/-- Index `n` denotes the coefficient of `(2r)^(-(n+1))`. -/
def sampledPhaseCoefficient (T : ℝ → ℂ) (n : ℕ) : ℂ :=
  limUnder atTop (fun j : ℕ => (2*(sampleFrequency j : ℂ))^(n+1)*
    (sampledTracePhase T j-∑ k : Fin n,
      sampledPhaseCoefficient T k.val/(2*(sampleFrequency j : ℂ))^(k.val+1)))
termination_by n

/-- One extra inverse-frequency error order makes the scaled remainder
vanish. This applies to arbitrary phase samples, not just analytic germs. -/
theorem sampled_scaled_error_tendsto (e : ℕ → ℂ) (N : ℕ) (C : ℝ)
    (he : ∀ᶠ j in atTop, ‖e j‖ ≤ C*‖(sampleFrequency j : ℂ)⁻¹‖^(N+1)) :
    Tendsto (fun j => (2*(sampleFrequency j : ℂ))^N*e j) atTop (𝓝 0) := by
  have hb : ∀ᶠ j in atTop,
      ‖(2*(sampleFrequency j : ℂ))^N*e j‖ ≤ (C*2^N)*(sampleFrequency j)⁻¹ := by
    filter_upwards [he] with j hj
    have hr : sampleFrequency j ≠ 0 := (sampleFrequency_pos j).ne'
    calc
      ‖(2*(sampleFrequency j : ℂ))^N*e j‖ = (2*sampleFrequency j)^N*‖e j‖ := by
        rw [norm_mul,norm_pow,norm_mul,norm_ofNat,Complex.norm_real,
          Real.norm_eq_abs,abs_of_pos (sampleFrequency_pos j)]
      _ ≤ (2*sampleFrequency j)^N*(C*‖(sampleFrequency j : ℂ)⁻¹‖^(N+1)) :=
        mul_le_mul_of_nonneg_left hj
          (pow_nonneg (mul_nonneg (by norm_num) (sampleFrequency_pos j).le) N)
      _ = (C*2^N)*(sampleFrequency j)⁻¹ := by
        rw [norm_inv,Complex.norm_real,Real.norm_eq_abs,abs_of_pos (sampleFrequency_pos j),inv_pow]
        field_simp [hr]
        simp only [pow_succ,mul_pow]
        ring
  have hlim : Tendsto (fun j => (C*2^N)*(sampleFrequency j)⁻¹) atTop (𝓝 0) := by
    simpa only [mul_zero,Pi.inv_apply,Function.comp_def] using!
      sampleFrequency_tendsto.inv_tendsto_atTop.const_mul (C*2^N)
  exact tendsto_zero_iff_norm_tendsto_zero.mpr
    (squeeze_zero' (Eventually.of_forall (fun _ => norm_nonneg _)) hb hlim)

end NLS.ComplexAnalysis
