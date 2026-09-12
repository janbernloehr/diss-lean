import NLS.Fourier.SchwartzSampling
import NLS.SequenceSpaces.TemperedWeight

/-!
# Weighted Schwartz lattice sampling

Schwartz decay absorbs every polynomially bounded reciprocal weight. Sampling
`f(-n/2)/w(n)` is a continuous linear map into `ℓ¹` whenever the inverse weight
has polynomial growth.
-/

noncomputable section
open scoped ENNReal SchwartzMap
namespace NLS.Fourier

private def samplingSeminorm (q : ℕ) : Seminorm ℂ 𝓢(ℝ, ℂ) :=
  (Finset.Iic (q, 0)).sup (schwartzSeminormFamily ℂ ℝ ℂ)

private theorem norm_sample_polynomial_le (f : 𝓢(ℝ, ℂ)) (K : ℕ) (n : ℤ) :
    (1 + |(n : ℝ)|) ^ K * ‖f (-(n : ℝ) / 2)‖ ≤
      (2 ^ (K + 2) * 2 ^ (K + 2) * samplingSeminorm (K + 2) f) /
        (1 + |(n : ℝ)|) ^ 2 := by
  have h := SchwartzMap.one_add_le_sup_seminorm_apply
    (𝕜 := ℂ) (m := (K + 2, 0)) le_rfl le_rfl f (-(n : ℝ) / 2)
  simp only [norm_iteratedFDeriv_zero, Real.norm_eq_abs, abs_div, abs_neg,
    abs_of_pos (by norm_num : (0 : ℝ) < 2)] at h
  change (1 + |(n : ℝ)| / 2) ^ (K + 2) * ‖f (-(n : ℝ) / 2)‖ ≤
    2 ^ (K + 2) * samplingSeminorm (K + 2) f at h
  have hb : (1 + |(n : ℝ)|) ^ (K + 2) ≤
      2 ^ (K + 2) * (1 + |(n : ℝ)| / 2) ^ (K + 2) := by
    rw [← mul_pow]
    gcongr
    linarith
  rw [le_div_iff₀ (by positivity)]
  calc
    _ = (1 + |(n : ℝ)|) ^ (K + 2) * ‖f (-(n : ℝ) / 2)‖ := by rw [pow_add]; ring
    _ ≤ (2 ^ (K + 2) * (1 + |(n : ℝ)| / 2) ^ (K + 2)) * ‖f (-(n : ℝ) / 2)‖ :=
      mul_le_mul_of_nonneg_right hb (norm_nonneg _)
    _ ≤ _ := by
      have he := mul_le_mul_of_nonneg_left h (by positivity : (0 : ℝ) ≤ 2 ^ (K + 2))
      simpa only [mul_assoc] using he

private theorem exists_weightedSample_bound (w : Weight) (hw : w.HasTemperedInverse) :
    ∃ K : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ (f : 𝓢(ℝ, ℂ)) (n : ℤ),
      ‖f (-(n : ℝ) / 2) / (w n : ℂ)‖ ≤
        (C * samplingSeminorm (K + 2) f) * (1 / (1 + |(n : ℝ)|) ^ 2) := by
  obtain ⟨K, C, hC, hbound⟩ := hw
  refine ⟨K, C * (2 ^ (K + 2) * 2 ^ (K + 2)), by positivity, fun f n => ?_⟩
  calc
    _ = ‖f (-(n : ℝ) / 2)‖ * (1 / w n) := by
      simp [Complex.norm_real, abs_of_pos (w.positive n), div_eq_mul_inv]
    _ ≤ ‖f (-(n : ℝ) / 2)‖ * (C * (1 + |(n : ℝ)|) ^ K) :=
      mul_le_mul_of_nonneg_left (hbound n) (norm_nonneg _)
    _ = C * ((1 + |(n : ℝ)|) ^ K * ‖f (-(n : ℝ) / 2)‖) := by ring
    _ ≤ C * ((2 ^ (K + 2) * 2 ^ (K + 2) * samplingSeminorm (K + 2) f) /
        (1 + |(n : ℝ)|) ^ 2) := mul_le_mul_of_nonneg_left (norm_sample_polynomial_le f K n) hC
    _ = _ := by ring

private theorem summable_weightedSampleEnvelope :
    Summable (fun n : ℤ => 1 / (1 + |(n : ℝ)|) ^ (2 : ℕ)) := by
  simpa only [Real.rpow_two] using summable_inverse_bracket (by norm_num : (1 : ℝ) < 2)

/-- Weighted lattice samples of a Schwartz function are absolutely summable. -/
theorem summable_norm_weightedSchwartzSamples (w : Weight) (hw : w.HasTemperedInverse)
    (f : 𝓢(ℝ, ℂ)) : Summable (fun n : ℤ => ‖f (-(n : ℝ) / 2) / (w n : ℂ)‖) := by
  obtain ⟨K, C, _, hbound⟩ := exists_weightedSample_bound w hw
  exact Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (hbound f)
    (summable_weightedSampleEnvelope.mul_left (C * samplingSeminorm (K + 2) f))

/-- Samples divided by the original positive weight, retaining the physical signed lattice. -/
def weightedSchwartzSamples (w : Weight) (hw : w.HasTemperedInverse) (f : 𝓢(ℝ, ℂ)) : Coeff 1 :=
  ⟨fun n => f (-(n : ℝ) / 2) / (w n : ℂ),
    (memℓp_gen_iff (by simp : (0 : ℝ) < (1 : ℝ≥0∞).toReal)).mpr
      (by simpa using summable_norm_weightedSchwartzSamples w hw f)⟩

@[simp] theorem weightedSchwartzSamples_apply (w : Weight) (hw : w.HasTemperedInverse)
    (f : 𝓢(ℝ, ℂ)) (n : ℤ) : weightedSchwartzSamples w hw f n = f (-(n : ℝ) / 2) / (w n : ℂ) := rfl

private theorem exists_norm_weightedSchwartzSamples_bound (w : Weight) (hw : w.HasTemperedInverse) :
    ∃ K : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ f : 𝓢(ℝ, ℂ),
      ‖weightedSchwartzSamples w hw f‖ ≤ C * samplingSeminorm (K + 2) f := by
  obtain ⟨K, C, hC, hbound⟩ := exists_weightedSample_bound w hw
  refine ⟨K, C * (∑' n : ℤ, 1 / (1 + |(n : ℝ)|) ^ (2 : ℕ)), by positivity, fun f => ?_⟩
  have hn : ‖weightedSchwartzSamples w hw f‖ = ∑' n : ℤ, ‖f (-(n : ℝ) / 2) / (w n : ℂ)‖ := by
    simpa using (lp.hasSum_norm (p := 1) (by simp) (weightedSchwartzSamples w hw f)).tsum_eq.symm
  rw [hn]
  calc
    _ ≤ ∑' n : ℤ, (C * samplingSeminorm (K + 2) f) * (1 / (1 + |(n : ℝ)|) ^ 2) :=
      (summable_norm_weightedSchwartzSamples w hw f).tsum_le_tsum (hbound f)
        (summable_weightedSampleEnvelope.mul_left _)
    _ = _ := by rw [tsum_mul_left]; ring

/-- Weighted sampling is continuous from the genuine Schwartz topology to `ℓ¹`. -/
def weightedSchwartzSamplesCLM (w : Weight) (hw : w.HasTemperedInverse) : 𝓢(ℝ, ℂ) →L[ℂ] Coeff 1 :=
  SchwartzMap.mkCLMtoNormedSpace (σ := RingHom.id ℂ) (weightedSchwartzSamples w hw)
    (fun f g => by ext n; simp [add_div])
    (fun c f => by ext n; simp [mul_div_assoc])
    (by
      obtain ⟨K, C, hC, hbound⟩ := exists_norm_weightedSchwartzSamples_bound w hw
      exact ⟨Finset.Iic (K + 2, 0), C, hC, hbound⟩)

@[simp] theorem weightedSchwartzSamplesCLM_apply (w : Weight) (hw : w.HasTemperedInverse)
    (f : 𝓢(ℝ, ℂ)) : weightedSchwartzSamplesCLM w hw f = weightedSchwartzSamples w hw f := rfl

end NLS.Fourier
