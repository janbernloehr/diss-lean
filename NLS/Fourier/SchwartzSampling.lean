import NLS.SequenceSpaces.SobolevEmbedding
import Mathlib.Analysis.Distribution.SchwartzSpace.Basic

/-!
# Sampling Schwartz functions at period-two frequencies

The samples `f (-n/2)` are absolutely summable, continuously in the Schwartz
topology. The sign and spacing are chosen so that sampling the Fourier transform
of a test function gives its integral against `exp(i π n x)`.
-/

noncomputable section
open scoped ENNReal SchwartzMap

namespace NLS.Fourier

private theorem summable_sampleEnvelope :
    Summable (fun n : ℤ => 1 / (1 + |(n : ℝ)|) ^ (2 : ℕ)) := by
  simpa only [Real.rpow_two] using summable_inverse_bracket (by norm_num : (1 : ℝ) < 2)

/-- A fixed, finite family of Schwartz seminorms controls lattice sampling. -/
def sampleSeminorm : Seminorm ℂ 𝓢(ℝ, ℂ) :=
  (Finset.Iic (2, 0)).sup (schwartzSeminormFamily ℂ ℝ ℂ)

/-- The sampling bound uses only decay up to degree two, with no derivatives. -/
theorem norm_sample_le (f : 𝓢(ℝ, ℂ)) (n : ℤ) :
    ‖f (-(n : ℝ) / 2)‖ ≤
      (16 * sampleSeminorm f) * (1 / (1 + |(n : ℝ)|) ^ (2 : ℕ)) := by
  have h := SchwartzMap.one_add_le_sup_seminorm_apply
    (𝕜 := ℂ) (m := (2, 0)) (k := 2) (n := 0) le_rfl le_rfl f (-(n : ℝ) / 2)
  simp only [norm_iteratedFDeriv_zero, Real.norm_eq_abs, abs_div, abs_neg,
    abs_of_pos (by norm_num : (0 : ℝ) < 2)] at h
  norm_num only [show (2 : ℝ) ^ 2 = 4 by norm_num] at h
  change (1 + |(n : ℝ)| / 2) ^ 2 * ‖f (-(n : ℝ) / 2)‖ ≤ 4 * sampleSeminorm f at h
  have hw : (1 + |(n : ℝ)|) ^ 2 ≤ 4 * (1 + |(n : ℝ)| / 2) ^ 2 := by
    nlinarith [abs_nonneg (n : ℝ)]
  have hm := mul_le_mul_of_nonneg_right hw (norm_nonneg (f (-(n : ℝ) / 2)))
  rw [mul_one_div, le_div_iff₀ (by positivity)]
  nlinarith

/-- Absolute convergence of all half-integer samples, including both tails. -/
theorem summable_norm_schwartzSamples (f : 𝓢(ℝ, ℂ)) :
    Summable (fun n : ℤ => ‖f (-(n : ℝ) / 2)‖) :=
  Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (norm_sample_le f)
    (summable_sampleEnvelope.mul_left (16 * sampleSeminorm f))

/-- Schwartz tests sampled at the signed physical frequency lattice. -/
def schwartzSamples (f : 𝓢(ℝ, ℂ)) : Coeff 1 :=
  ⟨fun n => f (-(n : ℝ) / 2), (memℓp_gen_iff (by simp : (0 : ℝ) < (1 : ℝ≥0∞).toReal)).mpr
    (by simpa using summable_norm_schwartzSamples f)⟩

@[simp] theorem schwartzSamples_apply (f : 𝓢(ℝ, ℂ)) (n : ℤ) :
    schwartzSamples f n = f (-(n : ℝ) / 2) := rfl

/-- A single finite Schwartz-seminorm bound for the entire sampled sequence. -/
theorem norm_schwartzSamples_le (f : 𝓢(ℝ, ℂ)) :
    ‖schwartzSamples f‖ ≤
      (16 * ∑' n : ℤ, 1 / (1 + |(n : ℝ)|) ^ (2 : ℕ)) * sampleSeminorm f := by
  have hn : ‖schwartzSamples f‖ = ∑' n : ℤ, ‖f (-(n : ℝ) / 2)‖ := by
    simpa using (lp.hasSum_norm (p := 1) (by simp) (schwartzSamples f)).tsum_eq.symm
  rw [hn]
  calc
    _ ≤ ∑' n : ℤ, (16 * sampleSeminorm f) * (1 / (1 + |(n : ℝ)|) ^ (2 : ℕ)) :=
      (summable_norm_schwartzSamples f).tsum_le_tsum (norm_sample_le f)
        (summable_sampleEnvelope.mul_left _)
    _ = _ := by rw [tsum_mul_left]; ring

/-- Sampling is continuous from the genuine Schwartz topology into `ℓ¹`. -/
def schwartzSamplesCLM : 𝓢(ℝ, ℂ) →L[ℂ] Coeff 1 :=
  SchwartzMap.mkCLMtoNormedSpace (σ := RingHom.id ℂ) schwartzSamples
    (fun f g => by ext n; rfl)
    (fun c f => by ext n; rfl)
    ⟨Finset.Iic (2, 0), 16 * ∑' n : ℤ, 1 / (1 + |(n : ℝ)|) ^ (2 : ℕ),
      by positivity, norm_schwartzSamples_le⟩

@[simp] theorem schwartzSamplesCLM_apply (f : 𝓢(ℝ, ℂ)) :
    schwartzSamplesCLM f = schwartzSamples f := rfl

end NLS.Fourier
