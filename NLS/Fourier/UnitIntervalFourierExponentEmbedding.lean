import NLS.Fourier.UnitIntervalC1FourierLebesgue
import NLS.SequenceSpaces.ExponentEmbedding

/-! # Contractive exponent embeddings for actual unit-interval Fourier coefficients -/

noncomputable section
open scoped ENNReal
namespace NLS.Fourier

/-- Increasing the Fourier exponent decreases the norm of the same actual coefficients. -/
theorem norm_unitIntervalC1Coefficients_mono_exponent
    {r q : ℝ≥0∞} (hr : 1 < r) (hq : 1 < q) (hrq : r ≤ q)
    (f : ℝ → ℂ) (hf : ContDiff ℝ 1 f) :
    ‖unitIntervalC1Coefficients hq f hf‖ ≤ ‖unitIntervalC1Coefficients hr f hf‖ := by
  let : Fact (1 ≤ r) := ⟨hr.le⟩
  let : Fact (1 ≤ q) := ⟨hq.le⟩
  have he : NLS.Coeff.exponentInclusion hrq (unitIntervalC1Coefficients hr f hf) =
      unitIntervalC1Coefficients hq f hf := by ext n; rfl
  rw [← he]
  exact NLS.Coeff.norm_exponentInclusion_le hrq _

end NLS.Fourier
