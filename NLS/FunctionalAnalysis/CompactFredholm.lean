import NLS.FunctionalAnalysis.FredholmDecomposition
import NLS.FunctionalAnalysis.CompactInvertibleComplement

/-! # Index zero for nonzero scalar shifts of compact operators -/
noncomputable section
namespace NLS.CompactSpectrum
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]

/-- Every nonzero scalar shift of a compact operator is Fredholm of index zero.
The equality states index zero without subtracting infinite dimensions. -/
theorem fredholm_index_zero_compact_shift (T : E →L[ℂ] E) (hT : IsCompactOperator T)
    {μ : ℂ} (hμ : μ ≠ 0) :
    (T - μ • 1).IsFredholm ∧
      Module.finrank ℂ (T - μ • 1).ker = Module.finrank ℂ (E ⧸ (T - μ • 1).range) := by
  obtain ⟨N,M,h,hfinite,hN,hM,hbij⟩ := exists_invertible_complement_compact_shift T hT hμ
  let _ := hfinite
  exact fredholm_index_zero_of_isTopCompl (T - μ • 1) h hN hM hbij

/-- A compact perturbation of any nonzero scalar identity has Fredholm index zero. -/
theorem fredholm_index_zero_of_compact_sub_smul (A : E →L[ℂ] E) {c : ℂ} (hc : c ≠ 0)
    (hA : IsCompactOperator (A - c • 1 : E →L[ℂ] E)) :
    A.IsFredholm ∧ Module.finrank ℂ A.ker = Module.finrank ℂ (E ⧸ A.range) := by
  have h := fredholm_index_zero_compact_shift (A - c • 1) hA (neg_ne_zero.mpr hc)
  have he : A - c • 1 - (-c) • 1 = A := by rw [neg_smul]; abel
  rw [he] at h
  exact h

end NLS.CompactSpectrum
