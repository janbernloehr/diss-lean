import NLS.ZakharovShabat.SourceNormalizedActionCommonExponentDomain

/-! # A common bound for all normalized Hilbert actions

The established ℓ² bound on the deviation from the free normalized action
bounds every scalar factor, including at collapsed gaps.
-/
noncomputable section
open Set
open scoped ENNReal
namespace NLS.ZakharovShabat

/-- All normalized action factors are bounded on one complex neighborhood of each
real Hilbert source, uniformly in the signed spectral index. -/
theorem exists_local_hilbert_normalizedAction_uniform_bound
    (φ : CoeffPair 2) (hφ : IsRealType (CoeffPair.toMax 2 φ)) :
    ∃ U : Set (CoeffPair 2), IsOpen U ∧ φ ∈ U ∧ ∃ C : ℝ, 0 ≤ C ∧
      ∀ ψ ∈ U, ∀ n : ℤ,
        ‖sourceNormalizedActionComplexExtension (by simp) (by norm_num) n ψ‖ ≤ C := by
  obtain ⟨U,hU,hφU,hall⟩ := exists_local_sourceNormalizedActionDeviation_allExponents
    (by simp : (2 : ℝ≥0∞) ≠ ⊤) (by norm_num) le_rfl φ hφ
  obtain ⟨M,hM⟩ := hall 2 (by norm_num) (by simp)
  refine ⟨U,hU,hφU,|M|+1,by positivity,?_⟩
  intro ψ hψ n
  obtain ⟨A,hA,hAn⟩ := hM ψ hψ
  have hn : ‖A n‖ ≤ M := (lp.norm_apply_le_norm (by norm_num) A n).trans hAn
  have he := norm_add_le (A n) (1 : ℂ)
  rw [hA n, sourceNormalizedActionDeviation, sub_add_cancel, norm_mul,
    Complex.norm_ofNat, norm_one] at he
  rw [hA n, sourceNormalizedActionDeviation] at hn
  linarith [le_abs_self M, abs_nonneg M]

end NLS.ZakharovShabat
