import NLS.SequenceSpaces.SourceLemmaI3

/-! # The compact-operator tail consequence used at the start of I.4 -/
noncomputable section
open Set Filter Topology
open scoped ENNReal
namespace NLS.Coeff
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- Compactness makes the entire omitted output small in operator norm,
uniformly for every larger cutoff. No input columns are discarded. -/
theorem exists_sourceI3Tail_comp_norm_le (hp : p ≠ ⊤) (T : E →L[ℂ] Coeff p)
    (hT : IsCompactOperator T) {ε : ℝ} (hε : 0 < ε) :
    ∃ N : ℕ, 1 ≤ N ∧ ∀ M : ℕ, N ≤ M → ‖(sourceI3Tail M).comp T‖ ≤ ε := by
  have hK := hT.isCompact_closure_image_closedBall 1
  obtain ⟨N,hN,hbound⟩ := ((sourceLemmaI3 hp _).mp hK.totallyBounded).2 ε hε
  refine ⟨N,hN,fun M hM => ?_⟩
  apply ContinuousLinearMap.opNorm_le_of_unit_norm hε.le
  intro x hx
  exact (norm_sourceI3Tail_antitone (T x) hM).trans
    (hbound (T x) (subset_closure ⟨x,by simpa only [Metric.mem_closedBall,dist_zero_right,hx] using (le_rfl : (1 : ℝ) ≤ 1),rfl⟩))

/-- Symmetric finite-output approximations converge in operator norm for every compact operator. -/
theorem tendsto_sourceI3Tail_comp (hp : p ≠ ⊤) (T : E →L[ℂ] Coeff p)
    (hT : IsCompactOperator T) :
    Tendsto (fun N : ℕ => (sourceI3Tail N).comp T) atTop (𝓝 0) := by
  apply Metric.tendsto_atTop.mpr
  intro ε hε
  obtain ⟨N,_,hN⟩ := exists_sourceI3Tail_comp_norm_le hp T hT (half_pos hε)
  refine ⟨N,fun M hM => ?_⟩
  rw [dist_zero_right]
  exact (hN M hM).trans_lt (half_lt_self hε)

end NLS.Coeff
