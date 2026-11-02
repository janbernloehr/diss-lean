import NLS.ComplexAnalysis.ComplexSegmentComplementConnected

/-! # Conjugation of real-centered discs with a real segment removed -/

noncomputable section
open Set Metric Complex
open scoped ComplexConjugate
namespace NLS.ComplexAnalysis

theorem conj_mem_real_cut (c r l u : ℝ) (z : ℂ)
    (hz : z ∈ ball (c : ℂ) r \ segment ℝ (l : ℂ) u) :
    conj z ∈ ball (c : ℂ) r \ segment ℝ (l : ℂ) u := by
  have hseg (w : ℂ) (hw : w ∈ segment ℝ (l : ℂ) u) :
      conj w ∈ segment ℝ (l : ℂ) u := by
    obtain ⟨t,ht,rfl⟩ := by rw [segment_eq_image_lineMap] at hw; exact hw
    rw [segment_eq_image_lineMap]
    refine ⟨t,ht,?_⟩
    simp only [AffineMap.lineMap_apply_module, Complex.real_smul,
      map_add, map_mul, conj_ofReal]
  refine ⟨?_,fun hs => hz.2 (by simpa only [conj_conj] using hseg _ hs)⟩
  simpa only [mem_ball,dist_conj_comm,conj_ofReal] using hz.1

end NLS.ComplexAnalysis
