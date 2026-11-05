import NLS.ComplexAnalysis.RealCutConjugation

/-! # Reflection of a continuous two-zero quotient on a real disc -/

noncomputable section
open Set Metric Complex
open scoped ComplexConjugate
namespace NLS.ComplexAnalysis

theorem real_two_zero_unit_conj
    (X Q : ℂ → ℂ) (c r a b : ℝ)
    (hQ : ContinuousOn Q (ball (c : ℂ) r))
    (hX : ∀ z ∈ ball (c : ℂ) r, X (conj z) = conj (X z))
    (hfactor : ∀ z ∈ ball (c : ℂ) r, X z = (z-a)*(z-b)*Q z) :
    ∀ z ∈ ball (c : ℂ) r, Q (conj z) = conj (Q z) := by
  have hc (z : ℂ) (hz : z ∈ ball (c : ℂ) r) : conj z ∈ ball (c : ℂ) r := by
    simpa only [mem_ball,dist_conj_comm,conj_ofReal] using hz
  apply continuous_eqOn_of_dense_on_open (segment ℝ (a : ℂ) b)ᶜ (ball (c : ℂ) r)
    (dense_complex_segment_complement _ _) isOpen_ball (fun z => Q (conj z)) (fun z => conj (Q z))
    (hQ.comp continuous_conj.continuousOn hc) (continuous_conj.comp_continuousOn hQ)
  intro z hz
  dsimp only
  have hzc := conj_mem_real_cut c r a b z hz
  have ha : conj z ≠ (a : ℂ) := fun he => hzc.2 (he ▸ left_mem_segment ℝ _ _)
  have hb : conj z ≠ (b : ℂ) := fun he => hzc.2 (he ▸ right_mem_segment ℝ _ _)
  apply mul_left_cancel₀ (mul_ne_zero (sub_ne_zero.mpr ha) (sub_ne_zero.mpr hb))
  rw [← hfactor _ hzc.1,hX z hz.1,hfactor z hz.1]
  simp only [map_mul,map_sub,conj_ofReal]

end NLS.ComplexAnalysis
