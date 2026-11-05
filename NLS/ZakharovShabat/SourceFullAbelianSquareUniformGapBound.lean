import NLS.ZakharovShabat.SourceFullAbelianSquareGapMajorants
import NLS.ZakharovShabat.SourceGapCosineError

/-! One complex neighborhood bounds the actual filled square by the
squared gap length, before every selected index and every gap point. -/
noncomputable section
open Set Metric Complex
open scoped ENNReal
namespace NLS.ZakharovShabat

theorem exists_sourceFullAbelian_local_uniform_square_gap_bound :
    ∃ W : Set (CoeffPair 2), ∀ φ : realTypeSourceSubmodule 2,
      ∃ C : SourceFullAbelianUniformCauchyFamily (by simp) (by norm_num) W,
      ∃ V : Set (CoeffPair 2), IsOpen V ∧ φ.val ∈ V ∧
        V ⊆ ball C.discs.source.val C.discs.sourceRadius ∧
        ∃ B : ℝ, 0 < B ∧ ∀ ψ ∈ V, ∀ j : ℤ,
          ∀ z ∈ sourcePeriodicSegment (by simp) (by norm_num) ψ j,
            ‖sourceFullAbelianSquare (by simp) (by norm_num) W j (z,ψ)‖ ≤
              B*‖sourcePeriodicGapDisplacement (by simp) (by norm_num) ψ j‖^2 := by
  obtain ⟨W,_,_,hlocal⟩ := exists_sourceFullAbelian_local_square_gap_majorants
    (p := 2) (by simp) (by norm_num)
  refine ⟨W,?_⟩
  intro φ
  obtain ⟨C,V,hV,hφ,hVC,hmajor⟩ := hlocal φ
  obtain ⟨M,hM,hrows⟩ := hmajor 2 (by simp) (by norm_num)
  refine ⟨C,V,hV,hφ,hVC,2*M+1,by positivity,?_⟩
  intro ψ hψ j z hz
  obtain ⟨Bq,Bg,hBq,hBg,hpoint⟩ := hrows ψ hψ
  have hqj := (lp.norm_apply_le_norm (by norm_num : (2:ℝ≥0∞) ≠ 0) Bq j).trans hBq
  have hgj := (lp.norm_apply_le_norm (by norm_num : ENNReal.ofReal ((2:ℝ≥0∞).toReal/2) ≠ 0) Bg j).trans hBg
  have hpoly := norm_sourceAngularSelectedPolynomial_le_gap_sq
    (p := 2) (by simp) (by norm_num) ψ j z hz
  calc
    _ ≤ ‖sourceFullAbelianSquare (by simp) (by norm_num) W j (z,ψ)+
          sourceAngularSelectedPolynomial (by simp) (by norm_num) ψ j z‖+
        ‖sourceAngularSelectedPolynomial (by simp) (by norm_num) ψ j z‖ := by
      simpa only [add_sub_cancel_right] using norm_sub_le
        (sourceFullAbelianSquare (by simp) (by norm_num) W j (z,ψ)+
          sourceAngularSelectedPolynomial (by simp) (by norm_num) ψ j z)
        (sourceAngularSelectedPolynomial (by simp) (by norm_num) ψ j z)
    _ ≤ _ := by
      have he := hpoint j z hz
      nlinarith [sq_nonneg ‖sourcePeriodicGapDisplacement (by simp) (by norm_num) ψ j‖,
        mul_le_mul_of_nonneg_left (add_le_add hqj hgj)
          (sq_nonneg ‖sourcePeriodicGapDisplacement (by simp) (by norm_num) ψ j‖)]

end NLS.ZakharovShabat
