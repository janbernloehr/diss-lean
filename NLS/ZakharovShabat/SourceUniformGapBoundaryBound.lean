import NLS.ZakharovShabat.SourceFullAbelianCentralGapBound
import NLS.ZakharovShabat.SourceFullAbelianGapAllExponentTails
import NLS.ZakharovShabat.SourceFullAbelianSquareGapBound

/-! Every actual Cauchy primitive family has a uniform boundary bound
proportional to the selected gap on a common complex source neighborhood. -/
noncomputable section
set_option autoImplicit false
open Set Metric Complex
open scoped ENNReal
namespace NLS.ZakharovShabat.SourceFullAbelianUniformCauchyFamily
variable {W : Set (CoeffPair 2)}

theorem exists_local_uniform_gapBoundary_bound
    (C : SourceFullAbelianUniformCauchyFamily (by norm_num) (by norm_num) W)
    (φ : realTypeSourceSubmodule 2) (hφC : φ.val∈ball C.discs.source.val C.discs.sourceRadius) :
    ∃ T : Set (CoeffPair 2), IsOpen T ∧ φ.val∈T ∧ T⊆ball C.discs.source.val C.discs.sourceRadius ∧
      ∃ B : ℝ, 0≤B ∧ ∀ ψ∈T, ∀ n : ℤ, ∀ θ∈Icc (0 : ℝ) Real.pi,
        ‖C.gapBoundary n ψ θ true‖≤‖sourcePeriodicGapDisplacement (by norm_num) (by norm_num) ψ n‖*B := by
  obtain ⟨V,hV,hφV,K,htail⟩ := exists_local_sourceFullAbelian_gap_all_exponent_tails
    (by norm_num : (2 : ℝ≥0∞)≠⊤) (by norm_num) φ.val φ.property
  obtain ⟨M,hM,hrows⟩ := htail 2 (by norm_num) (by norm_num)
  let S := Finset.Icc (-(K : ℤ)) (K : ℤ)
  obtain ⟨L,hL,hφL,hLC,A,hA,hfinite⟩ := C.exists_local_finite_gap_comparison_bound φ.val hφC S
  let B := max A (2*M)+1
  have hB : 0≤B := by dsimp [B]; positivity
  refine ⟨V∩L,hV.inter hL,⟨hφV,hφL⟩,fun ψ hψ => hLC hψ.2,B,hB,?_⟩
  intro ψ hψ n θ hθ
  have herr : ‖C.gapBoundary n ψ θ true-I*sourceStandardRootGapBoundary
      (by norm_num) (by norm_num) ψ n θ true‖≤
      ‖sourcePeriodicGapDisplacement (by norm_num) (by norm_num) ψ n‖*max A (2*M) := by
    by_cases hn : n∈S
    · exact (hfinite ψ hψ.2 n hn θ true).trans
        (mul_le_mul_of_nonneg_left (le_max_left _ _) (norm_nonneg _))
    · obtain ⟨Bq,Bg,hBq,hBg,hpoint⟩ := hrows ψ hψ.1
      have hnK : K≤n.natAbs := by simp only [S,Finset.mem_Icc] at hn; omega
      have hbq : ‖Bq n‖≤M := (lp.norm_apply_le_norm (by norm_num) Bq n).trans hBq
      have hbg : ‖Bg n‖≤M := (lp.norm_apply_le_norm (by norm_num) Bg n).trans hBg
      exact (hpoint W C (hLC hψ.2) n hnK θ hθ true).trans
        (mul_le_mul_of_nonneg_left (by linarith [le_max_right A (2*M)]) (norm_nonneg _))
  have hroot := norm_sourceStandardRootGapBoundary_le_halfGap (by norm_num) (by norm_num) ψ n θ true
  calc
    _=‖(C.gapBoundary n ψ θ true-I*sourceStandardRootGapBoundary
        (by norm_num) (by norm_num) ψ n θ true)+I*sourceStandardRootGapBoundary
          (by norm_num) (by norm_num) ψ n θ true‖ := by rw [sub_add_cancel]
    _≤_ := (norm_add_le _ _).trans (add_le_add herr (by simpa only [norm_mul,norm_I,one_mul] using hroot))
    _≤_ := by dsimp only [B]; nlinarith [norm_nonneg (sourcePeriodicGapDisplacement (by norm_num) (by norm_num) ψ n)]

end NLS.ZakharovShabat.SourceFullAbelianUniformCauchyFamily
