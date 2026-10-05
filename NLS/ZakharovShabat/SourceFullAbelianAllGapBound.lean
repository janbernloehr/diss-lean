import NLS.ZakharovShabat.SourceFullAbelianAllGapMajorants
import NLS.ZakharovShabat.SourceFullAbelianSquareGapBound

/-! # Uniform linear bounds on every complex gap

The mixed sequence majorants, including their finite central correction,
give one scalar bound for both sides and every gap index.
-/
noncomputable section
open Set Metric Complex
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- A common source neighborhood and positive scalar control the actual
primitive boundary on all gaps, with no cutoff or open-gap hypothesis. -/
theorem exists_sourceFullAbelian_all_gap_bound (hp : p ≠ ⊤) (hp1 : 1 < p) :
    ∃ W : Set (CoeffPair p), IsOpen W ∧ realTypeSourceLocus p ⊆ W ∧
      ∀ φ : realTypeSourceSubmodule p,
        ∃ C : SourceFullAbelianUniformCauchyFamily hp hp1 W,
        ∃ V : Set (CoeffPair p), IsOpen V ∧ φ.val ∈ V ∧
          V ⊆ ball C.discs.source.val C.discs.sourceRadius ∧
          ∃ B : ℝ, 0 < B ∧ ∀ ψ ∈ V, ∀ n : ℤ, ∀ θ ∈ Icc (0:ℝ) Real.pi, ∀ upper : Bool,
            ‖C.gapBoundary n ψ θ upper‖ ≤ B *
              ‖canonicalPeriodicGap hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) n‖ := by
  obtain ⟨W,hW,hreal,hlocal⟩ := exists_sourceFullAbelian_all_gap_majorants hp hp1
  refine ⟨W,hW,hreal,?_⟩
  intro φ
  obtain ⟨C,V,hV,hφ,hVC,hmajor⟩ := hlocal φ
  obtain ⟨M,hM,hb⟩ := hmajor 2 (by simp) (by norm_num)
  have hp0 : 0 < p.toReal := ENNReal.toReal_pos (zero_lt_one.trans hp1).ne' hp
  have hg0 : ENNReal.ofReal (p.toReal/2) ≠ 0 := (ENNReal.ofReal_pos.mpr (by positivity)).ne'
  refine ⟨C,V,hV,hφ,hVC,2*M+1,by positivity,?_⟩
  intro ψ hψ n θ hθ upper
  obtain ⟨Bq,Bg,hBq,hBg,hpoint⟩ := hb ψ hψ
  have hqj := (lp.norm_apply_le_norm (by norm_num : (2 : ℝ≥0∞) ≠ 0) Bq n).trans hBq
  have hgj := (lp.norm_apply_le_norm hg0 Bg n).trans hBg
  have hroot : ‖I*sourceStandardRootGapBoundary hp hp1 ψ n θ upper‖ ≤
      ‖sourcePeriodicGapDisplacement hp hp1 ψ n‖ := by
    simp only [norm_mul,norm_I,one_mul]
    apply (norm_sourceStandardRootGapBoundary_le_halfGap hp hp1 ψ n θ upper).trans
    linarith [norm_nonneg (sourcePeriodicGapDisplacement hp hp1 ψ n)]
  calc
    _ ≤ ‖C.gapBoundary n ψ θ upper-I*sourceStandardRootGapBoundary hp hp1 ψ n θ upper‖ +
        ‖I*sourceStandardRootGapBoundary hp hp1 ψ n θ upper‖ := norm_le_norm_sub_add _ _
    _ ≤ ‖sourcePeriodicGapDisplacement hp hp1 ψ n‖*(‖Bq n‖+‖Bg n‖) +
        ‖sourcePeriodicGapDisplacement hp hp1 ψ n‖ := add_le_add (hpoint n θ hθ upper) hroot
    _ ≤ ‖sourcePeriodicGapDisplacement hp hp1 ψ n‖*(M+M) +
        ‖sourcePeriodicGapDisplacement hp hp1 ψ n‖ :=
      add_le_add (mul_le_mul_of_nonneg_left (add_le_add hqj hgj)
        (norm_nonneg (sourcePeriodicGapDisplacement hp hp1 ψ n))) le_rfl
    _ = (2*M+1)*‖sourcePeriodicGapDisplacement hp hp1 ψ n‖ := by ring
    _ = _ := congrArg (fun z : ℂ => (2*M+1)*‖z‖) (sourcePeriodicGapDisplacement_apply hp hp1 ψ n)

end NLS.ZakharovShabat
