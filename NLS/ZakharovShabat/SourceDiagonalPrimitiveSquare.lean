import NLS.ZakharovShabat.SourceFullAbelianSquareJointAnalytic
import NLS.ZakharovShabat.SourceDiagonalLaurentGeometry

/-! # The central filled primitive square at zero energy

It is analytic on an ambient complex neighborhood of the entire real
diagonal, including a collapsed central gap. The extension comes from
the actual Cauchy square; no square root or sign branch is selected.
-/
noncomputable section
open Set Metric Filter Topology Complex
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

theorem exists_sourceDiagonalPrimitiveSquare (hp : p ≠ ⊤) (hp1 : 1 < p) :
    ∃ U : Set (CoeffPair p), ∃ F : CoeffPair p → ℂ,
      IsOpen U ∧ realDiagonalSourceLocus p ⊆ U ∧ AnalyticOnNhd ℂ F U ∧
      ∀ φ : realTypeSourceSubmodule p,
        F φ.val = sourceAbelianSquare hp hp1 φ.val φ.property 0 0 := by
  obtain ⟨W,_,_,hfamilies⟩ := exists_sourceFullAbelianUniformCauchyFamilies hp hp1
  let F : CoeffPair p → ℂ := fun ψ => sourceFullAbelianSquare hp hp1 W 0 (0,ψ)
  have hreal (φ : realTypeSourceSubmodule p) :
      F φ.val = sourceAbelianSquare hp hp1 φ.val φ.property 0 0 := by
    obtain ⟨C,hC⟩ := hfamilies φ
    have hφ : φ.val ∈ ball C.discs.source.val C.discs.sourceRadius := by
      rw [hC]
      exact mem_ball_self C.discs.sourceRadius_pos
    obtain ⟨E⟩ := C.charts φ.val hφ
    exact sourceFullAbelianSquare_eq_real φ E 0 0
  have ha (φ : realDiagonalSourceLocus p) : AnalyticAt ℂ F φ.val := by
    let φr : realTypeSourceSubmodule p := ⟨φ.val,φ.property.1⟩
    obtain ⟨C,hC⟩ := hfamilies φr
    have hφ : φ.val ∈ ball C.discs.source.val C.discs.sourceRadius := by
      rw [hC]
      exact mem_ball_self C.discs.sourceRadius_pos
    have hz : (0 : ℂ) ∈ ball (C.discs.center 0) (C.discs.outer 0) :=
      C.segment_subset_outer 0 φ.val hφ (zero_mem_central_segment_of_diagonal hp hp1 φr φ.property.2)
    obtain ⟨M,hM,_,hrealM,hcoord⟩ := exists_global_source_analytic_midpoint_squaredGap hp hp1
    let V := ball C.discs.source.val C.discs.sourceRadius ∩ M
    have hV : IsOpen V := isOpen_ball.inter hM
    have hφV : φ.val ∈ V := ⟨hφ,hrealM φ.property.1⟩
    have hS := C.square_joint_analytic V inter_subset_left 0
      (fun ψ hψ => (hcoord ψ hψ.2 0).1) (fun ψ hψ => (hcoord ψ hψ.2 0).2)
    have hcomp : AnalyticAt ℂ (fun ψ => C.square 0 (0,ψ)) φ.val :=
      (hS (0,φ.val) ⟨hz,hφV⟩).comp (analyticAt_const.prod analyticAt_id)
    apply hcomp.congr
    filter_upwards [hV.mem_nhds hφV] with ψ hψ
    exact (C.fullSquare_eq_square 0 ψ hψ.1 hz).symm
  let U := interior {ψ | AnalyticAt ℂ F ψ}
  refine ⟨U,F,isOpen_interior,?_,?_,hreal⟩
  · intro φ hφ
    exact mem_interior_iff_mem_nhds.mpr (ha ⟨φ,hφ⟩).eventually_analyticAt
  · intro ψ hψ
    exact interior_subset (s := {ψ | AnalyticAt ℂ F ψ}) hψ

end NLS.ZakharovShabat
