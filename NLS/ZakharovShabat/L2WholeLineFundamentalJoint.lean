import NLS.ZakharovShabat.L2WholeLineFloquetMass
import Mathlib.Analysis.Matrix.Normed

/-! # Joint continuity of the original whole-line fundamental matrix -/
noncomputable section
set_option autoImplicit false
open Set Matrix
open scoped Matrix.Norms.Elementwise
namespace NLS.ZakharovShabat

/-- The physical monodromy depends continuously on the original parameters. -/
theorem continuous_l2Monodromy_joint :
    Continuous (fun q : ℂ × IntervalPairL2 => l2Monodromy q.2 q.1) :=
  analyticOnNhd_l2Monodromy_joint.continuous

/-- Determinant one gives continuity of the original monodromy inverse. -/
theorem continuous_inv_l2Monodromy_joint :
    Continuous (fun q : ℂ × IntervalPairL2 => (l2Monodromy q.2 q.1)⁻¹) := by
  apply continuous_iff_continuousAt.mpr
  intro q
  apply (continuousAt_matrix_inv _ ?_).comp continuous_l2Monodromy_joint.continuousAt
  simpa only [Ring.inverse_eq_inv'] using continuousAt_inv₀
    (by simp : (l2Monodromy q.2 q.1).det ≠ 0)

/-- Every signed monodromy power is continuous in the physical parameters. -/
theorem continuous_l2MonodromyUnit_zpow (n : ℤ) :
    Continuous (fun q : ℂ × IntervalPairL2 =>
      (((l2MonodromyUnit q.2 q.1)^n : (Matrix (Fin 2) (Fin 2) ℂ)ˣ) : Matrix (Fin 2) (Fin 2) ℂ)) := by
  cases n with
  | ofNat n =>
    change Continuous (fun q : ℂ × IntervalPairL2 => (l2Monodromy q.2 q.1)^n)
    exact continuous_l2Monodromy_joint.pow n
  | negSucc n =>
    have he (q : ℂ × IntervalPairL2) :
        (((l2MonodromyUnit q.2 q.1)^(Int.negSucc n) : (Matrix (Fin 2) (Fin 2) ℂ)ˣ) :
          Matrix (Fin 2) (Fin 2) ℂ) = (l2Monodromy q.2 q.1)⁻¹^(n+1) := by
      rw [zpow_negSucc,← inv_pow,Units.val_pow_eq_pow_val]
      rfl
    simp only [he]
    exact continuous_inv_l2Monodromy_joint.pow (n+1)

private theorem locallyFinite_joint_wholeLine_strips :
    LocallyFinite (fun n : ℤ => Icc (n : ℝ) ((n : ℝ)+1)) := by
  intro x
  refine ⟨Ioo (x-1) (x+1),Ioo_mem_nhds (by linarith) (by linarith),?_⟩
  apply (Set.finite_Icc ⌊x-2⌋ ⌈x+1⌉).subset
  rintro n ⟨y,hy,hyx⟩
  have hl : (⌊x-2⌋ : ℝ) ≤ n := by
    have h := Int.floor_le (x-2)
    linarith [hy.2,hyx.1]
  have hu : (n : ℝ) ≤ ⌈x+1⌉ := by
    have h := Int.le_ceil (x+1)
    linarith [hy.1,hyx.2]
  exact ⟨Int.cast_le.mp hl,Int.cast_le.mp hu⟩

/-- Joint continuity includes every seam between positive and negative periods. -/
theorem continuous_l2WholeLineFundamentalMatrix_joint :
    Continuous (fun qt : (ℂ × IntervalPairL2) × ℝ =>
      l2WholeLineFundamentalMatrix qt.1.2 qt.1.1 qt.2) := by
  have htime : Continuous (fun qt : (ℂ × IntervalPairL2) × ℝ => qt.2) := continuous_snd
  have hloc := locallyFinite_joint_wholeLine_strips.preimage_continuous htime
  apply hloc.continuous
  · ext qt
    simp only [mem_iUnion,mem_preimage,mem_Icc,mem_univ,iff_true]
    exact ⟨⌊qt.2⌋,Int.floor_le qt.2,(Int.lt_floor_add_one qt.2).le⟩
  · intro n
    exact isClosed_Icc.preimage htime
  · intro n
    let r : (ℂ × IntervalPairL2) × ℝ → Icc (0 : ℝ) 1 :=
      fun qt => projIcc 0 1 (by norm_num) (qt.2-n)
    have hr : Continuous r := continuous_projIcc.comp (htime.sub continuous_const)
    have hM := continuous_l2FundamentalMatrix_time_joint.comp (continuous_fst.prodMk hr)
    have hB := (continuous_l2MonodromyUnit_zpow n).comp
      (continuous_fst : Continuous (fun qt : (ℂ × IntervalPairL2) × ℝ => qt.1))
    apply (hM.mul hB).continuousOn.congr
    intro qt hqt
    have ht : qt.2 ∈ Icc (n : ℝ) ((n : ℝ)+1) := hqt
    change l2WholeLineFundamentalMatrix qt.1.2 qt.1.1 qt.2 =
      l2FundamentalMatrix qt.1.2 qt.1.1 (r qt)*
        (((l2MonodromyUnit qt.1.2 qt.1.1)^n : (Matrix (Fin 2) (Fin 2) ℂ)ˣ) : Matrix (Fin 2) (Fin 2) ℂ)
    rw [l2WholeLineFundamentalMatrix_on_period _ _ n _ ht]
    congr 2
    apply Subtype.ext
    have hm : qt.2-(n : ℝ) ∈ Icc (0 : ℝ) 1 := by constructor <;> linarith [ht.1,ht.2]
    exact congrArg Subtype.val (projIcc_of_mem (by norm_num) hm).symm

/-- The actual inverse fundamental matrix is jointly continuous as well. -/
theorem continuous_inv_l2WholeLineFundamentalMatrix_joint :
    Continuous (fun qt : (ℂ × IntervalPairL2) × ℝ =>
      (l2WholeLineFundamentalMatrix qt.1.2 qt.1.1 qt.2)⁻¹) := by
  apply continuous_iff_continuousAt.mpr
  intro qt
  apply (continuousAt_matrix_inv _ ?_).comp continuous_l2WholeLineFundamentalMatrix_joint.continuousAt
  simpa only [Ring.inverse_eq_inv'] using continuousAt_inv₀
    ((Matrix.isUnit_iff_isUnit_det _).mp (isUnit_l2WholeLineFundamentalMatrix qt.1.2 qt.1.1 qt.2)).ne_zero

end NLS.ZakharovShabat
