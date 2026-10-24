import NLS.ZakharovShabat.L2PeriodicFundamental

/-! # Extension of the physical L2 fundamental matrix to all real times

Integer powers of the actual invertible monodromy glue the unit-interval
solution at every positive and negative period. This construction is a
prerequisite for the whole-line operator, which is not defined here.
-/
noncomputable section
set_option autoImplicit false
open Set Complex Matrix
open scoped Matrix.Norms.Elementwise
namespace NLS.ZakharovShabat

/-- The physical monodromy, with its determinant-one inverse. -/
def l2MonodromyUnit (u : IntervalPairL2) (z : ℂ) : (Matrix (Fin 2) (Fin 2) ℂ)ˣ :=
  Matrix.nonsingInvUnit (l2Monodromy u z) (by rw [det_l2Monodromy]; exact isUnit_one)

@[simp] theorem coe_l2MonodromyUnit (u : IntervalPairL2) (z : ℂ) :
    (l2MonodromyUnit u z : Matrix (Fin 2) (Fin 2) ℂ) = l2Monodromy u z := rfl

/-- The time coordinate within one period, including negative real times. -/
def l2WholeLinePeriodTime (t : ℝ) : Icc (0 : ℝ) 1 :=
  ⟨Int.fract t,Int.fract_nonneg t,(Int.fract_lt_one t).le⟩

/-- The actual unit-interval fundamental matrix continued to every real time. -/
def l2WholeLineFundamentalMatrix (u : IntervalPairL2) (z : ℂ) (t : ℝ) :
    Matrix (Fin 2) (Fin 2) ℂ :=
  l2FundamentalMatrix u z (l2WholeLinePeriodTime t) *
    ((l2MonodromyUnit u z)^⌊t⌋ : (Matrix (Fin 2) (Fin 2) ℂ)ˣ)

/-- At integer times the continuation is the corresponding integer monodromy power. -/
@[simp] theorem l2WholeLineFundamentalMatrix_int (u : IntervalPairL2) (z : ℂ) (n : ℤ) :
    l2WholeLineFundamentalMatrix u z (n : ℝ) =
      ((l2MonodromyUnit u z)^n : (Matrix (Fin 2) (Fin 2) ℂ)ˣ) := by
  have ht : l2WholeLinePeriodTime (n : ℝ) = ⟨0,by constructor <;> norm_num⟩ := by
    apply Subtype.ext
    simp [l2WholeLinePeriodTime]
  simp [l2WholeLineFundamentalMatrix,ht]

/-- The continuation has the original normalized initial value. -/
@[simp] theorem l2WholeLineFundamentalMatrix_zero (u : IntervalPairL2) (z : ℂ) :
    l2WholeLineFundamentalMatrix u z 0 = 1 := by
  simpa using l2WholeLineFundamentalMatrix_int u z 0

/-- Every whole closed period has its exact translated solution formula;
the right endpoint agrees with the next period. -/
theorem l2WholeLineFundamentalMatrix_on_period (u : IntervalPairL2) (z : ℂ)
    (n : ℤ) (t : ℝ) (ht : t ∈ Icc (n : ℝ) ((n : ℝ)+1)) :
    l2WholeLineFundamentalMatrix u z t =
      l2FundamentalMatrix u z ⟨t-n,by constructor <;> linarith [ht.1,ht.2]⟩ *
        ((l2MonodromyUnit u z)^n : (Matrix (Fin 2) (Fin 2) ℂ)ˣ) := by
  by_cases he : t = (n : ℝ)+1
  · have htn : t = ((n+1 : ℤ) : ℝ) := by simpa using he
    have hr : (⟨t-n,by constructor <;> linarith [ht.1,ht.2]⟩ : Icc (0 : ℝ) 1) =
        ⟨1,by constructor <;> norm_num⟩ := by
      apply Subtype.ext
      dsimp
      linarith
    rw [hr,htn,l2WholeLineFundamentalMatrix_int,show n+1 = 1+n by omega,_root_.zpow_one_add]
    simp only [Units.val_mul,coe_l2MonodromyUnit]
    rfl
  · have hf : ⌊t⌋ = n := Int.floor_eq_iff.mpr ⟨ht.1,lt_of_le_of_ne ht.2 he⟩
    unfold l2WholeLineFundamentalMatrix
    rw [hf]
    congr 2
    apply Subtype.ext
    simp [l2WholeLinePeriodTime,Int.fract,hf]

/-- Restricting to nonnegative times recovers the previously constructed solution. -/
theorem l2WholeLineFundamentalMatrix_nonneg (u : IntervalPairL2) (z : ℂ)
    (t : Ici (0 : ℝ)) :
    l2WholeLineFundamentalMatrix u z t.val = l2PeriodicFundamentalMatrix u z t := by
  let n : ℕ := ⌊t.val⌋₊
  have ht : t.val ∈ Icc (n : ℝ) ((n : ℝ)+1) :=
    ⟨Nat.floor_le t.property,(Nat.lt_floor_add_one t.val).le⟩
  rw [l2PeriodicFundamentalMatrix_on_period u z n t ht,
    l2WholeLineFundamentalMatrix_on_period u z (n : ℤ) t.val (by simpa using ht)]
  simp

/-- Every integer translation is governed by the same physical monodromy. -/
theorem l2WholeLineFundamentalMatrix_add_int (u : IntervalPairL2) (z : ℂ)
    (t : ℝ) (n : ℤ) :
    l2WholeLineFundamentalMatrix u z (t+n) = l2WholeLineFundamentalMatrix u z t *
      ((l2MonodromyUnit u z)^n : (Matrix (Fin 2) (Fin 2) ℂ)ˣ) := by
  have ht : l2WholeLinePeriodTime (t+n) = l2WholeLinePeriodTime t := by
    apply Subtype.ext
    simp [l2WholeLinePeriodTime]
  simp only [l2WholeLineFundamentalMatrix,ht,Int.floor_add_intCast,_root_.zpow_add,
    Units.val_mul,Matrix.mul_assoc]

private theorem locallyFinite_wholeLine_period_strips :
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

/-- The physical continuation is continuous at all times, including
every seam between positive or negative periods. -/
theorem continuous_l2WholeLineFundamentalMatrix (u : IntervalPairL2) (z : ℂ) :
    Continuous (l2WholeLineFundamentalMatrix u z) := by
  apply locallyFinite_wholeLine_period_strips.continuous
  · ext t
    simp only [mem_iUnion,mem_Icc,mem_univ,iff_true]
    exact ⟨⌊t⌋,Int.floor_le t,(Int.lt_floor_add_one t).le⟩
  · intro n
    exact isClosed_Icc
  · intro n
    let r : ℝ → Icc (0 : ℝ) 1 := fun t => projIcc 0 1 (by norm_num) (t-n)
    have hr : Continuous r := continuous_projIcc.comp (continuous_id.sub continuous_const)
    have hM := continuous_l2FundamentalMatrix_time_joint.comp
      (continuous_const.prodMk hr (f := fun _ : ℝ => (z,u)))
    apply (hM.mul (continuous_const (y := (((l2MonodromyUnit u z)^n :
      (Matrix (Fin 2) (Fin 2) ℂ)ˣ) : Matrix (Fin 2) (Fin 2) ℂ)))).continuousOn.congr
    intro t ht
    rw [l2WholeLineFundamentalMatrix_on_period u z n t ht]
    congr 2
    apply Subtype.ext
    have hm : t-(n : ℝ) ∈ Icc (0 : ℝ) 1 := by constructor <;> linarith [ht.1,ht.2]
    exact congrArg Subtype.val (projIcc_of_mem (by norm_num) hm).symm

end NLS.ZakharovShabat
