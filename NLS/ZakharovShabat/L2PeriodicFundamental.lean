import NLS.ZakharovShabat.L2FundamentalAnalytic
import Mathlib.Topology.LocallyFinite

/-! # Periodic continuation of the physical L2 fundamental matrix

On the n-th period the matrix is the original unit-interval matrix times
its monodromy to the n-th power. The closed-interval formula includes
both endpoints, so adjacent periods agree at their common boundary.
-/
noncomputable section
open Set Complex Filter Topology
open NLS.LinearVolterra
open scoped Matrix.Norms.Elementwise
namespace NLS.ZakharovShabat

/-- The actual monodromy of the original physical L2 solution. -/
def l2Monodromy (u : IntervalPairL2) (z : ℂ) : Matrix (Fin 2) (Fin 2) ℂ :=
  l2FundamentalMatrix u z ⟨1,by constructor <;> norm_num⟩

/-- The time inside a unit period, with the right endpoint assigned to the next period. -/
def l2PeriodTime (t : Ici (0 : ℝ)) : Icc (0 : ℝ) 1 :=
  ⟨t.val-(⌊t.val⌋₊ : ℝ),sub_nonneg.mpr (Nat.floor_le t.property),
    (by have h := Nat.lt_floor_add_one t.val; linarith)⟩

/-- Continuation by the actual monodromy, for all nonnegative times. -/
def l2PeriodicFundamentalMatrix (u : IntervalPairL2) (z : ℂ) (t : Ici (0 : ℝ)) :
    Matrix (Fin 2) (Fin 2) ℂ :=
  l2FundamentalMatrix u z (l2PeriodTime t)*l2Monodromy u z ^ ⌊t.val⌋₊

@[simp] theorem l2PeriodicFundamentalMatrix_nat (u : IntervalPairL2) (z : ℂ) (n : ℕ) :
    l2PeriodicFundamentalMatrix u z ⟨(n : ℝ),by change 0 ≤ (n : ℝ); positivity⟩ = l2Monodromy u z ^ n := by
  have ht : l2PeriodTime ⟨(n : ℝ),by change 0 ≤ (n : ℝ); positivity⟩ = ⟨0,by constructor <;> norm_num⟩ := by
    apply Subtype.ext
    simp [l2PeriodTime]
  simp [l2PeriodicFundamentalMatrix,ht]

@[simp] theorem l2PeriodicFundamentalMatrix_zero (u : IntervalPairL2) (z : ℂ) :
    l2PeriodicFundamentalMatrix u z ⟨0,by simp⟩ = 1 := by
  simpa only [Nat.cast_zero,pow_zero] using l2PeriodicFundamentalMatrix_nat u z 0

/-- The local formula is valid on each whole closed period, including the seam. -/
theorem l2PeriodicFundamentalMatrix_on_period (u : IntervalPairL2) (z : ℂ)
    (n : ℕ) (t : Ici (0 : ℝ)) (ht : t.val ∈ Icc (n : ℝ) ((n : ℝ)+1)) :
    l2PeriodicFundamentalMatrix u z t =
      l2FundamentalMatrix u z ⟨t.val-n,by constructor <;> linarith [ht.1,ht.2]⟩*
        l2Monodromy u z ^ n := by
  by_cases he : t.val = (n : ℝ)+1
  · have htn : t = ⟨((n+1 : ℕ) : ℝ),by change 0 ≤ ((n+1 : ℕ) : ℝ); positivity⟩ := by
      apply Subtype.ext
      simpa using he
    have hr : (⟨t.val-n,by constructor <;> linarith [ht.1,ht.2]⟩ : Icc (0 : ℝ) 1) =
        ⟨1,by constructor <;> norm_num⟩ := by
      apply Subtype.ext
      dsimp
      linarith
    rw [hr,htn,l2PeriodicFundamentalMatrix_nat,pow_succ']
    rfl
  · have hf : ⌊t.val⌋₊ = n := (Nat.floor_eq_iff t.property).mpr ⟨ht.1,lt_of_le_of_ne ht.2 he⟩
    unfold l2PeriodicFundamentalMatrix
    rw [hf]
    congr 2
    apply Subtype.ext
    simp [l2PeriodTime,hf]

/-- The continuation recovers the original matrix throughout the first closed interval. -/
theorem l2PeriodicFundamentalMatrix_unit (u : IntervalPairL2) (z : ℂ) (t : Icc (0 : ℝ) 1) :
    l2PeriodicFundamentalMatrix u z ⟨t.val,t.property.1⟩ = l2FundamentalMatrix u z t := by
  have h := l2PeriodicFundamentalMatrix_on_period u z 0 ⟨t.val,t.property.1⟩ (by simpa only [Nat.cast_zero,zero_add] using t.property)
  simpa using h

@[simp] theorem det_l2Monodromy (u : IntervalPairL2) (z : ℂ) : (l2Monodromy u z).det = 1 :=
  det_l2FundamentalMatrix u z _

@[simp] theorem det_l2PeriodicFundamentalMatrix (u : IntervalPairL2) (z : ℂ) (t : Ici (0 : ℝ)) :
    (l2PeriodicFundamentalMatrix u z t).det = 1 := by
  simp [l2PeriodicFundamentalMatrix,Matrix.det_mul,Matrix.det_pow]

private theorem locallyFinite_period_strips :
    LocallyFinite (fun n : ℕ => Icc (n : ℝ) ((n : ℝ)+1)) := by
  intro x
  refine ⟨Iio (x+1),Iio_mem_nhds (by linarith),?_⟩
  apply (Set.finite_Iic ⌈x+1⌉₊).subset
  rintro n ⟨y,hy,hyx⟩
  have hn : (n : ℝ) ≤ (⌈x+1⌉₊ : ℝ) := (hy.1.trans hyx.le).trans (Nat.le_ceil _)
  exact_mod_cast hn

/-- Joint continuity in the physical L2 potential, frequency, and every nonnegative time. -/
theorem continuous_l2PeriodicFundamentalMatrix_joint :
    Continuous (fun qt : (ℂ × IntervalPairL2) × Ici (0 : ℝ) =>
      l2PeriodicFundamentalMatrix qt.1.2 qt.1.1 qt.2) := by
  let time : (ℂ × IntervalPairL2) × Ici (0 : ℝ) → ℝ := fun qt => qt.2.val
  have htime : Continuous time := continuous_subtype_val.comp continuous_snd
  have hloc := locallyFinite_period_strips.preimage_continuous htime
  apply hloc.continuous
  · ext qt
    simp only [mem_iUnion,mem_preimage,mem_Icc,mem_univ,iff_true]
    exact ⟨⌊qt.2.val⌋₊,Nat.floor_le qt.2.property,(Nat.lt_floor_add_one qt.2.val).le⟩
  · intro n
    exact isClosed_Icc.preimage htime
  · intro n
    let r : (ℂ × IntervalPairL2) × Ici (0 : ℝ) → Icc (0 : ℝ) 1 :=
      fun qt => projIcc 0 1 (by norm_num) (time qt-n)
    have hr : Continuous r := continuous_projIcc.comp (htime.sub continuous_const)
    have hM := continuous_l2FundamentalMatrix_time_joint.comp (continuous_fst.prodMk hr)
    have hB : Continuous (fun qt : (ℂ × IntervalPairL2) × Ici (0 : ℝ) => l2Monodromy qt.1.2 qt.1.1) := by
      unfold l2Monodromy
      have hc : Continuous (fun qt : (ℂ × IntervalPairL2) × Ici (0 : ℝ) =>
          (qt.1,(⟨1,by constructor <;> norm_num⟩ : Icc (0 : ℝ) 1))) :=
        continuous_fst.prodMk continuous_const
      have h := continuous_l2FundamentalMatrix_time_joint.comp hc
      exact h
    apply (hM.mul (hB.pow n)).continuousOn.congr
    intro qt hqt
    have ht : qt.2.val ∈ Icc (n : ℝ) ((n : ℝ)+1) := hqt
    change l2PeriodicFundamentalMatrix qt.1.2 qt.1.1 qt.2 =
      l2FundamentalMatrix qt.1.2 qt.1.1 (r qt)*l2Monodromy qt.1.2 qt.1.1 ^ n
    rw [l2PeriodicFundamentalMatrix_on_period _ _ n _ ht]
    congr 2
    apply Subtype.ext
    have hm : qt.2.val-(n : ℝ) ∈ Icc (0 : ℝ) 1 := by
      constructor <;> linarith [ht.1,ht.2]
    exact congrArg Subtype.val (projIcc_of_mem (by norm_num) hm).symm

/-- Analyticity of the actual physical L2 monodromy. -/
theorem analyticOnNhd_l2Monodromy_joint :
    AnalyticOnNhd ℂ (fun q : ℂ × IntervalPairL2 => l2Monodromy q.2 q.1) univ :=
  analyticOnNhd_l2FundamentalMatrix_joint _

private theorem analyticAt_matrix_mul {f g : (ℂ × IntervalPairL2) → Matrix (Fin 2) (Fin 2) ℂ}
    {q : ℂ × IntervalPairL2} (hf : AnalyticAt ℂ f q) (hg : AnalyticAt ℂ g q) :
    AnalyticAt ℂ (fun r => f r*g r) q := by
  apply AnalyticAt.pi
  intro i
  apply AnalyticAt.pi
  intro j
  change AnalyticAt ℂ (fun r => ∑ k : Fin 2, f r i k*g r k j) q
  exact Finset.analyticAt_fun_sum _ (fun k _ =>
    (analyticAt_pi_iff.mp (analyticAt_pi_iff.mp hf i) k).mul
      (analyticAt_pi_iff.mp (analyticAt_pi_iff.mp hg k) j))

/-- Fixed-time joint analyticity holds at every nonnegative time, including integer times. -/
theorem analyticOnNhd_l2PeriodicFundamentalMatrix_joint (t : Ici (0 : ℝ)) :
    AnalyticOnNhd ℂ (fun q : ℂ × IntervalPairL2 => l2PeriodicFundamentalMatrix q.2 q.1 t) univ := by
  intro q _
  have hB := analyticOnNhd_l2Monodromy_joint q (mem_univ _)
  have hp (n : ℕ) : AnalyticAt ℂ (fun r : ℂ × IntervalPairL2 => l2Monodromy r.2 r.1 ^ n) q := by
    induction n with
    | zero => simpa only [pow_zero] using (analyticAt_const : AnalyticAt ℂ (fun _ : ℂ × IntervalPairL2 => (1 : Matrix (Fin 2) (Fin 2) ℂ)) q)
    | succ n ih =>
      simp only [pow_succ]
      exact analyticAt_matrix_mul ih hB
  exact analyticAt_matrix_mul
    (analyticOnNhd_l2FundamentalMatrix_joint (l2PeriodTime t) q (mem_univ _)) (hp _)

/-- The continued matrix obeys the original monodromy relation after any whole number of periods. -/
theorem l2PeriodicFundamentalMatrix_add_nat (u : IntervalPairL2) (z : ℂ)
    (t : Ici (0 : ℝ)) (n : ℕ) :
    l2PeriodicFundamentalMatrix u z ⟨t.val+n,by change 0 ≤ t.val+(n : ℝ); exact add_nonneg t.property (Nat.cast_nonneg n)⟩ =
      l2PeriodicFundamentalMatrix u z t*l2Monodromy u z ^ n := by
  have hf := Nat.floor_add_natCast (show 0 ≤ t.val from t.property) n
  have hr : l2PeriodTime ⟨t.val+n,by change 0 ≤ t.val+(n : ℝ); exact add_nonneg t.property (Nat.cast_nonneg n)⟩ = l2PeriodTime t := by
    apply Subtype.ext
    dsimp [l2PeriodTime]
    rw [hf,Nat.cast_add]
    ring
  simp only [l2PeriodicFundamentalMatrix,hr,hf,pow_add,mul_assoc]

end NLS.ZakharovShabat
