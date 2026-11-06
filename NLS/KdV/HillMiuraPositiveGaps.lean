import NLS.KdV.MiuraRealSource
import NLS.ZakharovShabat.SourceCriticalPointsAnalytic
import NLS.ZakharovShabat.CanonicalCriticalFree
import NLS.SequenceSpaces.ContinuousOrderedRootIndex

/-! # Every positive-index real Miura gap lies strictly to the right of zero

The actual diagonal Dirac trace is even, so zero is always critical.
Continuous strictly ordered critical coordinates retain its index along
the real scaling path from the free source. Thus the zero-index gap
contains zero; strict periodic gap separation proves positivity at every
positive index, without a high-frequency cutoff.
-/
noncomputable section
set_option autoImplicit false
open Set Complex Filter Topology
open scoped ENNReal
namespace NLS.KdV
open NLS.ZakharovShabat

theorem hillMiuraFrequencyTrace_deriv_zero (u : Coeff 2) :
    deriv (hillMiuraFrequencyTrace u) 0 = 0 := by
  have ha : AnalyticAt ℂ (hillMiuraFrequencyTrace u) 0 :=
    (analyticOnNhd_hillMiuraFrequencyTrace_joint (0,u) (mem_univ _)).comp
      (f := fun z : ℂ => (z,u)) (analyticAt_id.prod analyticAt_const)
  have hd := ha.differentiableAt.hasDerivAt
  have hn := hd.comp_of_eq (h := fun z : ℂ => -z) 0 (hasDerivAt_id (0 : ℂ)).neg (by simp)
  have he : (fun z => hillMiuraFrequencyTrace u (-z)) = hillMiuraFrequencyTrace u :=
    funext (hillMiuraFrequencyTrace_even u)
  dsimp only [Function.comp_def] at hn
  rw [he] at hn
  have h := hn.unique hd
  have htwo : (2 : ℂ)*deriv (hillMiuraFrequencyTrace u) 0 = 0 := by
    linear_combination -h
  exact (mul_eq_zero.mp htwo).resolve_left (by norm_num)

theorem hillMiuraCanonicalCritical_zero (u : PeriodOneRealL2) :
    canonicalCriticalPoints (by simp) (by norm_num)
      (periodOnePotential (hillMiuraDiagonal u.val)) (periodOnePotential_mem _) 0 = 0 := by
  let ψ : ℝ → realTypeSourceSubmodule 2 := fun s => s • hillMiuraRealSource u
  have hψ : Continuous (fun s : ℝ => (ψ s).val) :=
    continuous_subtype_val.comp (continuous_id.smul continuous_const)
  let f : ℝ → ℤ → ℝ := fun s n =>
    (canonicalCriticalPoints (by simp) (by norm_num)
      (periodOnePotential (ψ s).val) (periodOnePotential_mem _) n).re
  have hf (n : ℤ) : Continuous (fun s => f s n) := by
    apply continuous_iff_continuousAt.mpr
    intro s
    exact continuous_re.continuousAt.comp
      (((analyticAt_sourceCanonicalCriticalPoint_of_realType (by simp) (by norm_num)
        n (ψ s).val (ψ s).property).continuousAt).comp
          (f := fun t : ℝ => (ψ t).val) hψ.continuousAt)
  have hstrict (s : ℝ) : StrictMono (f s) :=
    strictMono_canonicalCriticalPoints_re_of_realType (by simp) (by norm_num)
      (periodOnePotential (ψ s).val) (periodOnePotential_mem _)
      (isRealType_periodOnePotential (ψ s).val (ψ s).property)
  have hzero (s : ℝ) : deriv (canonicalDiscriminant (by simp) (periodOnePotential (ψ s).val)) 0 = 0 := by
    have hdiag : (ψ s).val = hillMiuraDiagonal (s • u.val) := by
      change s • hillMiuraDiagonal u.val = hillMiuraDiagonal (s • u.val)
      exact ((hillMiuraDiagonal.restrictScalars ℝ).map_smul s u.val).symm
    rw [hdiag]
    exact hillMiuraFrequencyTrace_deriv_zero (s • u.val)
  have hex (s : ℝ) : ∃ n : ℤ, f s n = 0 := by
    obtain ⟨n,hn⟩ := (canonicalCriticalPoints_exhaustive (by simp) (by norm_num)
      (periodOnePotential (ψ s).val) (periodOnePotential_mem _) 0).mp (hzero s)
    exact ⟨n,congrArg Complex.re hn⟩
  have hbase : f 0 0 = 0 := by
    dsimp only [f,ψ]
    simp only [zero_smul,Submodule.coe_zero,map_zero,canonicalCriticalPoints_zero,
      Int.cast_zero,mul_zero,zero_re]
  have hfzero := continuous_ordered_root_eq_on_connected f hf hstrict 0 hex 0 0 hbase 1
  have hψone : (ψ 1).val = hillMiuraDiagonal u.val := by simp [ψ,hillMiuraRealSource]
  have hre : (canonicalCriticalPoints (by simp) (by norm_num)
      (periodOnePotential (hillMiuraDiagonal u.val)) (periodOnePotential_mem _) 0).re = 0 := by
    change (canonicalCriticalPoints (by simp) (by norm_num)
      (periodOnePotential (ψ 1).val) (periodOnePotential_mem _) 0).re = 0 at hfzero
    rwa [hψone] at hfzero
  apply Complex.ext hre
  exact canonicalCriticalPoints_im_eq_zero (by simp) (by norm_num)
    (periodOnePotential (hillMiuraDiagonal u.val)) (periodOnePotential_mem _)
    (isRealType_periodOnePotential _ (hillMiuraRealSource u).property) 0

theorem hillMiura_gap_zero_contains_zero (u : PeriodOneRealL2) :
    0 ∈ Icc
      (canonicalPeriodicLeft (by simp) (by norm_num)
        (periodOnePotential (hillMiuraDiagonal u.val)) (periodOnePotential_mem _) 0).re
      (canonicalPeriodicRight (by simp) (by norm_num)
        (periodOnePotential (hillMiuraDiagonal u.val)) (periodOnePotential_mem _) 0).re := by
  have h := canonicalCriticalPoints_mem_canonicalPeriodicGap (by simp) (by norm_num)
    (periodOnePotential (hillMiuraDiagonal u.val)) (periodOnePotential_mem _)
    (isRealType_periodOnePotential _ (hillMiuraRealSource u).property) 0
  rw [hillMiuraCanonicalCritical_zero,zero_re] at h
  exact h

theorem hillMiura_positive_gap_left_pos (u : PeriodOneRealL2) (n : ℤ) (hn : 0 < n) :
    0 < (canonicalPeriodicLeft (by simp) (by norm_num)
      (periodOnePotential (hillMiuraDiagonal u.val)) (periodOnePotential_mem _) n).re := by
  have h := canonicalPeriodicRight_re_lt_left_of_lt (by simp) (by norm_num)
    (periodOnePotential (hillMiuraDiagonal u.val)) (periodOnePotential_mem _)
    (isRealType_periodOnePotential _ (hillMiuraRealSource u).property) hn
  exact (hillMiura_gap_zero_contains_zero u).2.trans_lt h

theorem hillMiura_negative_gap_right_neg (u : PeriodOneRealL2) (n : ℤ) (hn : n < 0) :
    (canonicalPeriodicRight (by simp) (by norm_num)
      (periodOnePotential (hillMiuraDiagonal u.val)) (periodOnePotential_mem _) n).re < 0 := by
  have h := canonicalPeriodicRight_re_lt_left_of_lt (by simp) (by norm_num)
    (periodOnePotential (hillMiuraDiagonal u.val)) (periodOnePotential_mem _)
    (isRealType_periodOnePotential _ (hillMiuraRealSource u).property) hn
  exact h.trans_le (hillMiura_gap_zero_contains_zero u).1

end NLS.KdV
