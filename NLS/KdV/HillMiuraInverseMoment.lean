import NLS.KdV.HillMiuraCentralMean
import NLS.SequenceSpaces.PhysicalHilbertQuadratic
import NLS.ZakharovShabat.SourceFiniteGapInverseMoment

/-! Actual zero-mean diagonal Dirac sources have no central inverse-moment
pole. Their finite-gap inverse moment balance recovers the ORIGINAL lift
L2 squared norm, with all signed original gap indices retained. -/
noncomputable section
open Set Metric Complex NLS.ZakharovShabat NLS.ComplexAnalysis
namespace NLS.KdV

theorem hillMiura_mean_zero_central_data (u : PeriodOneRealL2) (hu : u.val 0=0) :
    canonicalPeriodicGap (by simp) (by norm_num) (periodOnePotential (hillMiuraDiagonal u.val))
      (periodOnePotential_mem _) 0=0 ∧
    (0:ℂ) ∈ ({canonicalPeriodicLeft (by simp) (by norm_num) (periodOnePotential (hillMiuraDiagonal u.val))
      (periodOnePotential_mem _) 0,
      canonicalPeriodicRight (by simp) (by norm_num) (periodOnePotential (hillMiuraDiagonal u.val))
      (periodOnePotential_mem _) 0} : Set ℂ) := by
  have hlr := (hillMiura_central_gap_collapsed_iff_mean_zero u).mpr hu
  have hr := (hillMiura_central_right_zero_iff_mean_zero u).mpr hu
  constructor
  · change hillMiuraDiracRight u.val 0-hillMiuraDiracLeft u.val 0=0
    exact sub_eq_zero.mpr hlr.symm
  · change (0:ℂ) ∈ ({hillMiuraDiracLeft u.val 0,hillMiuraDiracRight u.val 0} : Set ℂ)
    exact Set.mem_insert_of_mem _ (Set.mem_singleton_iff.mpr hr.symm)

variable {W : Set (CoeffPair 2)}

theorem hillMiura_fullPrimitive_zero_of_mean_zero
    (C : SourceFullAbelianUniformCauchyFamily (by simp) (by norm_num) W)
    (u : PeriodOneRealL2) (hu : u.val 0=0)
    (hC : hillMiuraDiagonal u.val ∈ ball C.discs.source.val C.discs.sourceRadius) :
    sourceFullAbelianPrimitive (by simp) (by norm_num) W 0 (0,hillMiuraDiagonal u.val)=0 := by
  have hd := hillMiura_mean_zero_central_data u hu
  exact (C.central_zero_value_and_mem _ hC hd.1 hd.2).1

theorem analytic_hillMiura_filled_inverse_square
    (C : SourceFullAbelianUniformCauchyFamily (by simp) (by norm_num) W)
    (u : PeriodOneRealL2) (hu : u.val 0=0)
    (hC : hillMiuraDiagonal u.val ∈ ball C.discs.source.val C.discs.sourceRadius) :
    AnalyticOnNhd ℂ
      (filledSquareOverZero (fun z => sourceFullAbelianPrimitive (by simp) (by norm_num) W 0 (z,hillMiuraDiagonal u.val)))
      (sourceOpenGapComplement (by simp) (by norm_num) (hillMiuraDiagonal u.val)) := by
  have hd := hillMiura_mean_zero_central_data u hu
  exact C.analytic_filled_inverse_square_of_central_zero (hillMiuraRealSource u) hC hd.1 hd.2

/-- The physical inverse moment balance at a genuine finite-gap lift.
It is an exact contour identity, not yet the action coercivity inequality. -/
theorem hillMiura_finiteGap_inverse_moment_norm_sq
    (C : SourceFullAbelianUniformCauchyFamily (by simp) (by norm_num) W)
    (u : PeriodOneRealL2) (hu : u.val 0=0)
    (hC : hillMiuraDiagonal u.val ∈ ball C.discs.source.val C.discs.sourceRadius)
    (hf : hillMiuraRealSource u ∈ sourceFiniteGapLocus (by simp) (by norm_num)) :
    ((‖u.val‖^2:ℝ):ℂ) =
      -∑ n ∈ hf.toFinset, (n:ℂ)*(∮ z in C(C.discs.center n,(C.discs.inner n+C.discs.outer n)/2),
        sourceFullAbelianPrimitive (by simp) (by norm_num) W n (z,hillMiuraDiagonal u.val)/z) := by
  have hd := hillMiura_mean_zero_central_data u hu
  have he := sourceFiniteGap_inverse_moment_balance C (hillMiuraRealSource u) hC hf hd.1 hd.2
  have hm : (∑' k : ℤ, (hillMiuraRealSource u).val.fst k*(hillMiuraRealSource u).val.snd (-k))=
      ((‖u.val‖^2:ℝ):ℂ) := by
    change (∑' k : ℤ, (hillMiuraDiagonal u.val).fst k*(hillMiuraDiagonal u.val).snd (-k))=_
    rw [hillMiuraDiagonal_fst,hillMiuraDiagonal_snd,← Coeff.oppositeHilbertPairing_apply]
    exact Coeff.oppositeHilbertPairing_self_eq_norm_sq _ u.property
  rw [hm] at he
  exact he

end NLS.KdV
