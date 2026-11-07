import NLS.KdV.HillHminusOneMiuraRealActionFamilies
import NLS.ZakharovShabat.SourcePositivePeriodCircle

/-! # Positive-gap Miura actions and their actual winding-one contours

For any real diagonal Miura source, positivity of the selected left
Dirac endpoint suffices to construct a valid positive isolating circle.
The actual mapped Hill contour computes the indexed Miura action with
winding one. Mean-value comparison with the ordinary Dirac action gives
real bounds and zero detection, including collapsed gaps. Identification
of every original Hill slot with a positive Dirac slot remains separate.
-/
noncomputable section
set_option autoImplicit false
open Set Metric Complex NLS.ComplexAnalysis NLS.ZakharovShabat
open scoped ENNReal
namespace NLS.KdV

theorem hillHminusMiuraIndexedAction_bounds (u : PeriodOneRealL2) (n : ℤ) :
    let ψ := hillMiuraDiagonal u.val
    let l := canonicalPeriodicLeft (by simp) (by norm_num) (periodOnePotential ψ) (periodOnePotential_mem ψ) n
    let r := canonicalPeriodicRight (by simp) (by norm_num) (periodOnePotential ψ) (periodOnePotential_mem ψ) n
    let I := sourceIndexedAction (by simp) (by norm_num) n ψ
    2*l.re*I.re ≤ (hillHminusMiuraIndexedAction u.val n).re ∧
      (hillHminusMiuraIndexedAction u.val n).re ≤ 2*r.re*I.re := by
  let φ := hillMiuraRealSource u
  obtain ⟨ζ,hζ,he⟩ := sourceIndexedHigherAction_eq_power_mul_action (by simp) (by norm_num) φ n 1
  dsimp only [φ,hillMiuraRealSource] at he hζ
  have heR := congrArg Complex.re he
  simp only [pow_one,mul_re,ofReal_re,ofReal_im,zero_mul,sub_zero] at heR
  have hI := (sourceIndexedAction_nonneg_and_eq_zero_iff_gap_zero
    (by simp) (by norm_num) n φ.val φ.property).1
  dsimp only [φ,hillMiuraRealSource] at hI
  have hJ : (hillHminusMiuraIndexedAction u.val n).re =
      2*ζ*(sourceIndexedAction (by simp) (by norm_num) n (hillMiuraDiagonal u.val)).re := by
    unfold hillHminusMiuraIndexedAction
    simp only [mul_re]
    norm_num
    rw [heR]
    ring
  dsimp only
  rw [hJ]
  constructor <;> nlinarith [mul_le_mul_of_nonneg_right hζ.1 hI,
    mul_le_mul_of_nonneg_right hζ.2 hI]

theorem hillHminusMiuraIndexedAction_eq_zero_iff_of_positive_left
    (u : PeriodOneRealL2) (n : ℤ)
    (hpos : 0 < (canonicalPeriodicLeft (by simp) (by norm_num)
      (periodOnePotential (hillMiuraDiagonal u.val)) (periodOnePotential_mem _) n).re) :
    hillHminusMiuraIndexedAction u.val n = 0 ↔
      canonicalPeriodicGap (by simp) (by norm_num)
        (periodOnePotential (hillMiuraDiagonal u.val)) (periodOnePotential_mem _) n = 0 := by
  let φ := hillMiuraRealSource u
  obtain ⟨ζ,hζ,he⟩ := sourceIndexedHigherAction_eq_power_mul_action (by simp) (by norm_num) φ n 1
  dsimp only [φ,hillMiuraRealSource] at he hζ
  have hζpos : 0 < ζ := hpos.trans_le hζ.1
  have hζne : (ζ : ℂ) ≠ 0 := by exact_mod_cast hζpos.ne'
  have hzero : hillHminusMiuraIndexedAction u.val n = 0 ↔
      sourceIndexedAction (by simp) (by norm_num) n (hillMiuraDiagonal u.val) = 0 := by
    unfold hillHminusMiuraIndexedAction
    rw [he,pow_one]
    simp only [mul_eq_zero,OfNat.ofNat_ne_zero,hζne,false_or]
  have hg := (sourceIndexedAction_nonneg_and_eq_zero_iff_gap_zero
    (by simp) (by norm_num) n φ.val φ.property).2.2
  have hegap := sourcePeriodicGapDisplacement_apply (by simp) (by norm_num) (hillMiuraDiagonal u.val) n
  exact hzero.trans (hg.trans ⟨fun h => hegap.symm.trans h,fun h => hegap.trans h⟩)

theorem hillHminusMiuraIndexedAction_pos_of_positive_left
    (u : PeriodOneRealL2) (n : ℤ)
    (hpos : 0 < (canonicalPeriodicLeft (by simp) (by norm_num)
      (periodOnePotential (hillMiuraDiagonal u.val)) (periodOnePotential_mem _) n).re)
    (hgap : canonicalPeriodicGap (by simp) (by norm_num)
      (periodOnePotential (hillMiuraDiagonal u.val)) (periodOnePotential_mem _) n ≠ 0) :
    0 < (hillHminusMiuraIndexedAction u.val n).re := by
  let φ := hillMiuraRealSource u
  have hI := sourceIndexedAction_nonneg_and_eq_zero_iff_gap_zero
    (by simp) (by norm_num) n φ.val φ.property
  dsimp only [φ,hillMiuraRealSource] at hI
  have hne : sourceIndexedAction (by simp) (by norm_num) n φ.val ≠ 0 := by
    intro h
    have hz : sourcePeriodicGapDisplacement (by simp) (by norm_num) (hillMiuraDiagonal u.val) n = 0 := hI.2.2.mp h
    exact hgap ((sourcePeriodicGapDisplacement_apply (by simp) (by norm_num)
      (hillMiuraDiagonal u.val) n).symm.trans hz)
  have hIpos : 0 < (sourceIndexedAction (by simp) (by norm_num) n φ.val).re := by
    apply lt_of_le_of_ne hI.1
    intro h
    apply hne
    apply Complex.ext
    · exact h.symm
    · exact hI.2.1
  have hb := (hillHminusMiuraIndexedAction_bounds u n).1
  exact lt_of_lt_of_le (mul_pos (mul_pos (by norm_num) hpos) hIpos) hb

theorem exists_positive_miura_action_contour
    (q : PeriodOneHminusOne) (u : PeriodOneRealL2) (c : ℝ)
    (himage : periodOneMiura u.val = q+periodOneL2Inclusion (lp.single 2 0 (c : ℂ)))
    (W : Set (CoeffPair 2))
    (D : SourceAbelianSpectralChart (by simp) (by norm_num) W (hillMiuraDiagonal u.val))
    (n : ℤ)
    (hpos : 0 < (canonicalPeriodicLeft (by simp) (by norm_num)
      (periodOnePotential (hillMiuraDiagonal u.val)) (periodOnePotential_mem _) n).re) :
    ∃ C : SourceCriticalRootPeriodCircle (by simp) (by norm_num) (hillMiuraDiagonal u.val) n,
      0 < C.center-C.radius ∧
      hillHminusMiuraContourAction q u.val (c : ℂ)
        (quadraticEnergyLoop (PiecewiseC1Loop.circle (C.center : ℂ) C.radius) (c : ℂ)) =
        hillHminusMiuraIndexedAction u.val n ∧
      (quadraticEnergyLoop (PiecewiseC1Loop.circle (C.center : ℂ) C.radius) (c : ℂ)).windingIntegral
        ((sourceStandardRootMidpoint (by simp) (by norm_num) (hillMiuraDiagonal u.val) n)^2-(c : ℂ)) = 1 := by
  obtain ⟨C,hC⟩ := exists_positive_sourceCriticalRootPeriodCircle
    (by simp) (by norm_num) (hillMiuraDiagonal u.val) (hillMiuraRealSource u).property n hpos
  exact ⟨C,hC,hillHminusMiuraContourAction_eq_indexed q u.val (c : ℂ) himage W D n C hC,
    winding_one_miura_action_contour u.val (c : ℂ) n C hC⟩

end NLS.KdV
