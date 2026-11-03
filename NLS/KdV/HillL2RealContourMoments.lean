import NLS.KdV.HillL2AllGapContourIntegrals
import NLS.KdV.HillL2RealCutDifferential
import NLS.KdV.HillL2HighGapMoments
import NLS.KdV.HillWeightedRealActions

/-! # Intrinsic actual contour actions at every real Hill gap

The polynomial moments of the globally normalized actual primitive
have both the source Arnold formula and the exact real gap formula,
with no high-index cutoff. At high gaps they agree with the existing
complex-potential analytic contour moments. The physical Birkhoff map
and Hamiltonian trace identities are separate obligations.
-/

noncomputable section
open Set Metric Complex Filter Topology MeasureTheory
namespace NLS.KdV
open NLS.ComplexAnalysis

def hillL2RealContourMoment
    (q : WeightedCoeff SpectralWeight.one.toWeight 2)
    (hq : SpectralWeight.one.toCoeff q ∈ Coeff.paritySubspace 0)
    (hr : IsRealHillPotential (SpectralWeight.one.toCoeff q)) (n m : ℕ) : ℂ :=
  -(Real.pi : ℂ)⁻¹ * ∮ z in C((hillRealGapCenter q hq hr n : ℂ),
      hillRealGapHalfLength q hq hr n + hillRealGapCollar q hq hr n),
    z ^ m * hillL2RealCutPrimitive (SpectralWeight.one.toCoeff q) z

theorem hillL2RealContourMoment_eq_gapIntegral
    (q : WeightedCoeff SpectralWeight.one.toWeight 2)
    (hq : SpectralWeight.one.toCoeff q ∈ Coeff.paritySubspace 0)
    (hr : IsRealHillPotential (SpectralWeight.one.toCoeff q)) (n : ℕ) (hn : 1 ≤ n) (m : ℕ) :
    hillL2RealContourMoment q hq hr n m = (hillRealGapIntegral q hq hr n m : ℂ) := by
  let c := (hillRealGapCenter q hq hr n : ℂ)
  let r := hillRealGapHalfLength q hq hr n + hillRealGapCollar q hq hr n
  obtain ⟨hd, hη, _⟩ := hillRealGapContour_geometry q hq hr n hn
  have hrpos : 0 < r := add_pos_of_nonneg_of_pos hd hη
  have hF : ContinuousOn (hillL2RealCutPrimitive (SpectralWeight.one.toCoeff q)) (sphere c r) :=
    (analyticOnNhd_hillL2RealCutPrimitive q hq hr).continuousOn.mono
      (hillRealGapContour_sphere_subset q hq hr n hn)
  have hi : CircleIntegrable (fun z => z ^ m * hillL2RealCutPrimitive (SpectralWeight.one.toCoeff q) z) c r :=
    ((continuousOn_id.pow m).mul hF).circleIntegrable hrpos.le
  have hp : CircleIntegrable (fun z : ℂ => I * (n : ℂ) * Real.pi * z ^ m) c r :=
    (continuousOn_const.mul (continuousOn_id.pow m)).circleIntegrable hrpos.le
  have hpoly : (∮ z in C(c, r), z ^ m) = 0 :=
    circleIntegral_eq_zero_of_differentiable_on_off_countable hrpos.le countable_empty
      (continuousOn_id.pow m) (fun z _ => differentiableAt_id.pow m)
  have hshift : (∮ z in C(c, r), z ^ m *
        (hillL2RealCutPrimitive (SpectralWeight.one.toCoeff q) z + I * (n : ℂ) * Real.pi)) =
      ∮ z in C(c, r), z ^ m * hillL2RealCutPrimitive (SpectralWeight.one.toCoeff q) z := by
    have he : (fun z : ℂ => z ^ m *
        (hillL2RealCutPrimitive (SpectralWeight.one.toCoeff q) z + I * (n : ℂ) * Real.pi)) =
        (fun z => z ^ m * hillL2RealCutPrimitive (SpectralWeight.one.toCoeff q) z +
          I * (n : ℂ) * Real.pi * z ^ m) := by funext z; ring
    rw [he, circleIntegral.integral_add hi hp, circleIntegral.integral_const_mul,
      hpoly, mul_zero, add_zero]
  have he := circleIntegral_hillL2RealCutPrimitive_shifted q hq hr n hn m
  rw [hshift] at he
  unfold hillL2RealContourMoment
  rw [he]
  unfold hillRealGapIntegral
  simp_rw [← ofReal_pow, ← ofReal_mul]
  rw [intervalIntegral.integral_ofReal]
  push_cast
  ring

theorem hillL2RealContourMoment_arnold_level
    (q : WeightedCoeff SpectralWeight.one.toWeight 2)
    (hq : SpectralWeight.one.toCoeff q ∈ Coeff.paritySubspace 0)
    (hr : IsRealHillPotential (SpectralWeight.one.toCoeff q)) (n : ℕ) (hn : 1 ≤ n) (m : ℕ) :
    hillL2RealContourMoment q hq hr n m = ((m + 1 : ℂ) * (Real.pi : ℂ))⁻¹ *
      ∮ z in C((hillRealGapCenter q hq hr n : ℂ),
          hillRealGapHalfLength q hq hr n + hillRealGapCollar q hq hr n),
        z ^ (m + 1) * deriv (hillL2Discriminant (SpectralWeight.one.toCoeff q)) z /
          hillL2RealCutRoot (SpectralWeight.one.toCoeff q) z := by
  let c := (hillRealGapCenter q hq hr n : ℂ)
  let r := hillRealGapHalfLength q hq hr n + hillRealGapCollar q hq hr n
  obtain ⟨hd, hη, _⟩ := hillRealGapContour_geometry q hq hr n hn
  have hrpos : 0 < r := add_pos_of_nonneg_of_pos hd hη
  have hs := hillRealGapContour_sphere_subset q hq hr n hn
  have hip := circleIntegral_pow_mul_deriv_eq_neg
    (hillL2RealCutPrimitive (SpectralWeight.one.toCoeff q)) (hillL2RealCutDomain q hq hr)
    (analyticOnNhd_hillL2RealCutPrimitive q hq hr) c r hrpos.le hs m
  have hi : (∮ z in C(c, r), z ^ (m + 1) *
        deriv (hillL2Discriminant (SpectralWeight.one.toCoeff q)) z /
          hillL2RealCutRoot (SpectralWeight.one.toCoeff q) z) =
      -(m + 1 : ℂ) * ∮ z in C(c, r), z ^ m * hillL2RealCutPrimitive (SpectralWeight.one.toCoeff q) z := by
    rw [← hip]
    apply circleIntegral.integral_congr hrpos.le
    intro z hz
    dsimp only
    rw [(hasDerivAt_hillL2RealCutPrimitive q hq hr z (hs hz)).deriv]
    exact mul_div_assoc _ _ _
  rw [hi]
  dsimp only [hillL2RealContourMoment, c, r]
  have hm : (m + 1 : ℂ) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero m
  have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  field_simp

theorem hillL2HighContourMoment_eq_realContourMoment
    (q : WeightedCoeff SpectralWeight.one.toWeight 2)
    (hq : SpectralWeight.one.toCoeff q ∈ Coeff.paritySubspace 0)
    (hr : IsRealHillPotential (SpectralWeight.one.toCoeff q)) (n : ℕ) (hn : 2 ≤ n)
    (hcut : 16 * ‖q‖ ≤ (n : ℝ)) (m : ℕ) :
    hillL2HighContourMoment n m (SpectralWeight.one.toCoeff q) = hillL2RealContourMoment q hq hr n m := by
  rw [hillL2HighContourMoment_eq_gapIntegral q hq hr n hn hcut,
    hillL2RealContourMoment_eq_gapIntegral q hq hr n (by omega)]

theorem hillL2RealContourMoment_nonneg_even
    (q : WeightedCoeff SpectralWeight.one.toWeight 2)
    (hq : SpectralWeight.one.toCoeff q ∈ Coeff.paritySubspace 0)
    (hr : IsRealHillPotential (SpectralWeight.one.toCoeff q)) (n : ℕ) (hn : 1 ≤ n) (m : ℕ) :
    0 ≤ (hillL2RealContourMoment q hq hr n (2 * m)).re := by
  rw [hillL2RealContourMoment_eq_gapIntegral q hq hr n hn, ofReal_re]
  exact hillRealGapIntegral_nonneg_even q hq hr n hn m

theorem hillL2RealContourMoment_pos_iff
    (q : WeightedCoeff SpectralWeight.one.toWeight 2)
    (hq : SpectralWeight.one.toCoeff q ∈ Coeff.paritySubspace 0)
    (hr : IsRealHillPotential (SpectralWeight.one.toCoeff q)) (n : ℕ) (hn : 1 ≤ n) :
    0 < (hillL2RealContourMoment q hq hr n 0).re ↔
      hillRealLabels q hq hr (2 * n - 1) < hillRealLabels q hq hr (2 * n) := by
  rw [hillL2RealContourMoment_eq_gapIntegral q hq hr n hn, ofReal_re]
  exact hillRealGapIntegral_pos_iff q hq hr n hn

theorem hillL2RealContourMoment_mean_value
    (q : WeightedCoeff SpectralWeight.one.toWeight 2)
    (hq : SpectralWeight.one.toCoeff q ∈ Coeff.paritySubspace 0)
    (hr : IsRealHillPotential (SpectralWeight.one.toCoeff q)) (n : ℕ) (hn : 1 ≤ n) (m : ℕ) :
    ∃ c ∈ Icc (hillRealLabels q hq hr (2 * n - 1)) (hillRealLabels q hq hr (2 * n)),
      hillL2RealContourMoment q hq hr n m = (c : ℂ) ^ m * hillL2RealContourMoment q hq hr n 0 := by
  obtain ⟨c, hc, he⟩ := hillRealGapIntegral_mean_value q hq hr n hn m
  refine ⟨c, hc, ?_⟩
  rw [hillL2RealContourMoment_eq_gapIntegral q hq hr n hn,
    hillL2RealContourMoment_eq_gapIntegral q hq hr n hn, he]
  push_cast
  rfl

theorem hillL2RealContourMoment_closed
    (q : WeightedCoeff SpectralWeight.one.toWeight 2)
    (hq : SpectralWeight.one.toCoeff q ∈ Coeff.paritySubspace 0)
    (hr : IsRealHillPotential (SpectralWeight.one.toCoeff q)) (n : ℕ) (hn : 1 ≤ n) (m : ℕ)
    (hc : hillRealLabels q hq hr (2 * n - 1) = hillRealLabels q hq hr (2 * n)) :
    hillL2RealContourMoment q hq hr n m = 0 := by
  rw [hillL2RealContourMoment_eq_gapIntegral q hq hr n hn,
    hillRealGapIntegral_closed q hq hr n m hc, ofReal_zero]

/-- The weighted source action is an actual normalized contour action
also at every low gap, with no potential-dependent cutoff. -/
theorem hillPeriodOneAction_eq_realContourMoment (w : SpectralWeight)
    (q : WeightedCoeff w.doubleIndex.toWeight 2)
    (hr : IsRealHillPotential (w.doubleIndex.toCoeff q)) (n : ℕ) (hn : 1 ≤ n) :
    hillL2RealContourMoment (hillPeriodOneUnitPotential w q) (hillPeriodOneUnitPotential_even w q)
        (hillPeriodOneUnitPotential_real w q hr) n 0 = (hillPeriodOneAction w q hr n : ℂ) :=
  hillL2RealContourMoment_eq_gapIntegral _ _ _ n hn 0

theorem summable_hillPeriodOneContourAction_weighted (w : SpectralWeight)
    (q : WeightedCoeff w.doubleIndex.toWeight 2)
    (hr : IsRealHillPotential (w.doubleIndex.toCoeff q)) :
    Summable (fun k : ℕ => w (2 * ((k + 1 : ℕ) : ℤ)) ^ 2 * (2 * Real.pi * (k + 1 : ℕ)) *
      (hillL2RealContourMoment (hillPeriodOneUnitPotential w q) (hillPeriodOneUnitPotential_even w q)
        (hillPeriodOneUnitPotential_real w q hr) (k + 1) 0).re) := by
  have he : (fun k : ℕ => w (2 * ((k + 1 : ℕ) : ℤ)) ^ 2 * (2 * Real.pi * (k + 1 : ℕ)) *
      (hillL2RealContourMoment (hillPeriodOneUnitPotential w q) (hillPeriodOneUnitPotential_even w q)
        (hillPeriodOneUnitPotential_real w q hr) (k + 1) 0).re) =
      (fun k : ℕ => w (2 * ((k + 1 : ℕ) : ℤ)) ^ 2 * (2 * Real.pi * (k + 1 : ℕ)) *
        hillPeriodOneAction w q hr (k + 1)) := by
    funext k
    rw [hillPeriodOneAction_eq_realContourMoment w q hr (k + 1) (by omega), ofReal_re]
  rw [he]
  exact summable_hillPeriodOneAction_weighted w q hr

end NLS.KdV
