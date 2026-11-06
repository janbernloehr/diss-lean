import NLS.KdV.HillShiftedDifferentialContinuation
import NLS.KdV.FrequencyMoments

/-! # Actual normalized Hill frequency moments on every intrinsic gap -/
noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology
open NLS.ComplexAnalysis NLS.ZakharovShabat
namespace NLS.KdV
variable (q : WeightedCoeff SpectralWeight.one.toWeight 2)
    (hq : SpectralWeight.one.toCoeff q∈Coeff.paritySubspace 0)
    (hr : IsRealHillPotential (SpectralWeight.one.toCoeff q))

/-- Literal article moments with the actual canonical product root. -/
def hillIntrinsicFrequencyMoment (n : ℕ) (hn : 1≤n) (k m : ℕ) : ℂ :=
  frequencyMoment (hillL2ShiftedPrimitive q k)
    (fun E => hillAbelianSelectedGlobalPsi q hq hr n hn E/hillEnergyCanonicalRootProduct q hq hr E)
    (hillRealGapCenter q hq hr k : ℂ) (hillRealGapHalfLength q hq hr k+hillRealGapCollar q hq hr k) m

theorem hillIntrinsicFrequencyMoment_zero (n : ℕ) (hn : 1≤n) (k : ℕ) (hk : 1≤k) :
    hillIntrinsicFrequencyMoment q hq hr n hn k 0=(2*Real.pi:ℂ)*(if k=n then 1 else 0) := by
  have hp := hillAbelianSelectedGlobalPsi_intrinsic_periods q hq hr n hn k hk
  have hne : (2*Real.pi:ℂ)≠0 := mul_ne_zero (by norm_num) (ofReal_ne_zero.mpr Real.pi_ne_zero)
  have he := congrArg (fun z : ℂ => (2*Real.pi)*z) hp
  simp only [← mul_assoc,mul_inv_cancel₀ hne,one_mul] at he
  simpa only [hillIntrinsicFrequencyMoment,frequencyMoment,pow_zero,one_mul] using he

theorem hillIntrinsicFrequencyMoment_odd_eq_zero
    (n : ℕ) (hn : 1≤n) (k : ℕ) (hk : 1≤k) (l : ℕ) :
    hillIntrinsicFrequencyMoment q hq hr n hn k (2*l+1)=0 := by
  let c : ℂ := hillRealGapCenter q hq hr k
  let r := hillRealGapHalfLength q hq hr k+hillRealGapCollar q hq hr k
  let P := hillAbelianSelectedGlobalPsi q hq hr n hn
  let K := hillL2RealGapPrimitiveSquare (SpectralWeight.one.toCoeff q) k
  let H := hillL2FilledShiftedDifferential q k P
  obtain ⟨hd,hη,_⟩ := hillRealGapContour_geometry q hq hr k hk
  have hrp : 0<r := add_pos_of_nonneg_of_pos hd hη
  have hsub : closedBall c r⊆ball c (hillRealGapHalfLength q hq hr k+2*hillRealGapCollar q hq hr k) :=
    closedBall_subset_ball (by dsimp only [r];linarith)
  have hK : AnalyticOnNhd ℂ K (closedBall c r) :=
    (analyticOnNhd_hillL2RealGapPrimitiveSquare q hq hr k hk).mono hsub
  have hP : AnalyticOnNhd ℂ P univ := analyticOnNhd_hillAbelianSelectedGlobalPsi_energy q hq hr n hn
  have hH : AnalyticOnNhd ℂ H (closedBall c r) :=
    (analyticOnNhd_hillL2FilledShiftedDifferential q hq hr k hk P hP).mono hsub
  apply frequencyMoment_odd_eq_zero_of_continuations _ _ K H c r hrp.le hK hH _ l
  intro E hE
  exact ⟨rfl,hillL2FilledShiftedDifferential_eq_on_gapContour q hq hr k hk P hP E hE⟩

theorem hillIntrinsicFrequencyMoment_pos_eq_zero_of_closed
    (n : ℕ) (hn : 1≤n) (k : ℕ) (hk : 1≤k)
    (hc : hillRealLabels q hq hr (2*k-1)=hillRealLabels q hq hr (2*k)) (m : ℕ) :
    hillIntrinsicFrequencyMoment q hq hr n hn k (m+1)=0 := by
  let c : ℂ := hillRealGapCenter q hq hr k
  let r := hillRealGapHalfLength q hq hr k+hillRealGapCollar q hq hr k
  let P := hillAbelianSelectedGlobalPsi q hq hr n hn
  let H := hillL2FilledShiftedDifferential q k P
  obtain ⟨hd,hη,_⟩ := hillRealGapContour_geometry q hq hr k hk
  have hrp : 0<r := add_pos_of_nonneg_of_pos hd hη
  have hsub : closedBall c r⊆ball c (hillRealGapHalfLength q hq hr k+2*hillRealGapCollar q hq hr k) :=
    closedBall_subset_ball (by dsimp only [r];linarith)
  have hJ := (analyticOnNhd_hillL2ShiftedPrimitive_collapsed q hq hr k hk hc).mono hsub
  have hP : AnalyticOnNhd ℂ P univ := analyticOnNhd_hillAbelianSelectedGlobalPsi_energy q hq hr n hn
  have hH : AnalyticOnNhd ℂ H (closedBall c r) :=
    (analyticOnNhd_hillL2FilledShiftedDifferential q hq hr k hk P hP).mono hsub
  apply frequencyMoment_pos_eq_zero_of_continuations _ _ (hillL2ShiftedPrimitive q k) H c r hrp.le hJ hH _ m
  intro E hE
  exact ⟨rfl,hillL2FilledShiftedDifferential_eq_on_gapContour q hq hr k hk P hP E hE⟩


/-- Finite-gap weighted positive moments have a genuine finite-support
sum. The zeroth index is removed by the weight, as in the source sums. -/
theorem hasSum_hillIntrinsicFrequencyMoment_closed_tail
    (n : ℕ) (hn : 1≤n) (N : ℕ)
    (hclosed : ∀ (k : ℕ) (_hk : 1≤k), N<k → hillRealGapHalfLength q hq hr k=0)
    (w : ℕ → ℂ) (hw : w 0=0) (m : ℕ) :
    HasSum (fun k => w k*hillIntrinsicFrequencyMoment q hq hr n hn k (m+1))
      (∑ k∈Finset.Icc 1 N, w k*hillIntrinsicFrequencyMoment q hq hr n hn k (m+1)) := by
  apply hasSum_sum_of_ne_finset_zero
  intro k hk
  by_cases hk0 : k=0
  · rw [hk0,hw,zero_mul]
  have hk1 : 1≤k := by omega
  have hNk : N<k := by
    by_contra hh
    exact hk (Finset.mem_Icc.mpr ⟨hk1,le_of_not_gt hh⟩)
  have hh := hclosed k hk1 hNk
  have hc : hillRealLabels q hq hr (2*k-1)=hillRealLabels q hq hr (2*k) := by
    dsimp only [hillRealGapHalfLength] at hh
    linarith
  rw [hillIntrinsicFrequencyMoment_pos_eq_zero_of_closed q hq hr n hn k hk1 hc m,mul_zero]

end NLS.KdV
