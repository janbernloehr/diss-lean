import NLS.KdV.HillHminusIntrinsicDeflatedRoot
import NLS.KdV.HillActionGapRatioAllBase

noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology
open NLS.ComplexAnalysis NLS.ZakharovShabat
namespace NLS.KdV
variable (q : WeightedCoeff SpectralWeight.one.toWeight 2)
    (hq : SpectralWeight.one.toCoeff q ∈ Coeff.paritySubspace 0)
    (hr : IsRealHillPotential (SpectralWeight.one.toCoeff q))

def hillHminusIntrinsicDeflatedTraceNumerator (n : ℕ) (t : ℂ × PeriodOneHminusOne) : ℂ :=
  deriv (hillHminusDiscriminant t.2) t.1 / hillHminusIntrinsicDeflatedRoot q hq hr n t

theorem analyticOnNhd_hillHminusIntrinsicDeflatedTraceNumerator (n : ℕ) (hn : 1 ≤ n) :
    AnalyticOnNhd ℂ (hillHminusIntrinsicDeflatedTraceNumerator q hq hr n)
      (hillHminusIntrinsicDeflatedRootDomain q hq hr n) := by
  have hD := analyticOnNhd_spectral_deriv_of_analyticOnNhd
    (fun t : ℂ × PeriodOneHminusOne => hillHminusDiscriminant t.2 t.1)
    univ isOpen_univ analyticOnNhd_hillHminusDiscriminant_joint
  intro t ht
  exact (hD t (mem_univ _)).div
    (analyticOnNhd_hillHminusIntrinsicDeflatedRoot q hq hr n hn t ht)
    (hillHminusIntrinsicDeflatedRoot_ne_zero q hq hr n hn t ht)

theorem hillHminusIntrinsicDeflatedTraceNumerator_original_source (n : ℕ)
    (p : WeightedCoeff SpectralWeight.one.toWeight 2)
    (hp : SpectralWeight.one.toCoeff p ∈ Coeff.paritySubspace 0) :
    (fun z => hillHminusIntrinsicDeflatedTraceNumerator q hq hr n (z,hillOriginalHminusSource p)) =
      (fun z => hillLocalDeflatedTraceNumerator q hq hr n (z,SpectralWeight.one.toCoeff p)) := by
  have he : hillHminusDiscriminant (hillOriginalHminusSource p) = hillL2Discriminant (SpectralWeight.one.toCoeff p) :=
    funext (hillHminusDiscriminant_original_source_agreement p hp)
  funext z
  rw [hillHminusIntrinsicDeflatedTraceNumerator,hillLocalDeflatedTraceNumerator,
    hillHminusIntrinsicDeflatedRoot_original_source q hq hr n p hp,he]

def hillHminusIntrinsicActionGapRatio (n : ℕ) : PeriodOneHminusOne → ℂ :=
  quadraticGapActionRatio (hillHminusIntrinsicDeflatedTraceNumerator q hq hr n)
    (hillHminusIntrinsicGapMidpoint q hq hr n) (fun p => hillHminusIntrinsicGapSquare q hq hr n p/4)

theorem analyticAt_hillHminusIntrinsicActionGapRatio (n : ℕ) (hn : 1 ≤ n) :
    AnalyticAt ℂ (hillHminusIntrinsicActionGapRatio q hq hr n) (hillOriginalHminusSource q) := by
  obtain ⟨A,_,hqA,hM,hS,_⟩ := exists_hillHminusIntrinsicGapSymmetricData_analytic_neighborhood q hq hr n hn
  obtain ⟨W,_,hqW,hmatch⟩ := exists_hillHminusIntrinsicGapSymmetricData_physical_neighborhood q hq hr n hn
  have hdata := hmatch ⟨q,hq,hr⟩ hqW
  obtain ⟨hd,hη,_⟩ := hillRealGapContour_geometry q hq hr n hn
  let δ := hillRealGapHalfLength q hq hr n
  let S := δ+hillRealGapCollar q hq hr n/2
  let D := hillHminusIntrinsicDeflatedRootDomain q hq hr n
  have hD : IsOpen D := isOpen_hillHminusIntrinsicDeflatedRootDomain q hq hr n hn
  have hH' := analyticOnNhd_spectral_deriv_of_analyticOnNhd
    (hillHminusIntrinsicDeflatedTraceNumerator q hq hr n) D hD (analyticOnNhd_hillHminusIntrinsicDeflatedTraceNumerator q hq hr n hn)
  have hsq : AnalyticAt ℂ (fun p : PeriodOneHminusOne => (Complex.sqrt (hillHminusIntrinsicGapSquare q hq hr n p/4))^2) (hillOriginalHminusSource q) := by
    simpa only [complex_sqrt_sq] using (hS _ hqA).div_const (c := (4 : ℂ))
  have hbase : (Complex.sqrt (hillHminusIntrinsicGapSquare q hq hr n (hillOriginalHminusSource q)/4))^2 = (δ : ℂ)^2 := by
    rw [complex_sqrt_sq,hdata.2]
    change (2*(δ : ℂ))^2/4 = (δ : ℂ)^2
    ring
  have hnorm : ‖Complex.sqrt (hillHminusIntrinsicGapSquare q hq hr n (hillOriginalHminusSource q)/4)‖ = δ := by
    have h := congrArg norm hbase
    rw [norm_pow,norm_pow,norm_real,Real.norm_eq_abs,abs_of_nonneg hd] at h
    nlinarith [norm_nonneg (Complex.sqrt (hillHminusIntrinsicGapSquare q hq hr n (hillOriginalHminusSource q)/4))]
  have hm := analyticAt_parametricSineSquareCosineMean_of_analytic_square _
    (hillHminusIntrinsicGapMidpoint q hq hr n) (fun p => Complex.sqrt (hillHminusIntrinsicGapSquare q hq hr n p/4)) D hD hH'
    (hillOriginalHminusSource q) (hM _ hqA) hsq S
    (by rw [hnorm];dsimp [S];linarith)
    (by
      intro z hz
      rw [hdata.1] at hz
      exact mem_hillHminusIntrinsicDeflatedRootDomain_base q hq hr n hn z
        (closedBall_subset_ball (by dsimp [S,δ];linarith : S < hillRealGapHalfLength q hq hr n+hillRealGapCollar q hq hr n) hz))
  exact analyticAt_const.mul hm

/-- The all-source action-gap ratio agrees exactly with the ORIGINAL
ratio, including its analytic value at collapsed own gaps. -/
theorem hillHminusIntrinsicActionGapRatio_original_source (n : ℕ)
    (p : WeightedCoeff SpectralWeight.one.toWeight 2)
    (hp : SpectralWeight.one.toCoeff p ∈ Coeff.paritySubspace 0) :
    hillHminusIntrinsicActionGapRatio q hq hr n (hillOriginalHminusSource p) =
      hillLocalActionGapRatio q hq hr n (SpectralWeight.one.toCoeff p) := by
  simp only [hillHminusIntrinsicActionGapRatio,hillLocalActionGapRatio,quadraticGapActionRatio,
    parametricSineSquareCosineMean]
  simp_rw [hillHminusIntrinsicGapMidpoint_original_source q hq hr n p hp,
    hillHminusIntrinsicGapSquare_original_source q hq hr n p hp,
    hillHminusIntrinsicDeflatedTraceNumerator_original_source q hq hr n p hp]

theorem hillHminusIntrinsicActionGapRatio_eventually_eq_physical (n : ℕ) (hn : 1 ≤ n) :
    ∀ᶠ p : RealPeriodOneHillPotential in 𝓝 (⟨q,hq,hr⟩ : RealPeriodOneHillPotential),
      hillHminusIntrinsicActionGapRatio q hq hr n (hillOriginalHminusSource p.val) =
        hillActionGapRatio p.val p.property.1 p.property.2 n := by
  filter_upwards [hillLocalActionGapRatio_eventually_eq_physical q hq hr n hn] with p hp
  rw [hillHminusIntrinsicActionGapRatio_original_source q hq hr n p.val p.property.1]
  exact hp

end NLS.KdV
