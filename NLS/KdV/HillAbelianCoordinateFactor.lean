import NLS.KdV.HillAbelianPhase
import NLS.KdV.HillActionGapPrefactor

/-! # Physical amplitude-weighted Abelian coordinates without gap division -/
noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology
open NLS.ZakharovShabat NLS.ComplexAnalysis
namespace NLS.KdV
variable (q : WeightedCoeff SpectralWeight.one.toWeight 2)
    (hq : SpectralWeight.one.toCoeff q∈Coeff.paritySubspace 0)
    (hr : IsRealHillPotential (SpectralWeight.one.toCoeff q))

/-- The complex source coordinates use sqrt(I), so the real Cartesian
sqrt(2I) prefactor must be divided by sqrt(2). -/
def hillAbelianAmplitudePrefactor (n : ℕ) : ℂ :=
  hillActionGapPrefactor q hq hr n/(Real.sqrt 2:ℂ)

def hillLocalAbelianAmplitudePrefactor (n : ℕ) (p : Coeff 2) : ℂ :=
  hillLocalActionGapPrefactor q hq hr n p/(Real.sqrt 2:ℂ)

theorem analyticAt_hillLocalAbelianAmplitudePrefactor (n : ℕ) (hn : 1≤n) :
    AnalyticAt ℂ (hillLocalAbelianAmplitudePrefactor q hq hr n) (SpectralWeight.one.toCoeff q) :=
  (analyticAt_hillLocalActionGapPrefactor q hq hr n hn).div_const

theorem hillLocalAbelianAmplitudePrefactor_eventually_eq_physical (n : ℕ) (hn : 1≤n) :
    ∀ᶠ p : RealPeriodOneHillPotential in 𝓝 (⟨q,hq,hr⟩ : RealPeriodOneHillPotential),
      hillLocalAbelianAmplitudePrefactor q hq hr n (SpectralWeight.one.toCoeff p.val)=
        hillAbelianAmplitudePrefactor p.val p.property.1 p.property.2 n := by
  filter_upwards [hillLocalActionGapPrefactor_eventually_eq_physical q hq hr n hn] with p hp
  exact congrArg (fun z : ℂ => z/(Real.sqrt 2:ℂ)) hp

theorem sqrt_hillAction_eq_halfLength_mul_abelianPrefactor (n : ℕ) (hn : 1≤n) :
    (Real.sqrt (hillRealGapIntegral q hq hr n 0):ℂ)=
      (hillRealGapHalfLength q hq hr n:ℂ)*hillAbelianAmplitudePrefactor q hq hr n := by
  have h := sqrt_twice_hillAction_eq_halfLength_mul_prefactor q hq hr n hn
  rw [Real.sqrt_mul (by norm_num : (0:ℝ)≤2),ofReal_mul] at h
  have hs : (Real.sqrt 2:ℂ)≠0 := ofReal_ne_zero.mpr (Real.sqrt_pos.mpr (by norm_num : (0:ℝ)<2)).ne'
  unfold hillAbelianAmplitudePrefactor
  rw [← mul_div_assoc]
  apply (eq_div_iff hs).mpr
  rw [mul_comm]
  exact h

/-- This scalar coordinate is defined from the actual nonnegative action
and the actual infinite Abelian phase, with the source's sqrt(I) amplitude. -/
def hillDirichletAbelianCoordinate (n : ℕ) (hn : 1≤n) : ℂ :=
  (Real.sqrt (hillRealGapIntegral q hq hr n 0):ℂ)*hillDirichletAbelianPhase q hq hr n hn

/-- The numerator factor remains meaningful when the own gap collapses. -/
def hillDirichletAbelianTerminalFactor (n : ℕ) (hn : 1≤n) : ℂ :=
  hillDirichletSheetRoot (SpectralWeight.one.toCoeff q) (hillDirichletEnergy q hq hr n hn)/
    hillDeflatedEnergyCanonicalRoot q hq hr n (hillDirichletEnergy q hq hr n hn) -
      ((hillDirichletEnergy q hq hr n hn:ℂ)-(hillRealGapCenter q hq hr n:ℂ))

theorem hillDirichletEnergy_eq_center_of_halfLength_zero (n : ℕ) (hn : 1≤n)
    (hc : hillRealGapHalfLength q hq hr n=0) :
    hillDirichletEnergy q hq hr n hn=hillRealGapCenter q hq hr n := by
  have hμ := hillDirichletEnergy_mem_gap q hq hr n hn
  dsimp only [hillRealGapHalfLength] at hc
  dsimp only [hillRealGapCenter]
  linarith [hμ.1,hμ.2]

theorem hillDirichletAbelianTerminalFactor_closed (n : ℕ) (hn : 1≤n)
    (hc : hillRealGapHalfLength q hq hr n=0) :
    hillDirichletAbelianTerminalFactor q hq hr n hn=0 := by
  unfold hillDirichletAbelianTerminalFactor
  rw [hillDirichletSheetRoot_eq_zero_of_halfLength_zero q hq hr n hn hc,
    hillDirichletEnergy_eq_center_of_halfLength_zero q hq hr n hn hc,zero_div,sub_self,sub_self]

theorem hillDirichletAbelianCoordinate_closed (n : ℕ) (hn : 1≤n)
    (hc : hillRealGapHalfLength q hq hr n=0) :
    hillDirichletAbelianCoordinate q hq hr n hn=0 := by
  have hi : hillRealGapIntegral q hq hr n 0=0 := by
    have h := hillRealGapIntegral_eq_halfLength_sq_mul_ratio q hq hr n hn
    rw [hc,ofReal_zero,zero_pow (by decide : 2≠0),zero_mul] at h
    exact ofReal_injective h
  simp only [hillDirichletAbelianCoordinate,hi,Real.sqrt_zero,ofReal_zero,zero_mul]

/-- The actual amplitude-weighted phase has a gap-division-free formula
at every real source, including a collapsed selected gap. -/
theorem hillDirichletAbelianCoordinate_eq_factor (n : ℕ) (hn : 1≤n) :
    hillDirichletAbelianCoordinate q hq hr n hn=
      hillAbelianAmplitudePrefactor q hq hr n*hillDirichletAbelianTerminalFactor q hq hr n hn*
        exp (I*hillSummedRegularAbelianCorrection q hq hr n hn) := by
  by_cases hc : hillRealGapHalfLength q hq hr n=0
  · rw [hillDirichletAbelianCoordinate_closed q hq hr n hn hc,
      hillDirichletAbelianTerminalFactor_closed q hq hr n hn hc,mul_zero,zero_mul]
  · have hball := hillRealGapSegment_subset_intrinsic_contour_ball q hq hr n hn
      (ofReal_mem_ordered_segment _ _ _ (monotone_hillRealLabels q hq hr (by omega : 2*n-1≤2*n))
        (hillDirichletEnergy_mem_gap q hq hr n hn))
    have hU := hillDeflatedEnergyCanonicalRoot_ne_zero q hq hr n hn (hillDirichletEnergy q hq hr n hn)
      (hillRealGapContour_closedBall_subset_filledDomain q hq hr n hn (ball_subset_closedBall hball))
    rw [hillDirichletAbelianCoordinate,sqrt_hillAction_eq_halfLength_mul_abelianPrefactor q hq hr n hn]
    unfold hillDirichletAbelianPhase hillDirichletGapCosine hillDirichletGapSine hillDirichletAbelianTerminalFactor
    field_simp [ofReal_ne_zero.mpr hc,hU]
    simp only [I_sq]
    ring

variable (h0q : SpectralWeight.one.toCoeff (0 : WeightedCoeff SpectralWeight.one.toWeight 2)∈Coeff.paritySubspace 0)
    (h0r : IsRealHillPotential (SpectralWeight.one.toCoeff (0 : WeightedCoeff SpectralWeight.one.toWeight 2)))
include h0q h0r

/-- The physical squared coordinate amplitude is exactly the actual
action, including closed selected gaps. -/
theorem norm_sq_hillDirichletAbelianCoordinate (n : ℕ) (hn : 1≤n) :
    ‖hillDirichletAbelianCoordinate q hq hr n hn‖^2=hillRealGapIntegral q hq hr n 0 := by
  by_cases hc : hillRealGapHalfLength q hq hr n=0
  · rw [hillDirichletAbelianCoordinate_closed q hq hr n hn hc,norm_zero,zero_pow (by decide : 2≠0)]
    have h := hillRealGapIntegral_eq_halfLength_sq_mul_ratio q hq hr n hn
    rw [hc,ofReal_zero,zero_pow (by decide : 2≠0),zero_mul] at h
    exact (ofReal_injective h).symm
  · have hI : 0≤hillRealGapIntegral q hq hr n 0 := by
      simpa only [mul_zero] using hillRealGapIntegral_nonneg_even q hq hr n hn 0
    rw [hillDirichletAbelianCoordinate,norm_mul,norm_hillDirichletAbelianPhase q hq hr h0q h0r n hn hc,mul_one,
      norm_real,Real.norm_of_nonneg (Real.sqrt_nonneg _),Real.sq_sqrt hI]

/-- The scalar physical coordinate vanishes precisely at its closed gap. -/
theorem hillDirichletAbelianCoordinate_eq_zero_iff (n : ℕ) (hn : 1≤n) :
    hillDirichletAbelianCoordinate q hq hr n hn=0 ↔ hillRealGapHalfLength q hq hr n=0 := by
  refine ⟨?_,hillDirichletAbelianCoordinate_closed q hq hr n hn⟩
  intro hz
  have hnorm := norm_sq_hillDirichletAbelianCoordinate q hq hr h0q h0r n hn
  rw [hz,norm_zero,zero_pow (by decide : 2≠0)] at hnorm
  have h := congrArg Complex.re (hillRealGapIntegral_eq_halfLength_sq_mul_ratio q hq hr n hn)
  rw [← ofReal_pow] at h
  simp only [ofReal_re,mul_re,ofReal_im,zero_mul,sub_zero] at h
  have hprod : (hillRealGapHalfLength q hq hr n)^2*(hillActionGapRatio q hq hr n).re=0 := h.symm.trans hnorm.symm
  exact sq_eq_zero_iff.mp ((mul_eq_zero.mp hprod).resolve_right
    (hillActionGapRatio_real_positive q hq hr n hn).1.ne')

end NLS.KdV
