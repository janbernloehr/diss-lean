import NLS.KdV.HillHminusOneAnnulusCoverage
import NLS.KdV.HillL2CubicContourMoments
import NLS.ComplexAnalysis.TracePrimitiveMoments

/-! # The actual H^-1 high contour moments on one common complex neighborhood

These are the literal Arnold and cubic primitive periods. Uniform
source coverage gives joint contour analyticity on one H^-1 neighborhood
before all high indices. The source constants and physical L2 periods
are retained exactly; no Birkhoff action-space descent is assumed.
-/
noncomputable section
set_option autoImplicit false
open Set Metric Complex NLS.ComplexAnalysis
namespace NLS.KdV

def hillHminusHighContourMoment (n m : ℕ) (q : PeriodOneHminusOne) : ℂ :=
  hillHminusSourceFamily.contourMoment (freeHillValue n : ℂ) (n : ℝ) m q

def hillHminusHighCubicContourMoment (n : ℕ) (q : PeriodOneHminusOne) : ℂ :=
  (Real.pi : ℂ)⁻¹ * ∮ z in C((freeHillValue n : ℂ),(n : ℝ)),
    (hillHminusContinuedPrimitive (z,q)+I*(n : ℂ)*Real.pi)^3

@[simp] theorem hillHminusHighContourMoment_zero (n m : ℕ) (hn : 1 ≤ n) :
    hillHminusHighContourMoment n m 0 = 0 :=
  hillHminusSourceFamily.contourMoment_base (freeHillValue n : ℂ) (n : ℝ) (by positivity)
    (hillClosedBall_subset_slitPlane n hn) m

@[simp] theorem hillHminusHighCubicContourMoment_zero (n : ℕ) (hn : 1 ≤ n) :
    hillHminusHighCubicContourMoment n 0 = 0 := by
  have hF : AnalyticOnNhd ℂ
      (fun z => (classicalHillFreePrimitive z+I*(n : ℂ)*Real.pi)^3)
      (closedBall (freeHillValue n : ℂ) (n : ℝ)) := by
    intro z hz
    exact ((analyticOnNhd_classicalHillFreePrimitive z
      (hillClosedBall_subset_slitPlane n hn hz)).add analyticAt_const).pow 3
  have hi := (DiffContOnCl.mk_ball
    (hF.differentiableOn.mono ball_subset_closedBall) hF.continuousOn).circleIntegral_eq_zero
    (show (0 : ℝ) ≤ n by positivity)
  simp only [hillHminusHighCubicContourMoment,hillHminusContinuedPrimitive_base,
    classicalHillFreePrimitive] at hi ⊢
  rw [hi,mul_zero]

theorem hillHminusHighContourMoment_arnold_level (q : PeriodOneHminusOne) (n m : ℕ)
    (hc : ∀ z ∈ sphere (freeHillValue n : ℂ) (n : ℝ), (z,q) ∈ hillHminusContinuationDomain) :
    hillHminusHighContourMoment n m q =
      ((m+1 : ℂ)*(Real.pi : ℂ))⁻¹ * ∮ z in C((freeHillValue n : ℂ),(n : ℝ)),
        z^(m+1)*deriv (hillHminusDiscriminant q) z/hillHminusContinuedRoot (z,q) :=
  hillHminusSourceFamily.contourMoment_arnold (freeHillValue n : ℂ) (n : ℝ) (by positivity) q hc m

theorem hillHminusHighContourMoment_eq_hillL2 (q : Coeff 2) (n m : ℕ)
    (hc : ∀ z ∈ sphere (freeHillValue n : ℂ) (n : ℝ),
      (z,Coeff.periodDouble q) ∈ hillL2ContinuationDomain) :
    hillHminusHighContourMoment n m (periodOneL2Inclusion q) =
      hillL2HighContourMoment n m (Coeff.periodDouble q) := by
  unfold hillHminusHighContourMoment hillL2HighContourMoment TracePrimitiveFamily.contourMoment
  congr 1
  apply circleIntegral.integral_congr (by positivity : (0 : ℝ) ≤ n)
  intro z hz
  change z^m*hillHminusContinuedPrimitive (z,periodOneL2Inclusion q) =
    z^m*hillL2ContinuedPrimitive (z,Coeff.periodDouble q)
  rw [hillHminusContinuedPrimitive_eq_hillL2 z q (hc z hz)]

theorem hillHminusHighCubicContourMoment_eq_hillL2 (q : Coeff 2) (n : ℕ)
    (hc : ∀ z ∈ sphere (freeHillValue n : ℂ) (n : ℝ),
      (z,Coeff.periodDouble q) ∈ hillL2ContinuationDomain) :
    hillHminusHighCubicContourMoment n (periodOneL2Inclusion q) =
      hillL2HighCubicContourMoment n (Coeff.periodDouble q) := by
  unfold hillHminusHighCubicContourMoment hillL2HighCubicContourMoment
  congr 1
  apply circleIntegral.integral_congr (by positivity : (0 : ℝ) ≤ n)
  intro z hz
  change (hillHminusContinuedPrimitive (z,periodOneL2Inclusion q)+I*(n : ℂ)*Real.pi)^3 =
    (hillL2ContinuedPrimitive (z,Coeff.periodDouble q)+I*(n : ℂ)*Real.pi)^3
  rw [hillHminusContinuedPrimitive_eq_hillL2 z q (hc z hz)]

theorem exists_analytic_hillHminusHighContourMomentFamilies (q : PeriodOneHminusOne) :
    ∃ N : ℕ, ∃ V : Set PeriodOneHminusOne, 0 < N ∧ IsOpen V ∧ q ∈ V ∧
      ∀ n : ℕ+, N ≤ (n : ℕ) →
        (∀ m : ℕ, AnalyticOnNhd ℂ (hillHminusHighContourMoment (n : ℕ) m) V) ∧
        AnalyticOnNhd ℂ (hillHminusHighCubicContourMoment (n : ℕ)) V := by
  obtain ⟨N,V,hN,hV,hq,hcover⟩ := exists_hillHminus_high_energy_annulus_neighborhood q 1
    (by norm_num)
  refine ⟨N,V,hN,hV,hq,?_⟩
  intro n hn
  have hc (a : PeriodOneHminusOne) (ha : a ∈ V) (z : ℂ)
      (hz : z ∈ sphere (freeHillValue (n : ℕ) : ℂ) (n : ℝ)) :
      (z,a) ∈ hillHminusContinuationDomain := by
    apply hcover a ha n hn z (sphere_subset_closedBall hz)
    have he : ‖z-(freeHillValue (n : ℕ) : ℂ)‖ = (n : ℝ) := by
      simpa only [mem_sphere,dist_eq_norm] using hz
    rw [one_mul,he]
  constructor
  · intro m
    let F : ℂ × PeriodOneHminusOne → ℂ := fun t => t.1^m*hillHminusContinuedPrimitive t
    have hF : AnalyticOnNhd ℂ F hillHminusContinuationDomain :=
      (analyticOnNhd_fst.pow m).mul analyticOnNhd_hillHminusContinuedPrimitive
    have hi := analyticOnNhd_circleIntegral_of_jointAnalytic F
      isOpen_hillHminusContinuationDomain hF (freeHillValue (n : ℕ) : ℂ) (n : ℝ)
      (by positivity) hV hc
    intro a ha
    change AnalyticAt ℂ (fun b => -(Real.pi : ℂ)⁻¹ *
      ∮ z in C((freeHillValue (n : ℕ) : ℂ),(n : ℝ)), z^m*hillHminusContinuedPrimitive (z,b)) a
    exact (hi a ha).const_smul (c := -(Real.pi : ℂ)⁻¹)
  · let F : ℂ × PeriodOneHminusOne → ℂ := fun t => (hillHminusContinuedPrimitive t+I*(n : ℂ)*Real.pi)^3
    have hF : AnalyticOnNhd ℂ F hillHminusContinuationDomain :=
      (analyticOnNhd_hillHminusContinuedPrimitive.add analyticOnNhd_const).pow 3
    have hi := analyticOnNhd_circleIntegral_of_jointAnalytic F
      isOpen_hillHminusContinuationDomain hF (freeHillValue (n : ℕ) : ℂ) (n : ℝ)
      (by positivity) hV hc
    intro a ha
    exact (hi a ha).const_smul (c := (Real.pi : ℂ)⁻¹)

end NLS.KdV
