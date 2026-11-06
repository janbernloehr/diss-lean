import NLS.KdV.HillOddKernelContinuation
import NLS.KdV.HillFiniteGapIntrinsicDecomposition

/-! # Actual finite-gap odd-power exterior periods and intrinsic deformation -/
noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology
open NLS.ComplexAnalysis NLS.ZakharovShabat
namespace NLS.KdV
variable (q : WeightedCoeff SpectralWeight.one.toWeight 2)
    (hq : SpectralWeight.one.toCoeff q∈Coeff.paritySubspace 0)
    (hr : IsRealHillPotential (SpectralWeight.one.toCoeff q))

/-- The genuine odd-power integrand is circle integrable at every large
radius and its outer periods are exactly independent of that radius. -/
theorem HillFiniteGap.exists_odd_exterior_and_periods
    (hfg : HillFiniteGap q hq hr) (m n : ℕ) (hn : 1≤n) :
    ∃ R : ℝ, 0<R ∧
      AnalyticOnNhd ℂ (hillL2FilledOddKernel q m (hillAbelianSelectedGlobalPsi q hq hr n hn))
        {E : ℂ | R<‖E‖} ∧
      ∀ r : ℝ, R<r →
        CircleIntegrable (hillL2OddKernel q m (hillAbelianSelectedGlobalPsi q hq hr n hn)) 0 r ∧
        ∀ s : ℝ, R<s →
          (∮ E in C(0,r), hillL2OddKernel q m (hillAbelianSelectedGlobalPsi q hq hr n hn) E)=
            ∮ E in C(0,s), hillL2OddKernel q m (hillAbelianSelectedGlobalPsi q hq hr n hn) E := by
  obtain ⟨R,hR,hsub⟩ := HillFiniteGap.exists_exterior_subset_cubic_filled q hq hr hfg n
  let P := hillAbelianSelectedGlobalPsi q hq hr n hn
  let G := hillL2FilledOddKernel q m P
  have hP : AnalyticOnNhd ℂ P univ := analyticOnNhd_hillAbelianSelectedGlobalPsi_energy q hq hr n hn
  have ha : AnalyticOnNhd ℂ G {E : ℂ | R<‖E‖} :=
    (analyticOnNhd_hillL2FilledOddKernel q hq hr m n hn).mono hsub
  have hi (r s : ℝ) (hrR : R<r) (hrs : r≤s) :
      (∮ E in C(0,s), G E)=∮ E in C(0,r), G E := by
    have hA : AnalyticOnNhd ℂ G (closedBall 0 s \ ball 0 r) := ha.mono (by
      intro E hE
      have hnorm : r≤‖E‖ := by
        by_contra hh
        exact hE.2 (mem_ball_zero_iff.mpr (lt_of_not_ge hh))
      exact hrR.trans_le hnorm)
    exact Complex.circleIntegral_eq_of_differentiable_on_annulus_off_countable
      (hR.trans hrR) hrs countable_empty hA.continuousOn
      (fun E hE => (hA E ⟨ball_subset_closedBall hE.1.1,
        fun h => hE.1.2 (ball_subset_closedBall h)⟩).differentiableAt)
  refine ⟨R,hR,ha,?_⟩
  intro r hrR
  have hrp : 0<r := hR.trans hrR
  have hGi : CircleIntegrable G 0 r := (ha.continuousOn.mono (by
    intro E hE
    have he : ‖E‖=r := by simpa only [mem_sphere_iff_norm,sub_zero] using hE
    change R<‖E‖
    rw [he]
    exact hrR)).circleIntegrable hrp.le
  refine ⟨(circleIntegrable_hillL2FilledOddKernel_iff q hq hr m P hP r hrp).mp hGi,?_⟩
  intro s hsR
  rw [← circleIntegral_hillL2FilledOddKernel_eq q hq hr m P hP r hrp,
    ← circleIntegral_hillL2FilledOddKernel_eq q hq hr m P hP s (hR.trans hsR)]
  by_cases hrs : r≤s
  · exact (hi r s hrR hrs).symm
  · exact hi s r hsR (le_of_not_ge hrs)

/-- Actual analytic filling and disjoint intrinsic discs give a genuine
finite-hole deformation at every odd power. Every first-N index, including the selected
closed one, is retained. -/
theorem exists_hillFiniteGap_odd_contour_decomposition
    (m n N : ℕ) (hn : 1≤n) (hnN : n≤N)
    (hclosed : ∀ (k : ℕ) (_hk : 1≤k), N<k → hillRealGapHalfLength q hq hr k=0) :
    ∃ R : ℝ, 0<R ∧ ∀ S : ℝ, R<S →
      (∮ E in C(0,S), hillL2OddKernel q m (hillAbelianSelectedGlobalPsi q hq hr n hn) E)=
        ∑ k∈Finset.Icc 1 N, ∮ E in C((hillRealGapCenter q hq hr k : ℂ),hillIntrinsicGapRadius q hq hr k),
          hillL2RealCutPrimitive (SpectralWeight.one.toCoeff q) E^(2*m+1)*
            hillAbelianSelectedGlobalPsi q hq hr n hn E/hillEnergyCanonicalRootProduct q hq hr E := by
  let A := Finset.Icc 1 N
  let c : ℕ → ℂ := fun k => hillRealGapCenter q hq hr k
  let r := hillIntrinsicGapRadius q hq hr
  let ρ := hillIntrinsicGapOuterRadius q hq hr
  let P := hillAbelianSelectedGlobalPsi q hq hr n hn
  let f := hillL2FilledOddKernel q m P
  have hP : AnalyticOnNhd ℂ P univ := analyticOnNhd_hillAbelianSelectedGlobalPsi_energy q hq hr n hn
  obtain ⟨R,hR,henclosed⟩ := exists_intrinsicOuterBalls_enclosed q hq hr N
  refine ⟨R,hR,?_⟩
  intro S hS
  have hSp : 0<S := hR.trans hS
  have ha : AnalyticOnNhd ℂ f (circleHoleDomain 0 S A c r) :=
    (analyticOnNhd_hillL2FilledOddKernel q hq hr m n hn).mono (by
      intro E hE
      exact hillCubicFilledDomain_of_avoids_intrinsicBalls q hq hr n N hn hnN hclosed E hE.2)
  rw [← circleIntegral_hillL2FilledOddKernel_eq q hq hr m P hP S hSp,
    circleIntegral_eq_sum_of_finite_holes 0 S hSp.le A c r ρ f
      (fun k hk => (hillIntrinsicGapRadii_bounds q hq hr k (Finset.mem_Icc.mp hk).1).1)
      (fun k hk => (hillIntrinsicGapRadii_bounds q hq hr k (Finset.mem_Icc.mp hk).1).2.1)
      (henclosed S hS)
      (fun k hk j hj hkj => hillIntrinsicGapOuterBalls_disjoint q hq hr k j
        (Finset.mem_Icc.mp hk).1 (Finset.mem_Icc.mp hj).1 hkj) ha]
  apply Finset.sum_congr rfl
  intro k hk
  have hk1 : 1≤k := (Finset.mem_Icc.mp hk).1
  apply circleIntegral.integral_congr (hillIntrinsicGapRadii_bounds q hq hr k hk1).1.le
  intro E hE
  have hc := hillRealGapContour_sphere_subset q hq hr k hk1 hE
  dsimp only [f]
  rw [hillL2FilledOddKernel_eq_on_realCut q hq hr m P hP hc,
    hillEnergyCanonicalRootProduct_eq_realCutRoot q hq hr hc]
  rfl

end NLS.KdV
