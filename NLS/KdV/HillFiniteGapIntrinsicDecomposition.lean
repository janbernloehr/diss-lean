import NLS.KdV.HillIntrinsicGapGeometry
import NLS.KdV.HillIntrinsicCubicFrequency

/-! # Actual finite-gap cubic contour deformation -/
noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology
open NLS.ComplexAnalysis NLS.ZakharovShabat
namespace NLS.KdV
variable (q : WeightedCoeff SpectralWeight.one.toWeight 2)
    (hq : SpectralWeight.one.toCoeff q∈Coeff.paritySubspace 0)
    (hr : IsRealHillPotential (SpectralWeight.one.toCoeff q))

/-- Actual analytic filling and disjoint intrinsic discs give a genuine
finite-hole deformation. Every first-N index, including the selected
closed one, is retained. -/
theorem exists_hillFiniteGap_cubic_contour_decomposition
    (n N : ℕ) (hn : 1≤n) (hnN : n≤N)
    (hclosed : ∀ (k : ℕ) (_hk : 1≤k), N<k → hillRealGapHalfLength q hq hr k=0) :
    ∃ R : ℝ, 0<R ∧ ∀ S : ℝ, R<S →
      (∮ E in C(0,S), hillL2CubicKernel q (hillAbelianSelectedGlobalPsi q hq hr n hn) E)=
        ∑ k∈Finset.Icc 1 N, ∮ E in C((hillRealGapCenter q hq hr k : ℂ),hillIntrinsicGapRadius q hq hr k),
          hillL2RealCutPrimitive (SpectralWeight.one.toCoeff q) E^3*
            hillAbelianSelectedGlobalPsi q hq hr n hn E/hillEnergyCanonicalRootProduct q hq hr E := by
  let A := Finset.Icc 1 N
  let c : ℕ → ℂ := fun k => hillRealGapCenter q hq hr k
  let r := hillIntrinsicGapRadius q hq hr
  let ρ := hillIntrinsicGapOuterRadius q hq hr
  let P := hillAbelianSelectedGlobalPsi q hq hr n hn
  let f := hillL2FilledCubicKernel q P
  have hP : AnalyticOnNhd ℂ P univ := analyticOnNhd_hillAbelianSelectedGlobalPsi_energy q hq hr n hn
  obtain ⟨R,hR,henclosed⟩ := exists_intrinsicOuterBalls_enclosed q hq hr N
  refine ⟨R,hR,?_⟩
  intro S hS
  have hSp : 0<S := hR.trans hS
  have ha : AnalyticOnNhd ℂ f (circleHoleDomain 0 S A c r) :=
    (analyticOnNhd_hillL2FilledCubicKernel q hq hr n hn).mono (by
      intro E hE
      exact hillCubicFilledDomain_of_avoids_intrinsicBalls q hq hr n N hn hnN hclosed E hE.2)
  rw [← circleIntegral_hillL2FilledCubicKernel_eq q hq hr P hP S hSp,
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
  rw [hillL2FilledCubicKernel_eq_on_realCut q hq hr P hP hc,
    hillEnergyCanonicalRootProduct_eq_realCutRoot q hq hr hc]
  rfl

/-- The actual cubic outer contour has exactly the source leading
frequency and the finite weighted second-moment correction. -/
theorem exists_hillFiniteGap_cubic_frequency_moments
    (n N : ℕ) (hn : 1≤n) (hnN : n≤N)
    (hclosed : ∀ (k : ℕ) (_hk : 1≤k), N<k → hillRealGapHalfLength q hq hr k=0) :
    ∃ R : ℝ, 0<R ∧ ∀ S : ℝ, R<S →
      (4/(I*Real.pi) : ℂ)*(∮ E in C(0,S), hillL2CubicKernel q (hillAbelianSelectedGlobalPsi q hq hr n hn) E)-
        (2*(n:ℂ)*Real.pi)^3=
          -12*∑ k∈Finset.Icc 1 N, (k:ℂ)*hillIntrinsicFrequencyMoment q hq hr n hn k 2 := by
  obtain ⟨R,hR,hcontour⟩ := exists_hillFiniteGap_cubic_contour_decomposition q hq hr n N hn hnN hclosed
  refine ⟨R,hR,?_⟩
  intro S hS
  rw [hcontour S hS,Finset.mul_sum]
  have hsum : (∑ k∈Finset.Icc 1 N, (4/(I*Real.pi) : ℂ)*
      (∮ E in C((hillRealGapCenter q hq hr k : ℂ),hillIntrinsicGapRadius q hq hr k),
        hillL2RealCutPrimitive (SpectralWeight.one.toCoeff q) E^3*
          hillAbelianSelectedGlobalPsi q hq hr n hn E/hillEnergyCanonicalRootProduct q hq hr E))=
      ∑ k∈Finset.Icc 1 N, (-12*(k:ℂ)*hillIntrinsicFrequencyMoment q hq hr n hn k 2+
        if k=n then (2*(n:ℂ)*Real.pi)^3 else 0) := by
    apply Finset.sum_congr rfl
    intro k hk
    dsimp only [hillIntrinsicGapRadius]
    rw [hillIntrinsicCubicFrequency_gap_contribution q hq hr n hn k (Finset.mem_Icc.mp hk).1]
    split_ifs with he
    · subst k
      rfl
    · rfl
  rw [hsum,Finset.sum_add_distrib]
  simp only [Finset.sum_ite_eq',Finset.mem_Icc.mpr ⟨hn,hnN⟩,if_true]
  rw [Finset.mul_sum]
  simp_rw [mul_assoc]
  ring

end NLS.KdV
