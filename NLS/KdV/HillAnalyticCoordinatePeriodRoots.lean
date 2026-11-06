import NLS.KdV.HillComplexRootCoordinatePeriods

noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology
open NLS.ComplexAnalysis NLS.ZakharovShabat
open scoped ENNReal ComplexConjugate

namespace NLS.KdV

variable (q : WeightedCoeff SpectralWeight.one.toWeight 2)
    (hq : SpectralWeight.one.toCoeff q ∈ Coeff.paritySubspace 0)
    (hr : IsRealHillPotential (SpectralWeight.one.toCoeff q))

def hillAbelianComplexCoordinateRoot (n m : ℕ) (t : Coeff 2 × Coeff 2) : ℂ :=
  -hillAbelianComplexUpdatedPeriod q hq hr n m 0 t/
    (hillAbelianComplexUpdatedPeriod q hq hr n m 1 t-hillAbelianComplexUpdatedPeriod q hq hr n m 0 t)

theorem hillAbelianComplexUpdatedPeriod_difference_at_base
    (n m : ℕ) (hm : 1 ≤ m) (hmn : m ≠ n) (a : Coeff 2) :
    hillAbelianComplexUpdatedPeriod q hq hr n m 1 (a,SpectralWeight.one.toCoeff q)-
      hillAbelianComplexUpdatedPeriod q hq hr n m 0 (a,SpectralWeight.one.toCoeff q) =
        hillIntrinsicGapPeriod q hq hr m (fun E => hillAbelianRootSlope n m E a) := by
  rw [hillAbelianComplexUpdatedPeriod_at_base q hq hr n m hm 1 a,
    hillAbelianComplexUpdatedPeriod_at_base q hq hr n m hm 0 a,
    hillIntrinsicGapPeriod_rootUpdate_affine q hq hr n m hm hmn a 1]
  ring

theorem analyticAt_hillAbelianComplexCoordinateRoot
    (roots : ℕ → ℝ) (hroots : roots ∈ hillGapRootBox q hq hr)
    (n m : ℕ) (hn : 1 ≤ n) (hm : 1 ≤ m) (hmn : m ≠ n) :
    AnalyticAt ℂ (hillAbelianComplexCoordinateRoot q hq hr n m)
      (hillGapRootHilbertCoordinates q hq hr roots hroots,SpectralWeight.one.toCoeff q) := by
  let a := hillGapRootHilbertCoordinates q hq hr roots hroots
  have h0 := analyticAt_hillAbelianComplexUpdatedPeriod q hq hr n m hm 0 a
  have h1 := analyticAt_hillAbelianComplexUpdatedPeriod q hq hr n m hm 1 a
  apply h0.neg.div (h1.sub h0)
  simp only [Pi.sub_apply]
  rw [hillAbelianComplexUpdatedPeriod_difference_at_base q hq hr n m hm hmn a]
  exact hillAbelianRootSlope_period_ne_zero q hq hr roots hroots n m hn hm

theorem hillAbelianComplexCoordinateRoot_at_base
    (roots : ℕ → ℝ) (hroots : roots ∈ hillGapRootBox q hq hr)
    (n m : ℕ) (hm : 1 ≤ m) (hmn : m ≠ n) :
    hillAbelianComplexCoordinateRoot q hq hr n m
      (hillGapRootHilbertCoordinates q hq hr roots hroots,SpectralWeight.one.toCoeff q) =
        hillAbelianPeriodRoot q hq hr roots hroots n m := by
  rw [hillAbelianComplexCoordinateRoot,
    hillAbelianComplexUpdatedPeriod_difference_at_base q hq hr n m hm hmn,
    hillAbelianComplexUpdatedPeriod_at_base q hq hr n m hm 0]
  rfl

theorem hillAbelianComplexUpdatedIntegrand_circleIntegrable
    (n m : ℕ) (hm : 1 ≤ m) (s : ℂ) (t : Coeff 2 × Coeff 2)
    (hdom : ∀ E ∈ sphere (hillRealGapCenter q hq hr m : ℂ)
      (hillRealGapHalfLength q hq hr m+hillRealGapCollar q hq hr m),
      (E,t.2) ∈ hillAbelianComplexRootDomain q hq hr) :
    CircleIntegrable (fun E => hillAbelianHilbertPsi n (E,hillAbelianRootUpdate m (t.1,s))/
      hillAbelianComplexRoot q hq hr (E,t.2)) (hillRealGapCenter q hq hr m : ℂ)
        (hillRealGapHalfLength q hq hr m+hillRealGapCollar q hq hr m) := by
  apply ContinuousOn.circleIntegrable
    (add_nonneg (hillRealGapContour_geometry q hq hr m hm).1 (hillRealGapContour_geometry q hq hr m hm).2.1.le)
  intro E hE
  have hN : AnalyticAt ℂ (fun z : ℂ => hillAbelianHilbertPsi n (z,hillAbelianRootUpdate m (t.1,s))) E :=
    (analyticOnNhd_hillAbelianHilbertPsi n (E,hillAbelianRootUpdate m (t.1,s)) (mem_univ _)).comp
      (f := fun z : ℂ => (z,hillAbelianRootUpdate m (t.1,s))) (analyticAt_id.prod analyticAt_const)
  have hD : AnalyticAt ℂ (fun z : ℂ => hillAbelianComplexRoot q hq hr (z,t.2)) E :=
    (analyticOnNhd_hillAbelianComplexRoot q hq hr (E,t.2) (hdom E hE)).comp
      (f := fun z : ℂ => (z,t.2)) (analyticAt_id.prod analyticAt_const)
  exact (hN.div hD (hillAbelianComplexRoot_ne_zero q hq hr (E,t.2) (hdom E hE))).continuousAt.continuousWithinAt

theorem hillAbelianComplexUpdatedPeriod_affine
    (n m : ℕ) (hm : 1 ≤ m) (hmn : m ≠ n) (s : ℂ) (t : Coeff 2 × Coeff 2)
    (hdom : ∀ E ∈ sphere (hillRealGapCenter q hq hr m : ℂ)
      (hillRealGapHalfLength q hq hr m+hillRealGapCollar q hq hr m),
      (E,t.2) ∈ hillAbelianComplexRootDomain q hq hr) :
    hillAbelianComplexUpdatedPeriod q hq hr n m s t =
      s*hillAbelianComplexUpdatedPeriod q hq hr n m 1 t+
        (1-s)*hillAbelianComplexUpdatedPeriod q hq hr n m 0 t := by
  have he : (fun E => hillAbelianHilbertPsi n (E,hillAbelianRootUpdate m (t.1,s))/hillAbelianComplexRoot q hq hr (E,t.2)) =
      (fun E => s*(hillAbelianHilbertPsi n (E,hillAbelianRootUpdate m (t.1,1)) /hillAbelianComplexRoot q hq hr (E,t.2))+
        (1-s)*(hillAbelianHilbertPsi n (E,hillAbelianRootUpdate m (t.1,0))/hillAbelianComplexRoot q hq hr (E,t.2))) := by
    funext E
    rw [hillAbelianHilbertPsi_rootUpdate_eq_rootSlope n m hm hmn E t.1 s,
      hillAbelianHilbertPsi_rootUpdate_eq_rootSlope n m hm hmn E t.1 1,
      hillAbelianHilbertPsi_rootUpdate_eq_rootSlope n m hm hmn E t.1 0]
    ring
  have h1 := (hillAbelianComplexUpdatedIntegrand_circleIntegrable q hq hr n m hm 1 t hdom).const_fun_smul (a := s)
  have h0 := (hillAbelianComplexUpdatedIntegrand_circleIntegrable q hq hr n m hm 0 t hdom).const_fun_smul (a := (1-s))
  simp only [smul_eq_mul] at h1 h0
  unfold hillAbelianComplexUpdatedPeriod hillAbelianComplexPeriod
  rw [he,circleIntegral.integral_add h1 h0,circleIntegral.integral_const_mul,circleIntegral.integral_const_mul]
  ring

theorem hillAbelianComplexCoordinateRoot_period_zero
    (n m : ℕ) (hm : 1 ≤ m) (hmn : m ≠ n) (t : Coeff 2 × Coeff 2)
    (hdom : ∀ E ∈ sphere (hillRealGapCenter q hq hr m : ℂ)
      (hillRealGapHalfLength q hq hr m+hillRealGapCollar q hq hr m),
      (E,t.2) ∈ hillAbelianComplexRootDomain q hq hr)
    (hne : hillAbelianComplexUpdatedPeriod q hq hr n m 1 t-
      hillAbelianComplexUpdatedPeriod q hq hr n m 0 t ≠ 0) :
    hillAbelianComplexUpdatedPeriod q hq hr n m (hillAbelianComplexCoordinateRoot q hq hr n m t) t = 0 := by
  rw [hillAbelianComplexUpdatedPeriod_affine q hq hr n m hm hmn _ t hdom,hillAbelianComplexCoordinateRoot]
  field_simp
  ring

theorem eventually_hillAbelianComplexCoordinateRoot_period_zero
    (roots : ℕ → ℝ) (hroots : roots ∈ hillGapRootBox q hq hr)
    (n m : ℕ) (hn : 1 ≤ n) (hm : 1 ≤ m) (hmn : m ≠ n) :
    ∀ᶠ t : Coeff 2 × Coeff 2 in
      𝓝 (hillGapRootHilbertCoordinates q hq hr roots hroots,SpectralWeight.one.toCoeff q),
      hillAbelianComplexUpdatedPeriod q hq hr n m (hillAbelianComplexCoordinateRoot q hq hr n m t) t = 0 := by
  let a := hillGapRootHilbertCoordinates q hq hr roots hroots
  obtain ⟨U,hU,hqU,hcircle⟩ := exists_hillAbelianComplexRoot_contour_neighborhood q hq hr m hm
  have hden : hillAbelianComplexUpdatedPeriod q hq hr n m 1 (a,SpectralWeight.one.toCoeff q)-
      hillAbelianComplexUpdatedPeriod q hq hr n m 0 (a,SpectralWeight.one.toCoeff q) ≠ 0 := by
    rw [hillAbelianComplexUpdatedPeriod_difference_at_base q hq hr n m hm hmn a]
    exact hillAbelianRootSlope_period_ne_zero q hq hr roots hroots n m hn hm
  have hc : ContinuousAt (fun t : Coeff 2 × Coeff 2 => hillAbelianComplexUpdatedPeriod q hq hr n m 1 t-
      hillAbelianComplexUpdatedPeriod q hq hr n m 0 t) (a,SpectralWeight.one.toCoeff q) :=
    (analyticAt_hillAbelianComplexUpdatedPeriod q hq hr n m hm 1 a).continuousAt.sub
      (analyticAt_hillAbelianComplexUpdatedPeriod q hq hr n m hm 0 a).continuousAt
  have hnear : ∀ᶠ t : Coeff 2 × Coeff 2 in 𝓝 (a,SpectralWeight.one.toCoeff q), t.2 ∈ U :=
    continuous_snd.continuousAt.eventually (hU.mem_nhds hqU)
  filter_upwards [hc.eventually_ne hden,hnear] with t ht htp
  exact hillAbelianComplexCoordinateRoot_period_zero q hq hr n m hm hmn t (hcircle t.2 htp) ht

end NLS.KdV
