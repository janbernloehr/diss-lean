import NLS.ZakharovShabat.SourceResolventContours
import NLS.ZakharovShabat.SourceCorollary3_5

/-! # Equation (1.4) on a common original-norm neighborhood -/
noncomputable section
open Complex Metric
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- Every sufficiently large actual central rectangle gives an analytic
projection on a single source neighborhood containing the potential and zero. -/
theorem exists_uniform_sourceCentralRectangleIntegral (hp : p ≠ ⊤) (φ : CoeffPair p) :
    ∃ N₀ : ℕ, ∃ U : Set (CoeffPair p), 0 < N₀ ∧ IsOpen U ∧ Convex ℝ U ∧ φ ∈ U ∧ 0 ∈ U ∧
      (∀ N : ℕ, N₀ ≤ N → AnalyticOnNhd ℂ (fun ψ => sourceCentralRectangleIntegral hp ψ N) U) ∧
      ∀ ψ ∈ U, ∀ N : ℕ, N₀ ≤ N →
        centralRectangleBoundary N ⊆ sourceResolventSet hp ψ ∧ IsIdempotentElem (sourceCentralRectangleIntegral hp ψ N) := by
  obtain ⟨N₀,V,hN₀,ho,hconv,hφ,h0,han,h⟩ :=
    exists_uniform_centralRectangleProjection hp (CoeffPair.toMax p φ)
  let U : Set (CoeffPair p) := (CoeffPair.toMax p) ⁻¹' V
  have hU : IsOpen U := ho.preimage (CoeffPair.toMax p).continuous
  have hb (ψ : CoeffPair p) (hψ : ψ ∈ U) (N : ℕ) (hN : N₀ ≤ N) :
      centralRectangleBoundary N ⊆ sourceResolventSet hp ψ := by
    rw [sourceResolventSet_eq]
    exact (h _ hψ N hN).1
  refine ⟨N₀,U,hN₀,hU,
    hconv.linear_preimage ((CoeffPair.toMax p).toContinuousLinearMap.restrictScalars ℝ).toLinearMap,
    hφ,?_,?_,?_⟩
  · simpa only [U,Set.mem_preimage,map_zero] using h0
  · intro N hN ψ hψ
    have ha := ((CoeffPair.toMax p).symm.conjContinuousAlgEquiv.toContinuousLinearEquiv.analyticAt _).comp
      ((han N hN _ hψ).comp ((CoeffPair.toMax p).analyticAt ψ))
    apply ha.congr
    filter_upwards [hU.mem_nhds hψ] with a ha
    exact (sourceCentralRectangleIntegral_eq_conj hp a N (hb a ha N hN)).symm
  · intro ψ hψ N hN
    exact ⟨hb ψ hψ N hN,sourceCentralRectangleIntegral_idempotent hp ψ N (hb ψ hψ N hN)⟩

/-- Equation (1.4): the actual central rectangle and all distant circle
integrals are analytic finite-rank projections on one original-norm
neighborhood, valid simultaneously at every larger cutoff. -/
theorem sourceEquation1_4 (hp : p ≠ ⊤) (φ : CoeffPair p) :
    ∃ N₀ : ℕ, ∃ U : Set (CoeffPair p), 0 < N₀ ∧ IsOpen U ∧ Convex ℝ U ∧ IsConnected U ∧
      φ ∈ U ∧ 0 ∈ U ∧ ∀ N : ℕ, N₀ ≤ N →
      (AnalyticOnNhd ℂ (fun ψ => sourceCentralRectangleIntegral hp ψ N) U ∧
        ∀ ψ ∈ U, centralRectangleBoundary N ⊆ sourceResolventSet hp ψ ∧
          IsIdempotentElem (sourceCentralRectangleIntegral hp ψ N) ∧
          IsCompactOperator (sourceCentralRectangleIntegral hp ψ N) ∧
          FiniteDimensional ℂ (sourceCentralRectangleIntegral hp ψ N).range) ∧
      ∀ n : ℤ, N < n.natAbs →
        AnalyticOnNhd ℂ (fun ψ => sourceResolventCircleIntegral hp ψ ((Real.pi : ℂ)*n) (Real.pi/4)) U ∧
        ∀ ψ ∈ U, sphere ((Real.pi : ℂ)*n) (Real.pi/4) ⊆ sourceResolventSet hp ψ ∧
          IsIdempotentElem (sourceResolventCircleIntegral hp ψ ((Real.pi : ℂ)*n) (Real.pi/4)) ∧
          IsCompactOperator (sourceResolventCircleIntegral hp ψ ((Real.pi : ℂ)*n) (Real.pi/4)) ∧
          FiniteDimensional ℂ (sourceResolventCircleIntegral hp ψ ((Real.pi : ℂ)*n) (Real.pi/4)).range := by
  obtain ⟨K,V,hK,hVo,hVc,hφV,h0V,han,hcentral⟩ := exists_uniform_sourceCentralRectangleIntegral hp φ
  obtain ⟨L,W,_,hWo,hWc,hφW,h0W,hstrip⟩ := exists_source_uniform_height_and_strips hp φ
    (r := Real.pi/4) (by positivity) le_rfl
  have hconv : Convex ℝ (V ∩ W) := hVc.inter hWc
  refine ⟨max K L,V ∩ W,hK.trans_le (le_max_left _ _),hVo.inter hWo,hconv,
    ⟨⟨0,⟨h0V,h0W⟩⟩,hconv.isPreconnected⟩,⟨hφV,hφW⟩,⟨h0V,h0W⟩,?_⟩
  intro N hN
  have hKN : K ≤ N := (le_max_left _ _).trans hN
  refine ⟨⟨(han N hKN).mono Set.inter_subset_left,?_⟩,?_⟩
  · intro ψ hψ
    have hb := (hcentral ψ hψ.1 N hKN).1
    exact ⟨hb,sourceCentralRectangleIntegral_idempotent hp ψ N hb,
      isCompactOperator_sourceCentralRectangleIntegral hp ψ N hb,
      finiteDimensional_range_sourceCentralRectangleIntegral hp ψ N hb⟩
  · intro n hn
    have hLn : L ≤ n.natAbs := ((le_max_right _ _).trans hN).trans hn.le
    have hb (ψ : CoeffPair p) (hψ : ψ ∈ V ∩ W) :
        sphere ((Real.pi : ℂ)*n) (Real.pi/4) ⊆ sourceResolventSet hp ψ :=
      (sphere_subset_verticalStrip n le_rfl).trans ((hstrip ψ hψ.2).2 n hLn)
    refine ⟨fun ψ hψ => analyticAt_sourceResolventCircleIntegral hp ψ _ _ (by positivity) (hb ψ hψ),?_⟩
    intro ψ hψ
    exact ⟨hb ψ hψ,sourceResolventCircleIntegral_idempotent hp ψ _ _ (by positivity) (hb ψ hψ),
      isCompactOperator_sourceResolventCircleIntegral hp ψ _ _ (by positivity) (hb ψ hψ),
      finiteDimensional_range_sourceResolventCircleIntegral hp ψ _ _ (by positivity) (hb ψ hψ)⟩

end NLS.ZakharovShabat
