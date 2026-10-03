import NLS.ZakharovShabat.SourceAbelianGlobalPrimitive
import NLS.ZakharovShabat.SourceAbelianFloquetIdentity

/-! # Global endpoint limits, path integrals, and Floquet normalization

The real-source global primitive has the prescribed endpoint values for
all approaches off the cuts, integrates the actual quotient along every
smooth path in that domain, and exponentiates to the Floquet multiplier.
-/
noncomputable section
open Set Metric Filter Topology Complex NLS.ComplexAnalysis
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- Lemma 19.1(ii)'s full cut-complement endpoint limits for real sources,
including collapsed gaps and every signed index. -/
theorem sourceAbelianGlobalPrimitive_endpoint_limit
    (hp : p ≠ ⊤) (hp1 : 1 < p) (φ : CoeffPair p)
    (hφ : IsRealType (CoeffPair.toMax p φ)) (n : ℤ) (a : ℂ)
    (ha : a ∈ ({canonicalPeriodicLeft hp hp1 (periodOnePotential φ) (periodOnePotential_mem φ) n,
      canonicalPeriodicRight hp hp1 (periodOnePotential φ) (periodOnePotential_mem φ) n} : Set ℂ)) :
    Tendsto (sourceAbelianGlobalPrimitive hp hp1 φ hφ)
      (𝓝[sourceCanonicalRootDomain hp hp1 φ] a) (𝓝 (-I*(Real.pi : ℂ)*n)) := by
  obtain ⟨D⟩ := nonempty_sourceAbelianDiscPrimitive hp hp1 φ hφ n
  have haball : a ∈ ball D.center D.radius := by
    rcases (by simpa only [mem_insert_iff,mem_singleton_iff] using ha) with rfl | rfl
    · exact D.segment_subset (left_mem_segment ℝ _ _)
    · exact D.segment_subset (right_mem_segment ℝ _ _)
  have hset : ball D.center D.radius ∩ sourceCanonicalRootDomain hp hp1 φ =
      ball D.center D.radius ∩ D.extensionDomain := by
    rw [D.ball_inter_extensionDomain]
    ext z
    exact ⟨fun hz => ⟨hz.1,hz.2 n⟩,
      fun hz => ⟨hz.1,D.extensionDomain_subset_rootDomain (Or.inr hz)⟩⟩
  have hf : 𝓝[sourceCanonicalRootDomain hp hp1 φ] a = 𝓝[D.extensionDomain] a := by
    calc
      _ = 𝓝[ball D.center D.radius ∩ sourceCanonicalRootDomain hp hp1 φ] a :=
        (nhdsWithin_inter_of_mem (nhdsWithin_le_nhds (isOpen_ball.mem_nhds haball))).symm
      _ = 𝓝[ball D.center D.radius ∩ D.extensionDomain] a := by rw [hset]
      _ = _ := nhdsWithin_inter_of_mem (nhdsWithin_le_nhds (isOpen_ball.mem_nhds haball))
  rw [hf]
  apply (D.zeroNormalizedExtension_endpoint_limit a ha).congr'
  filter_upwards [self_mem_nhdsWithin] with z hz
  exact (sourceAbelianGlobalPrimitive_eq_disc hp hp1 φ hφ n D hz).symm

/-- Integrability and the fundamental theorem hold along every smooth
path off the cuts, even when it crosses many real spectral bands. -/
theorem sourceAbelianGlobalPrimitive_pathIntegral_eq_sub
    (hp : p ≠ ⊤) (hp1 : 1 < p) (φ : CoeffPair p)
    (hφ : IsRealType (CoeffPair.toMax p φ)) {a b : ℂ}
    (γ : Path a b) (hγ : ContDiffOn ℝ 1 γ.extend (Icc 0 1))
    (hγD : ∀ t : unitInterval, γ t ∈ sourceCanonicalRootDomain hp hp1 φ) :
    CurveIntegrable (holomorphicOneForm (fun z =>
      deriv (canonicalDiscriminant hp (periodOnePotential φ)) z / sourceCanonicalRoot hp hp1 φ z)) γ ∧
    (∫ᶜ z in γ, holomorphicOneForm (fun w =>
      deriv (canonicalDiscriminant hp (periodOnePotential φ)) w / sourceCanonicalRoot hp hp1 φ w) z) =
        sourceAbelianGlobalPrimitive hp hp1 φ hφ b-sourceAbelianGlobalPrimitive hp hp1 φ hφ a := by
  have hω : ContinuousOn (holomorphicOneForm (fun z =>
      deriv (canonicalDiscriminant hp (periodOnePotential φ)) z / sourceCanonicalRoot hp hp1 φ z))
      (sourceCanonicalRootDomain hp hp1 φ) :=
    (sourceCriticalRootRatio_analyticOnNhd hp hp1 φ).continuousOn.smul continuousOn_const
  have hint := hω.curveIntegrable_of_contDiffOn hγ hγD
  exact ⟨hint,curveIntegral_eq_sub_of_primitive _ (sourceAbelianGlobalPrimitive hp hp1 φ hφ)
    (sourceCanonicalRootDomain hp hp1 φ) (sourceAbelianGlobalPrimitive_hasDerivAt hp hp1 φ hφ)
    γ hγ (fun t ht => by simpa only [Path.extend_apply γ ht] using hγD ⟨t,ht⟩) hint⟩

/-- A full closed path has zero period without any homotopy supplied
by the caller. -/
theorem sourceAbelianGlobalPrimitive_closedPath_integral_zero
    (hp : p ≠ ⊤) (hp1 : 1 < p) (φ : CoeffPair p)
    (hφ : IsRealType (CoeffPair.toMax p φ)) {a : ℂ}
    (γ : Path a a) (hγ : ContDiffOn ℝ 1 γ.extend (Icc 0 1))
    (hγD : ∀ t : unitInterval, γ t ∈ sourceCanonicalRootDomain hp hp1 φ) :
    (∫ᶜ z in γ, holomorphicOneForm (fun w =>
      deriv (canonicalDiscriminant hp (periodOnePotential φ)) w / sourceCanonicalRoot hp hp1 φ w) z) = 0 := by
  simpa only [sub_self] using
    (sourceAbelianGlobalPrimitive_pathIntegral_eq_sub hp hp1 φ hφ γ hγ hγD).2

/-- The global primitive is an exact analytic logarithm of the actual
Floquet multiplier throughout the cut complement. -/
theorem sourceAbelianGlobalPrimitive_exp
    (hp : p ≠ ⊤) (hp1 : 1 < p) (φ : CoeffPair p)
    (hφ : IsRealType (CoeffPair.toMax p φ)) (z : ℂ)
    (hz : z ∈ sourceCanonicalRootDomain hp hp1 φ) :
    exp (sourceAbelianGlobalPrimitive hp hp1 φ hφ z) = sourceFloquetMultiplier hp hp1 φ z := by
  have hhalf (upper : Bool) (w : ℂ) (hw : w ∈ sourceAbelianHalfPlane upper) :
      exp (sourceAbelianGlobalPrimitive hp hp1 φ hφ w) = sourceFloquetMultiplier hp hp1 φ w := by
    rw [sourceAbelianGlobalPrimitive_eq_halfPlane hp hp1 φ hφ upper hw]
    simpa only [sourceAbelianGapSign,Int.zero_emod,ite_true,one_mul] using
      sourceAbelianHalfPlanePrimitive_exp hp hp1 φ hφ 0 upper w hw
  by_cases hu : 0 < z.im
  · exact hhalf true z hu
  by_cases hl : z.im < 0
  · exact hhalf false z hl
  have hU := isOpen_sourceCanonicalRootDomain_of_realType hp hp1 φ hφ
  exact eq_at_real_of_upperHalfPlane_extension
    (fun w => exp (sourceAbelianGlobalPrimitive hp hp1 φ hφ w))
    (sourceFloquetMultiplier hp hp1 φ) (sourceFloquetMultiplier hp hp1 φ)
    _ _ z (le_antisymm (le_of_not_gt hu) (le_of_not_gt hl)) hU hU hz hz
    (continuous_exp.continuousAt.comp
      (sourceAbelianGlobalPrimitive_hasDerivAt hp hp1 φ hφ z hz).continuousAt)
    (sourceFloquetMultiplier_analyticOnNhd hp hp1 φ z hz).continuousAt
    (fun w hw => hhalf true w hw.2) (fun _ _ => rfl)

/-- At the zero source, the full global primitive is exactly `-i*z`,
including real band points. -/
theorem sourceAbelianGlobalPrimitive_zero
    (hp : p ≠ ⊤) (hp1 : 1 < p) :
    EqOn (sourceAbelianGlobalPrimitive hp hp1 (0 : CoeffPair p) (by simp))
      (fun z => -I*z) (sourceCanonicalRootDomain hp hp1 0) := by
  intro z hz
  have hhalf (upper : Bool) (w : ℂ) (hw : w ∈ sourceAbelianHalfPlane upper) :
      sourceAbelianGlobalPrimitive hp hp1 (0 : CoeffPair p) (by simp) w = -I*w := by
    rw [sourceAbelianGlobalPrimitive_eq_halfPlane hp hp1 0 (by simp) upper hw]
    simpa only [Int.cast_zero,mul_zero,add_zero] using sourceAbelianHalfPlanePrimitive_zero hp hp1 0 upper hw
  by_cases hu : 0 < z.im
  · exact hhalf true z hu
  by_cases hl : z.im < 0
  · exact hhalf false z hl
  have hU := isOpen_sourceCanonicalRootDomain_of_realType hp hp1 (0 : CoeffPair p) (by simp)
  exact eq_at_real_of_upperHalfPlane_extension _ (fun w => -I*w) (fun w => -I*w) _ _ z
    (le_antisymm (le_of_not_gt hu) (le_of_not_gt hl)) hU hU hz hz
    (sourceAbelianGlobalPrimitive_hasDerivAt hp hp1 0 (by simp) z hz).continuousAt
    (continuous_const.mul continuous_id).continuousAt
    (fun w hw => hhalf true w hw.2) (fun _ _ => rfl)

end NLS.ZakharovShabat
