import NLS.ZakharovShabat.SourceAbelianHalfPlane
import NLS.ZakharovShabat.SourcePsiFree
import NLS.ZakharovShabat.SourceIsospectralSet

/-! # Intrinsic properties of the normalized half-plane abelian integrals

The primitives are analytic in the spectral variable, evaluate actual
endpoint path integrals, commute with exponent inclusion, and are
isospectral invariants. At the zero source their exact values are
`-i λ + i n π` on both half-planes, fixing the Section 19 normalization.
-/
noncomputable section
open Set Filter Topology Complex
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p q : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ q)]

/-- Spectral analyticity on the entire selected half-plane. -/
theorem sourceAbelianHalfPlanePrimitive_analytic
    (hp : p ≠ ⊤) (hp1 : 1 < p) (φ : CoeffPair p)
    (hφ : IsRealType (CoeffPair.toMax p φ)) (n : ℤ) (upper : Bool) :
    AnalyticOnNhd ℂ (sourceAbelianHalfPlanePrimitive hp hp1 φ hφ n upper) (sourceAbelianHalfPlane upper) :=
  (show DifferentiableOn ℂ (sourceAbelianHalfPlanePrimitive hp hp1 φ hφ n upper)
    (sourceAbelianHalfPlane upper) from fun z hz =>
      ((sourceAbelianHalfPlanePrimitive_spec hp hp1 φ hφ n upper).1 z hz).differentiableAt.differentiableWithinAt).analyticOnNhd
        (isOpen_sourceAbelianHalfPlane upper)

/-- Every smooth integrable path from either gap endpoint into the chosen
half-plane evaluates to the same normalized abelian integral. -/
theorem sourceAbelianHalfPlanePrimitive_eq_pathIntegral
    (hp : p ≠ ⊤) (hp1 : 1 < p) (φ : CoeffPair p)
    (hφ : IsRealType (CoeffPair.toMax p φ)) (n : ℤ) (upper : Bool)
    {a b : ℂ} (ha : a ∈ ({canonicalPeriodicLeft hp hp1 (periodOnePotential φ) (periodOnePotential_mem φ) n,
      canonicalPeriodicRight hp hp1 (periodOnePotential φ) (periodOnePotential_mem φ) n} : Set ℂ))
    (γ : Path a b) (hγ : ContDiffOn ℝ 1 γ.extend (Icc 0 1))
    (hγs : ∀ t ∈ Ioo (0 : ℝ) 1, γ.extend t ∈ sourceAbelianHalfPlane upper)
    (hb : b ∈ sourceAbelianHalfPlane upper)
    (hint : CurveIntegrable (NLS.ComplexAnalysis.holomorphicOneForm
      (fun z => deriv (canonicalDiscriminant hp (periodOnePotential φ)) z / sourceCanonicalRoot hp hp1 φ z)) γ) :
    (∫ᶜ z in γ, NLS.ComplexAnalysis.holomorphicOneForm
      (fun w => deriv (canonicalDiscriminant hp (periodOnePotential φ)) w / sourceCanonicalRoot hp hp1 φ w) z) =
      sourceAbelianHalfPlanePrimitive hp hp1 φ hφ n upper b := by
  have hs := sourceAbelianHalfPlanePrimitive_spec hp hp1 φ hφ n upper
  have hboundary : Tendsto (sourceAbelianHalfPlanePrimitive hp hp1 φ hφ n upper)
      (𝓝[sourceAbelianHalfPlane upper] a) (𝓝 0) := by
    rcases (by simpa only [mem_insert_iff,mem_singleton_iff] using ha) with rfl | rfl
    · exact hs.2.1
    · exact hs.2.2
  simpa only [sub_zero] using NLS.ComplexAnalysis.curveIntegral_eq_sub_of_primitive_boundary_start
    _ _ (sourceAbelianHalfPlane upper) hs.1 γ hγ hγs hb hint hboundary

/-- Exponent inclusion preserves the normalized primitive, not only its derivative. -/
theorem sourceAbelianHalfPlanePrimitive_exponent
    (hp : p ≠ ⊤) (hq : q ≠ ⊤) (hp1 : 1 < p) (hq1 : 1 < q) (hpq : p ≤ q)
    (φ : realTypeSourceSubmodule p) (n : ℤ) (upper : Bool) :
    EqOn (sourceAbelianHalfPlanePrimitive hp hp1 φ.val φ.property n upper)
      (sourceAbelianHalfPlanePrimitive hq hq1 (CoeffPair.exponentInclusion hpq φ.val)
        (realTypeSourceExponentInclusion hpq φ).property n upper) (sourceAbelianHalfPlane upper) := by
  have hs := sourceAbelianHalfPlanePrimitive_spec hq hq1 (CoeffPair.exponentInclusion hpq φ.val)
    (realTypeSourceExponentInclusion hpq φ).property n upper
  have hΔ := funext (sourceDiscriminant_exponent hp hq hpq φ.val)
  apply sourceAbelianHalfPlanePrimitive_eq_of_normalized hp hp1 φ.val φ.property n upper
  · intro z hz
    rw [hΔ,sourceCanonicalRoot_exponent hp hq hp1 hq1 hpq φ.val z]
    exact hs.1 z hz
  · rw [(canonicalPeriodicEndpoints_periodOne_exponent hp hq hp1 hq1 hpq φ.val).1]
    exact hs.2.1

/-- The endpoint normalization makes every primitive an actual isospectral invariant. -/
theorem sourceAbelianHalfPlanePrimitive_eq_of_isospectral
    (hp : p ≠ ⊤) (hp1 : 1 < p) (φ ψ : realTypeSourceSubmodule p)
    (h : ψ ∈ sourceIsospectralSet hp φ) (n : ℤ) (upper : Bool) :
    EqOn (sourceAbelianHalfPlanePrimitive hp hp1 ψ.val ψ.property n upper)
      (sourceAbelianHalfPlanePrimitive hp hp1 φ.val φ.property n upper) (sourceAbelianHalfPlane upper) := by
  have hs := sourceAbelianHalfPlanePrimitive_spec hp hp1 φ.val φ.property n upper
  have hΔ := (mem_sourceIsospectralSet_iff_discriminant_eq hp hp1 φ ψ).mp h
  have he := canonicalPeriodicEndpoints_eq_of_spectral_data hp hp1
    (periodOnePotential ψ.val) (periodOnePotential φ.val) (periodOnePotential_mem _) (periodOnePotential_mem _)
    h.1 h.2
  apply sourceAbelianHalfPlanePrimitive_eq_of_normalized hp hp1 ψ.val ψ.property n upper
  · intro z hz
    rw [hΔ,sourceCanonicalRoot_eq_of_isospectral hp hp1 φ ψ h z]
    exact hs.1 z hz
  · rw [he.1]
    exact hs.2.1

/-- The free quotient has its exact canonical orientation on each half-plane. -/
theorem sourceCriticalRootRatio_zero_on_halfPlane
    (hp : p ≠ ⊤) (hp1 : 1 < p) (upper : Bool) (z : ℂ) (hz : z ∈ sourceAbelianHalfPlane upper) :
    deriv (canonicalDiscriminant hp (periodOnePotential (0 : CoeffPair p))) z /
      sourceCanonicalRoot hp hp1 (0 : CoeffPair p) z = -I := by
  have hΔ : canonicalDiscriminant hp (periodOnePotential (0 : CoeffPair p)) = freeDiscriminant := by
    funext w
    simpa only [map_zero] using canonicalDiscriminant_zero_finite hp w
  have hd : deriv freeDiscriminant z = -2*sin z := by
    convert! ((Complex.hasDerivAt_cos z).const_mul 2).deriv using 1
    ring
  have hroot := sourceCanonicalRoot_ne_zero_off_gaps hp hp1 (0 : CoeffPair p) z
    (sourceAbelianHalfPlane_subset_rootDomain hp hp1 0 (by simp) upper hz)
  rw [hΔ,hd,sourceCanonicalRoot_zero_source_eq_free_sine hp hp1 0]
  rw [sourceCanonicalRoot_zero_source_eq_free_sine hp hp1 0] at hroot
  apply (div_eq_iff hroot).mpr
  linear_combination -2*sin z*Complex.I_mul_I

/-- Lemma 19.1(vi) on both complete half-planes, for every signed index. -/
theorem sourceAbelianHalfPlanePrimitive_zero
    (hp : p ≠ ⊤) (hp1 : 1 < p) (n : ℤ) (upper : Bool) :
    EqOn (sourceAbelianHalfPlanePrimitive hp hp1 (0 : CoeffPair p) (by simp) n upper)
      (fun z => -I*z+I*(Real.pi : ℂ)*n) (sourceAbelianHalfPlane upper) := by
  apply sourceAbelianHalfPlanePrimitive_eq_of_normalized
  · intro z hz
    rw [sourceCriticalRootRatio_zero_on_halfPlane hp hp1 upper z hz]
    convert! ((hasDerivAt_id z).const_mul (-I)).add_const (I*(Real.pi : ℂ)*n) using 1
    simp
  · have hc : Continuous (fun z : ℂ => -I*z+I*(Real.pi : ℂ)*n) :=
      (continuous_const.mul continuous_id).add continuous_const
    have ht : Tendsto (fun z : ℂ => -I*z+I*(Real.pi : ℂ)*n)
        (𝓝[sourceAbelianHalfPlane upper] ((Real.pi : ℂ)*n))
        (𝓝 (-I*((Real.pi : ℂ)*n)+I*(Real.pi : ℂ)*n)) :=
      hc.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
    simpa only [map_zero,canonicalPeriodicLeft_zero,show -I*((Real.pi : ℂ)*n)+I*(Real.pi : ℂ)*n = 0 by ring] using ht

end NLS.ZakharovShabat
