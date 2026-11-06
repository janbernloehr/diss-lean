import NLS.MKdV.MiuraCanonicalHillSheets
import NLS.ComplexAnalysis.ConvexHolomorphicPrimitive

/-! # Endpoint normalization and actual physical Hill path integrals

The independent filled primitive has its exact signed endpoint constants.
At the lowest Hill endpoint its full relative limit is zero, so every
smooth integrable connector in the physical gap complement gives the
source's normalized abelian path integral.
-/
noncomputable section
open Set Complex Filter Topology NLS.ComplexAnalysis NLS.KdV NLS.ZakharovShabat
open scoped ENNReal ComplexConjugate
namespace NLS.MKdV

theorem canonicalMiuraHillPrimitive_endpoint_limit (a : ScalarDomain 2)
    (ha : ∀ n, a.val n = conj (a.val (-n))) (n : ℤ) (ζ : ℂ)
    (hζ : ζ = miuraNLSLeft a n ∨ ζ = miuraNLSRight a n) (hζpos : 0 ≤ ζ.re) :
    Tendsto (canonicalMiuraHillPrimitive a) (𝓝[miuraHillGapComplement a ha] (ζ^2))
      (𝓝 (-I*(Real.pi : ℂ)*n)) := by
  have hi : ζ.im = 0 := by
    rcases hζ with rfl | rfl
    · exact (miuraNLSEndpoints_real a ha n).1
    · exact (miuraNLSEndpoints_real a ha n).2
  have hs : Complex.sqrt (ζ^2) = ζ := by
    by_cases he : ζ.re = 0
    · have hz : ζ = 0 := Complex.ext he hi
      simp [hz]
    · exact sqrt_sq_of_re_pos ζ (lt_of_le_of_ne hζpos (Ne.symm he))
  have hre : 0 ≤ (ζ^2).re := by
    simpa only [pow_two,mul_re,hi,mul_zero,sub_zero] using mul_self_nonneg ζ.re
  have hc := Complex.continuousAt_sqrt (Or.inl hre)
  have hmap : Tendsto Complex.sqrt (𝓝[miuraHillGapComplement a ha] (ζ^2))
      (𝓝[sourceOpenGapComplement (by simp) (by norm_num) (realDiagonalH1Source a ha).val] ζ) := by
    apply tendsto_nhdsWithin_iff.mpr
    constructor
    · simpa only [hs] using hc.tendsto.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with w hw
      exact sourceCanonicalRootDomain_subset_openGapComplement _ _ _
        (miuraHillGapComplement_sqrt a ha w hw).2.2
  have hmem : ζ ∈ ({canonicalPeriodicLeft (by simp) (by norm_num)
        (periodOnePotential (realDiagonalH1Source a ha).val) (periodOnePotential_mem _) n,
      canonicalPeriodicRight (by simp) (by norm_num)
        (periodOnePotential (realDiagonalH1Source a ha).val) (periodOnePotential_mem _) n} : Set ℂ) := by
    simpa only [Set.mem_insert_iff,Set.mem_singleton_iff,miuraNLSLeft,miuraNLSRight,
      realDiagonalH1Source] using hζ
  have ht := (sourceAbelianPrimitive_endpoint_limit (by simp) (by norm_num)
    (realDiagonalH1Source a ha).val (realDiagonalH1Source a ha).property n ζ hmem).comp hmap
  apply ht.congr'
  filter_upwards [self_mem_nhdsWithin] with w hw
  have hsw := miuraHillGapComplement_sqrt a ha w hw
  have he := (canonicalMiuraHillSheets_eq_NLS a ha (Complex.sqrt w) hsw.2.1 hsw.2.2).2
  simpa only [complex_sqrt_sq,Function.comp_def] using! he.symm

theorem canonicalMiuraHillPrimitive_ground_limit (a : ScalarDomain 2)
    (ha : ∀ n, a.val n = conj (a.val (-n))) :
    Tendsto (canonicalMiuraHillPrimitive a)
      (𝓝[miuraHillGapComplement a ha] (miuraHillLabels a ha 0 : ℂ)) (𝓝 0) := by
  have h := canonicalMiuraHillPrimitive_endpoint_limit a ha 0 (miuraNLSRight a 0)
    (Or.inr rfl) (miuraNLSRight_zero_nonnegative a)
  simpa only [Int.cast_zero,mul_zero,(miuraHillLabels_ground_complex a ha).1] using h

/-- The source's physical abelian path integral, normalized at the
actual ground energy, for every admissible smooth integrable path. -/
theorem canonicalMiuraHillPrimitive_eq_pathIntegral (a : ScalarDomain 2)
    (ha : ∀ n, a.val n = conj (a.val (-n))) {μ : ℂ}
    (γ : Path (miuraHillLabels a ha 0 : ℂ) μ)
    (hγ : ContDiffOn ℝ 1 γ.extend (Icc 0 1))
    (hγs : ∀ t ∈ Ioo (0 : ℝ) 1, γ.extend t ∈ miuraHillGapComplement a ha)
    (hμ : μ ∈ miuraHillGapComplement a ha)
    (hint : CurveIntegrable (holomorphicOneForm (fun w =>
      deriv (hillL2Discriminant (sobolevMiuraHillPotential a)) w / canonicalMiuraHillRoot a w)) γ) :
    (∫ᶜ w in γ, holomorphicOneForm (fun w =>
      deriv (hillL2Discriminant (sobolevMiuraHillPotential a)) w / canonicalMiuraHillRoot a w) w) =
        canonicalMiuraHillPrimitive a μ := by
  simpa only [sub_zero] using curveIntegral_eq_sub_of_primitive_boundary_start _ _ _
    (fun w hw => hasDerivAt_canonicalMiuraHillPrimitive a ha w hw) γ hγ hγs hμ hint
    (canonicalMiuraHillPrimitive_ground_limit a ha)

end NLS.MKdV
