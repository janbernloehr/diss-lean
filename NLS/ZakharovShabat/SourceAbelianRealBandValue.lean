import NLS.ZakharovShabat.SourceAbelianPrimitiveProperties
import NLS.ZakharovShabat.SourceRealBandArcsin

/-! # Exact values of the normalized abelian integral on real bands

The actual primitive equals the arcsine expression with its endpoint
constant fixed exactly. This supplies a continuous normalization as
both the real spectral point and the real source vary within a band.
-/
noncomputable section
open Set Filter Topology Complex NLS.ComplexAnalysis
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The global primitive on band `n` is its explicit arcsine primitive
minus `i*pi/2 + i*n*pi`. All signed indices are included. -/
theorem sourceAbelianPrimitive_eq_arcsin_on_band
    (hp : p ≠ ⊤) (hp1 : 1 < p) (φ : CoeffPair p)
    (hφ : IsRealType (CoeffPair.toMax p φ)) (n : ℤ) (x : ℝ)
    (hx : x ∈ sourceRealBand hp hp1 φ n) :
    sourceAbelianPrimitive hp hp1 φ hφ (x : ℂ) =
      sourceRealBandArcsinPrimitive hp φ n x-I*(Real.pi : ℂ)/2-I*(Real.pi : ℂ)*n := by
  let a := (canonicalPeriodicRight hp hp1 (periodOnePotential φ) (periodOnePotential_mem φ) n).re
  let b := (canonicalPeriodicLeft hp hp1 (periodOnePotential φ) (periodOnePotential_mem φ) (n+1)).re
  let F := sourceAbelianPrimitive hp hp1 φ hφ
  let P := sourceRealBandArcsinPrimitive hp φ n
  have hd (t : ℝ) (ht : t ∈ sourceRealBand hp hp1 φ n) : HasDerivAt (fun t : ℝ => F t-P t) 0 t := by
    simpa only [F,P,Pi.sub_apply,sub_self] using!
      (sourceAbelianPrimitive_hasDerivAt_quotient hp hp1 φ hφ t
        (sourceRealBand_subset_rootDomain hp hp1 φ hφ n t ht)).comp_ofReal.sub
        (hasDerivAt_sourceRealBandArcsinPrimitive hp hp1 φ hφ n t ht)
  obtain ⟨C,hC⟩ := isOpen_Ioo.exists_is_const_of_deriv_eq_zero isPreconnected_Ioo
    (show DifferentiableOn ℝ (fun t : ℝ => F t-P t) (sourceRealBand hp hp1 φ n) from
      fun t ht => (hd t ht).differentiableAt.differentiableWithinAt)
    (fun t ht => (hd t ht).deriv)
  have hab : a < b := canonicalPeriodicRight_re_lt_next_left hp hp1 (periodOnePotential φ)
    (periodOnePotential_mem φ) (isRealType_periodOnePotential φ hφ) n
  let : NeBot (𝓝[sourceRealBand hp hp1 φ n] a) := left_nhdsWithin_Ioo_neBot hab
  have hareal : (a : ℂ) = canonicalPeriodicRight hp hp1 (periodOnePotential φ) (periodOnePotential_mem φ) n :=
    Complex.ext rfl (canonicalPeriodicEndpoints_im_eq_zero_of_realType hp hp1 (periodOnePotential φ)
      (periodOnePotential_mem φ) (isRealType_periodOnePotential φ hφ) n).2.symm
  have hmap : Tendsto (fun t : ℝ => (t : ℂ)) (𝓝[sourceRealBand hp hp1 φ n] a)
      (𝓝[sourceOpenGapComplement hp hp1 φ] (a : ℂ)) := by
    apply tendsto_nhdsWithin_iff.mpr
    refine ⟨continuous_ofReal.continuousAt.tendsto.mono_left nhdsWithin_le_nhds,?_⟩
    filter_upwards [self_mem_nhdsWithin] with t ht
    exact sourceCanonicalRootDomain_subset_openGapComplement hp hp1 φ
      (sourceRealBand_subset_rootDomain hp hp1 φ hφ n t ht)
  have hlim : Tendsto (fun t : ℝ => F t) (𝓝[sourceRealBand hp hp1 φ n] a) (𝓝 (-I*(Real.pi : ℂ)*n)) := by
    apply (sourceAbelianPrimitive_endpoint_limit hp hp1 φ hφ n (a : ℂ) (by rw [hareal]; simp)).comp hmap
  have hpLim : Tendsto (fun t : ℝ => F t) (𝓝[sourceRealBand hp hp1 φ n] a) (𝓝 (P a+C)) := by
    have hc : Continuous (fun t : ℝ => P t+C) :=
      (continuous_sourceRealBandArcsinPrimitive hp hp1 φ n).add continuous_const
    apply (hc.continuousAt.tendsto.mono_left nhdsWithin_le_nhds).congr'
    filter_upwards [self_mem_nhdsWithin] with t ht
    have he := hC t ht
    linear_combination -he
  have he := tendsto_nhds_unique hlim hpLim
  have hPa : P a = I*(Real.pi : ℂ)/2 := sourceRealBandArcsinPrimitive_left hp hp1 φ hφ n
  rw [hPa] at he
  have hvalue := hC x hx
  change F x = P x-I*(Real.pi : ℂ)/2-I*(Real.pi : ℂ)*n
  linear_combination hvalue-he

/-- The real-band normalization has a globally continuous expression
in real spectral coordinate and unrestricted complex source. Its
agreement with the primitive is asserted only for real sources in the band. -/
theorem continuous_sourceRealBandArcsinPrimitive_joint
    (hp : p ≠ ⊤) (hp1 : 1 < p) (n : ℤ) :
    Continuous (fun t : ℝ × CoeffPair p => sourceRealBandArcsinPrimitive hp t.2 n t.1) := by
  have hc : Continuous (fun t : ℂ × CoeffPair p => canonicalDiscriminant hp (periodOnePotential t.2) t.1) :=
    continuousOn_univ.mp (analyticOnNhd_canonicalDiscriminant_periodOne hp hp1).continuousOn
  have hm : Continuous (fun t : ℝ × CoeffPair p => ((t.1 : ℂ),t.2)) :=
    (continuous_ofReal.comp continuous_fst).prodMk continuous_snd
  have hΔ : Continuous (fun t : ℝ × CoeffPair p => canonicalDiscriminant hp (periodOnePotential t.2) (t.1 : ℂ)) := by
    simpa only [Function.comp_def] using! hc.comp hm
  exact continuous_const.mul (continuous_ofReal.comp
    (Real.continuous_arcsin.comp ((continuous_re.comp hΔ).div_const 2)))

end NLS.ZakharovShabat
