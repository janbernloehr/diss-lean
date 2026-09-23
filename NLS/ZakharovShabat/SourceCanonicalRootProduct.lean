import NLS.ZakharovShabat.SourceStandardRootOmittedJointAnalytic
import NLS.ZakharovShabat.PeriodicEndpointProducts
import NLS.ZakharovShabat.FiniteParityCompatibility

/-!
# The canonical root as the full standard-root product

Equation (2.13) uses the factor `2i` and the exceptional central
normalization `π₀ = 1`. Symmetric finite products factor through every
arbitrary-index omitted product of Lemma 10.5. This identifies their
pointwise limit, including at spectral zeros, and supplies the local
factorization needed for Lemma 10.7.
-/

noncomputable section
open Set Filter Topology Complex
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- Literal symmetric finite cutoff of the full canonical root. -/
def sourceCanonicalRootPartialProduct (hp : p ≠ ⊤) (hp1 : 1 < p)
    (N : ℕ) (ψ : CoeffPair p) (z : ℂ) : ℂ :=
  2*I * ∏ m ∈ Finset.Icc (-(N : ℤ)) (N : ℤ),
    sourceStandardRoot hp hp1 ψ m z / singleSpectralDenominator m

/-- The full product in equation (2.13), split at the central mode. -/
def sourceCanonicalRoot (hp : p ≠ ⊤) (hp1 : 1 < p)
    (ψ : CoeffPair p) (z : ℂ) : ℂ :=
  2*I * sourceStandardRoot hp hp1 ψ 0 z *
    sourceStandardRootPairedProduct hp hp1 ψ z

/-- The spectral domain outside every closed canonical periodic gap. -/
def sourceCanonicalRootDomain (hp : p ≠ ⊤) (hp1 : 1 < p)
    (ψ : CoeffPair p) : Set ℂ :=
  {z | ∀ n : ℤ, z ∉ sourcePeriodicSegment hp hp1 ψ n}

/-- Restoring any one omitted factor gives the literal full cutoff. -/
theorem sourceCanonicalRootPartialProduct_eq_omitted
    (hp : p ≠ ⊤) (hp1 : 1 < p) (n : ℤ) (N : ℕ)
    (hn : n.natAbs ≤ N) (ψ : CoeffPair p) (z : ℂ) :
    sourceCanonicalRootPartialProduct hp hp1 N ψ z =
      2*I * sourceStandardRoot hp hp1 ψ n z *
        sourceStandardRootOmittedPartialProduct hp hp1 n N (z,ψ) := by
  have hm : n ∈ Finset.Icc (-(N : ℤ)) (N : ℤ) := by
    simp only [Finset.mem_Icc]
    constructor <;> omega
  unfold sourceCanonicalRootPartialProduct sourceStandardRootOmittedPartialProduct
  rw [← Finset.mul_prod_erase _ _ hm]
  have hd := singleSpectralDenominator_ne_zero n
  field_simp

/-- The full symmetric cutoffs converge at every spectral parameter,
including points on the gap segments. -/
theorem tendsto_sourceCanonicalRootPartialProduct
    (hp : p ≠ ⊤) (hp1 : 1 < p) (ψ : CoeffPair p) (z : ℂ) :
    Tendsto (fun N => sourceCanonicalRootPartialProduct hp hp1 N ψ z) atTop
      (𝓝 (sourceCanonicalRoot hp hp1 ψ z)) := by
  have h := (tendsto_sourceStandardRootOmittedPartialProduct hp hp1 0 ψ z).const_mul
    (2*I*sourceStandardRoot hp hp1 ψ 0 z)
  have he : ∀ N : ℕ,
      sourceCanonicalRootPartialProduct hp hp1 N ψ z =
        (2*I*sourceStandardRoot hp hp1 ψ 0 z) *
          sourceStandardRootOmittedPartialProduct hp hp1 0 N (z,ψ) := by
    intro N
    exact sourceCanonicalRootPartialProduct_eq_omitted hp hp1 0 N (by omega) ψ z
  simpa only [he, sourceStandardRootOmittedProduct_zero,
    sourceCanonicalRoot, mul_assoc]
    using h

/-- The full canonical root factors through the omitted product at every
index, as in equation (2.13). -/
theorem sourceCanonicalRoot_eq_omitted
    (hp : p ≠ ⊤) (hp1 : 1 < p) (n : ℤ)
    (ψ : CoeffPair p) (z : ℂ) :
    sourceCanonicalRoot hp hp1 ψ z =
      2*I * sourceStandardRoot hp hp1 ψ n z *
        sourceStandardRootOmittedProduct hp hp1 n ψ z := by
  have hfull := tendsto_sourceCanonicalRootPartialProduct hp hp1 ψ z
  have hdel := (tendsto_sourceStandardRootOmittedPartialProduct hp hp1 n ψ z).const_mul
    (2*I*sourceStandardRoot hp hp1 ψ n z)
  have he : ∀ᶠ N : ℕ in atTop,
      (2*I*sourceStandardRoot hp hp1 ψ n z) *
          sourceStandardRootOmittedPartialProduct hp hp1 n N (z,ψ) =
        sourceCanonicalRootPartialProduct hp hp1 N ψ z := by
    filter_upwards [eventually_ge_atTop n.natAbs] with N hN
    exact (sourceCanonicalRootPartialProduct_eq_omitted hp hp1 n N hN ψ z).symm
  exact tendsto_nhds_unique hfull (hdel.congr' he)

/-- At every source potential, the full canonical root is analytic in
the spectral parameter off the union of closed periodic gap segments. -/
theorem sourceCanonicalRoot_analyticOnNhd
    (hp : p ≠ ⊤) (hp1 : 1 < p) (ψ : CoeffPair p) :
    AnalyticOnNhd ℂ (sourceCanonicalRoot hp hp1 ψ)
      (sourceCanonicalRootDomain hp hp1 ψ) := by
  intro z hz
  have hzero := sourceStandardRoot_analyticAt hp hp1 ψ 0 z (hz 0)
  have hpaired := sourceStandardRootPairedProduct_analyticOnNhd hp hp1 ψ z
    (fun k _ => hz k)
  change AnalyticAt ℂ (fun w =>
    2*I * sourceStandardRoot hp hp1 ψ 0 w *
      sourceStandardRootPairedProduct hp hp1 ψ w) z
  exact (analyticAt_const.mul hzero).mul hpaired

/-- At a point off all gaps, each normalized root factor squares to
the corresponding normalized pair of periodic endpoints. -/
theorem sourceStandardRoot_factor_sq_eq_spectralPairFactor
    (hp : p ≠ ⊤) (hp1 : 1 < p) (ψ : CoeffPair p)
    (m : ℤ) (z : ℂ) (hz : z ∉ sourcePeriodicSegment hp hp1 ψ m) :
    (sourceStandardRoot hp hp1 ψ m z / singleSpectralDenominator m)^2 =
      spectralPairFactor
        (canonicalPeriodicLeft hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ))
        (canonicalPeriodicRight hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ))
        z m := by
  have hd : singleSpectralDenominator m ^ 2 = spectralPairDenominator m := by
    by_cases hm : m = 0 <;>
      simp [singleSpectralDenominator, spectralPairDenominator, hm]
  rw [div_pow, sourceStandardRoot_sq_of_not_mem_segment hp hp1 ψ m z hz,
    spectralPairFactor_eq_div, hd]

/-- Finite canonical-root cutoffs square to the finite normalized
periodic endpoint product off the gap segments. -/
theorem sourceCanonicalRootPartialProduct_sq_eq_spectralPairPartialProduct
    (hp : p ≠ ⊤) (hp1 : 1 < p) (N : ℕ)
    (ψ : CoeffPair p) (z : ℂ) (hz : z ∈ sourceCanonicalRootDomain hp hp1 ψ) :
    (sourceCanonicalRootPartialProduct hp hp1 N ψ z)^2 =
      spectralPairPartialProduct
        (canonicalPeriodicLeft hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ))
        (canonicalPeriodicRight hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ))
        z N := by
  unfold sourceCanonicalRootPartialProduct spectralPairPartialProduct
  rw [mul_pow, ← Finset.prod_pow]
  have hi : ((2 : ℂ)*I)^2 = -4 := by
    calc
      _ = 4*I^2 := by ring
      _ = -4 := by simp
  rw [hi]
  congr 1
  apply Finset.prod_congr rfl
  intro m _
  exact sourceStandardRoot_factor_sq_eq_spectralPairFactor hp hp1 ψ m z (hz m)

/-- On the complement of all canonical periodic gaps, the full standard-root
product is a square root of the actual source discriminant squared minus four. -/
theorem sourceCanonicalRoot_sq_eq_discriminant_sq_sub_four
    (hp : p ≠ ⊤) (hp1 : 1 < p) (ψ : CoeffPair p)
    (z : ℂ) (hz : z ∈ sourceCanonicalRootDomain hp hp1 ψ) :
    (sourceCanonicalRoot hp hp1 ψ z)^2 =
      (canonicalDiscriminant hp (periodOnePotential ψ) z)^2-4 := by
  let ξ := canonicalPeriodicLeft hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ)
  let η := canonicalPeriodicRight hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ)
  have hroot := (tendsto_sourceCanonicalRootPartialProduct hp hp1 ψ z).pow 2
  have hpair := (tendstoLocallyUniformlyOn_entireSpectralPairProduct hp ξ η
    (canonicalPeriodicEndpoints_spec hp hp1 (periodOnePotential ψ)
      (periodOnePotential_mem ψ)).1.left_displacement
    (canonicalPeriodicEndpoints_spec hp hp1 (periodOnePotential ψ)
      (periodOnePotential_mem ψ)).1.right_displacement).tendsto_at (mem_univ z)
  have hroot' : Tendsto (fun N => spectralPairPartialProduct ξ η z N) atTop
      (𝓝 ((sourceCanonicalRoot hp hp1 ψ z)^2)) := by
    convert hroot using 1
    funext N
    exact (sourceCanonicalRootPartialProduct_sq_eq_spectralPairPartialProduct
      hp hp1 N ψ z hz).symm
  have heq : (sourceCanonicalRoot hp hp1 ψ z)^2 =
      entireSpectralPairProduct ξ η z := tendsto_nhds_unique hroot' hpair
  calc
    _ = entireSpectralPairProduct ξ η z := heq
    _ = canonicalPeriodicProduct hp (periodOnePotential ψ) z :=
      congrFun (canonicalPeriodicEndpoints_product hp hp1 (periodOnePotential ψ)
        (periodOnePotential_mem ψ)) z
    _ = _ := canonicalPeriodic_eq_discriminant_sq_sub_four_finite hp hp1
      (periodOnePotential ψ) (periodOnePotential_mem ψ) z

end NLS.ZakharovShabat
