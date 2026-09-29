import NLS.ZakharovShabat.SingleSpectralProductRatioExterior
import NLS.ZakharovShabat.SourceGapInterpolationOuterCircles
import NLS.ZakharovShabat.SourcePsiRootResolventExterior
import NLS.ComplexAnalysis.SimpleZeroInterpolation

/-!
# Exterior decay of the psi interpolation quotient

The original displaced-root product and the product formed from gap
zeros both approach the same free sine normalization. Their ratio is
therefore uniformly bounded on large separated circles. The
root-resolvent factor of the numerator variation tends uniformly to
zero there, giving the circle estimate in Lemma 12.7.
-/

noncomputable section
open Set Filter Topology Metric Complex
open scoped ENNReal
namespace NLS.ZakharovShabat

/-- The interpolation numerator is the full original root product
times the negative of the actual-root resolvent series. -/
theorem sourcePsi_interpolationNumerator_eq_neg_product_mul_resolvent
    {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (n : ℤ) (a h : Coeff p) (z : ℂ)
    (hvariation : sourcePsiCandidateVariation n a h z =
      sourcePsiCandidate n (z,a) *
        ∑' m : ℤ, h m / (displacedRoots a m - z)) :
    (displacedRoots a n - z) * sourcePsiCandidateVariation n a h z =
      -jointSingleSpectralProduct (z,a) *
        ∑' m : ℤ, h m / (displacedRoots a m - z) := by
  rw [hvariation, sourcePsiCandidate,
    jointSingleSpectralProduct_eq_deleted hp hp1 n (z,a)]
  ring

/-- At large separated spectral parameters, the quotient of the
interpolation numerator by any `ℓᵖ` single-root product is uniformly
small; that product is nonzero there. -/
theorem exists_threshold_sourcePsi_interpolationQuotient_small
    {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (ρ : ℤ → ℂ)
    (hρlp : Memℓp (fun m => ρ m - (Real.pi : ℂ) * m) p)
    (n : ℤ) (a h : Coeff p) (hdeleted : h n = 0)
    {r : ℝ} (hr : 0 < r) (hrπ : r ≤ Real.pi / 4)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ R : ℝ, ∀ z : ℂ, R ≤ ‖z‖ →
      (∀ m : ℤ, r ≤ ‖z - (Real.pi : ℂ) * m‖) →
      entireSingleSpectralProduct ρ z ≠ 0 ∧
      ‖((displacedRoots a n - z) *
          sourcePsiCandidateVariation n a h z) /
          entireSingleSpectralProduct ρ z‖ ≤ ε := by
  obtain ⟨Rratio,hRratio⟩ := exists_threshold_entireSingleSpectralProduct_ratio_le_four
    hp (displacedRoots a) ρ (memℓp_displacedRoots a) hρlp hr hrπ
  obtain ⟨Rs,hRs⟩ := exists_threshold_sourcePsiCandidateVariation_resolvent_small
    hp hp1 n a h hdeleted hr hrπ (by positivity : 0 < ε/4)
  refine ⟨max Rratio Rs,?_⟩
  intro z hz hsep
  let J : ℂ := jointSingleSpectralProduct (z,a)
  let G : ℂ := entireSingleSpectralProduct ρ z
  let S : ℂ := ∑' m : ℤ, h m / (displacedRoots a m-z)
  obtain ⟨hG,hratio⟩ := hRratio z ((le_max_left _ _).trans hz) hsep
  change ‖J/G‖ ≤ 4 at hratio
  have hsmall := hRs z ((le_max_right _ _).trans hz) hsep
  have hnum := sourcePsi_interpolationNumerator_eq_neg_product_mul_resolvent
    hp hp1 n a h z hsmall.1
  have hnorm : ‖((displacedRoots a n - z) *
      sourcePsiCandidateVariation n a h z) / G‖ =
      ‖J / G‖ * ‖S‖ := by
    rw [hnum]
    have heq : (-J * S) / G = -(J / G) * S := by
      field_simp [hG]
    rw [heq, norm_mul, norm_neg]
  refine ⟨hG,?_⟩
  change ‖((displacedRoots a n - z) *
      sourcePsiCandidateVariation n a h z) / G‖ ≤ ε
  rw [hnorm]
  have hS : ‖S‖ ≤ ε / 4 := hsmall.2
  nlinarith [norm_nonneg S]

/-- The interpolation quotient decays uniformly on the
half-integer-radius circles used in Lemma 12.7. -/
theorem eventually_centralCircle_sourcePsi_interpolationQuotient_small
    {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (ρ : ℤ → ℂ)
    (hρlp : Memℓp (fun m => ρ m - (Real.pi : ℂ) * m) p)
    (n : ℤ) (a h : Coeff p) (hdeleted : h n = 0)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ K : ℕ, ∀ k : ℕ, K ≤ k →
      ∀ z ∈ sphere (0 : ℂ) (centralCircleRadius k),
        entireSingleSpectralProduct ρ z ≠ 0 ∧
        ‖((displacedRoots a n - z) *
            sourcePsiCandidateVariation n a h z) /
            entireSingleSpectralProduct ρ z‖ ≤ ε := by
  obtain ⟨R,hR⟩ :=
    exists_threshold_sourcePsi_interpolationQuotient_small
      hp hp1 ρ hρlp n a h hdeleted
        (by positivity : 0 < Real.pi / 4) le_rfl hε
  obtain ⟨K,hK⟩ := exists_nat_gt (R / Real.pi)
  refine ⟨K,?_⟩
  intro k hk z hz
  have hK : R < (K : ℝ) * Real.pi := by
    apply (div_lt_iff₀ Real.pi_pos).mp
    exact_mod_cast hK
  have hkreal : (K : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
  have hRk : R ≤ centralCircleRadius k := by
    unfold centralCircleRadius
    nlinarith [Real.pi_pos]
  have hnorm : ‖z‖ = centralCircleRadius k := by
    simpa only [mem_sphere, dist_zero_right] using hz
  apply hR z (by rw [hnorm]; exact hRk)
  intro m
  have hsep := centralCircle_lattice_gap k hz m
  nlinarith [Real.pi_pos]

/-- The circle bound closes the interpolation argument: an entire
variation numerator sharing the simple zeros of a gap product
vanishes identically. -/
theorem sourcePsi_interpolationNumerator_eq_zero_of_simpleGapZeros
    {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (ρ : ℤ → ℂ)
    (hρlp : Memℓp (fun m => ρ m - (Real.pi : ℂ) * m) p)
    (hsimple : ∀ z : ℂ, entireSingleSpectralProduct ρ z = 0 →
      deriv (entireSingleSpectralProduct ρ) z ≠ 0)
    (n : ℤ) (a h : Coeff p) (hdeleted : h n = 0)
    (hcommon : ∀ z : ℂ, entireSingleSpectralProduct ρ z = 0 →
      (displacedRoots a n - z) * sourcePsiCandidateVariation n a h z = 0) :
    (fun z : ℂ => (displacedRoots a n - z) *
      sourcePsiCandidateVariation n a h z) = 0 := by
  have hf : AnalyticOnNhd ℂ
      (fun z : ℂ => (displacedRoots a n - z) *
        sourcePsiCandidateVariation n a h z) Set.univ :=
    (analyticOnNhd_const.sub analyticOnNhd_id).mul
      (analyticOnNhd_sourcePsiCandidateVariation hp hp1 n a h)
  have hg := analyticOnNhd_entireSingleSpectralProduct hp ρ hρlp
  obtain ⟨K,hK⟩ := eventually_centralCircle_entireSingleSpectralProduct_ne_zero
    hp ρ hρlp
  let R : ℕ → ℝ := fun j => centralCircleRadius (j + K)
  have hbase : Tendsto centralCircleRadius atTop atTop := by
    have ht : Tendsto (fun j : ℕ => (j : ℝ) * Real.pi) atTop atTop :=
      (tendsto_natCast_atTop_atTop.const_mul_atTop Real.pi_pos).congr'
        (Filter.Eventually.of_forall (fun j => by ring))
    change Tendsto (fun j : ℕ => (j : ℝ) * Real.pi + Real.pi / 2)
      atTop atTop
    exact ht.atTop_add tendsto_const_nhds
  have hR : Tendsto R atTop atTop :=
    hbase.comp (tendsto_add_atTop_nat K)
  have hcircle (j : ℕ) (z : ℂ)
      (hz : z ∈ sphere (0 : ℂ) (R j)) :
      entireSingleSpectralProduct ρ z ≠ 0 :=
    hK (j + K) (by omega) z hz
  have hdecay (ε : ℝ) (hε : 0 < ε) :
      ∀ᶠ j : ℕ in atTop,
        ∀ z ∈ sphere (0 : ℂ) (R j),
          ‖((displacedRoots a n - z) *
            sourcePsiCandidateVariation n a h z) /
            entireSingleSpectralProduct ρ z‖ ≤ ε := by
    obtain ⟨Kε,hKε⟩ :=
      eventually_centralCircle_sourcePsi_interpolationQuotient_small
        hp hp1 ρ hρlp n a h hdeleted hε
    filter_upwards [eventually_ge_atTop Kε] with j hj
    intro z hz
    exact (hKε (j + K) (by omega) z hz).2
  exact NLS.ComplexAnalysis.entire_eq_zero_of_simple_zero_interpolation
    hf hg hcommon hsimple R hR hcircle hdecay

/-- Remove the deleted-root factor by continuity. -/
theorem sourcePsiCandidateVariation_eq_zero_of_simpleGapZeros
    {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (ρ : ℤ → ℂ)
    (hρlp : Memℓp (fun m => ρ m - (Real.pi : ℂ) * m) p)
    (hsimple : ∀ z : ℂ, entireSingleSpectralProduct ρ z = 0 →
      deriv (entireSingleSpectralProduct ρ) z ≠ 0)
    (n : ℤ) (a h : Coeff p) (hdeleted : h n = 0)
    (hcommon : ∀ z : ℂ, entireSingleSpectralProduct ρ z = 0 →
      (displacedRoots a n - z) * sourcePsiCandidateVariation n a h z = 0) :
    sourcePsiCandidateVariation n a h = 0 := by
  have hnum := sourcePsi_interpolationNumerator_eq_zero_of_simpleGapZeros
    hp hp1 ρ hρlp hsimple n a h hdeleted hcommon
  have hc : Continuous (sourcePsiCandidateVariation n a h) :=
    continuousOn_univ.mp
      (analyticOnNhd_sourcePsiCandidateVariation hp hp1 n a h).continuousOn
  apply Continuous.ext_on
    ((Set.to_countable {displacedRoots a n}).dense_compl ℂ)
    hc continuous_const
  intro z hz
  have hne : displacedRoots a n - z ≠ 0 := by
    have : z ≠ displacedRoots a n := by simpa using hz
    exact sub_ne_zero.mpr this.symm
  have heq := congrFun hnum z
  exact (mul_eq_zero.mp heq).resolve_left hne

/-- The gap-zero interpolation argument proves uniqueness of a
deleted root-direction variation. -/
theorem sourcePsiCandidateVariation_zero_of_gapZeros
    {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (φ ψ : CoeffPair p) (N : ℕ) (ε : ℝ)
    (n : ℤ) (a h : Coeff p) (hdeleted : h n = 0)
    (hseg : ∀ m : ℤ,
      sourcePeriodicSegment hp hp1 ψ m ⊆
        sourceIsolatingDisc hp hp1 φ N ε m)
    (hroot : displacedRoots a n ∈
      sourceIsolatingDisc hp hp1 φ N ε n)
    (hdisjoint : ∀ i j : ℤ, i ≠ j →
      Disjoint (sourceIsolatingDisc hp hp1 φ N ε i)
        (sourceIsolatingDisc hp hp1 φ N ε j))
    (hgap : ∀ m : ℤ, m ≠ n →
      ∃ μ ∈ sourcePeriodicSegment hp hp1 ψ m,
        sourcePsiCandidateVariation n a h μ = 0) :
    sourcePsiCandidateVariation n a h = 0 := by
  obtain ⟨ρ,hρlp,_,_,_,hsimple,hcommon⟩ :=
    exists_sourcePsiCandidateVariation_simple_interpolation_product
      hp hp1 φ ψ N ε n a h hseg hroot hdisjoint hgap
  exact sourcePsiCandidateVariation_eq_zero_of_simpleGapZeros
    hp hp1 ρ hρlp hsimple n a h hdeleted hcommon

/-- With distinct original roots, the gap-zero condition kills the
deleted direction itself. -/
theorem sourcePsiCandidate_deleted_direction_zero_of_gapZeros
    {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (φ ψ : CoeffPair p) (N : ℕ) (ε : ℝ)
    (n : ℤ) (a h : Coeff p)
    (hsep : Function.Injective (displacedRoots a))
    (hdeleted : h n = 0)
    (hseg : ∀ m : ℤ,
      sourcePeriodicSegment hp hp1 ψ m ⊆
        sourceIsolatingDisc hp hp1 φ N ε m)
    (hroot : displacedRoots a n ∈
      sourceIsolatingDisc hp hp1 φ N ε n)
    (hdisjoint : ∀ i j : ℤ, i ≠ j →
      Disjoint (sourceIsolatingDisc hp hp1 φ N ε i)
        (sourceIsolatingDisc hp hp1 φ N ε j))
    (hgap : ∀ m : ℤ, m ≠ n →
      ∃ μ ∈ sourcePeriodicSegment hp hp1 ψ m,
        sourcePsiCandidateVariation n a h μ = 0) :
    h = 0 := by
  apply sourcePsiCandidateVariation_zero_imp_deleted_direction_zero
    hp hp1 n a h hsep hdeleted
  intro z
  exact congrFun (sourcePsiCandidateVariation_zero_of_gapZeros
    hp hp1 φ ψ N ε n a h hdeleted hseg hroot hdisjoint hgap) z

end NLS.ZakharovShabat
