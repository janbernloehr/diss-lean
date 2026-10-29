import NLS.ZakharovShabat.CentralParityPolynomialAnalytic
import NLS.ZakharovShabat.PeriodOneEmbedding
import NLS.ZakharovShabat.OrderedPeriodicParityPairs
import NLS.ZakharovShabat.SourceDiscriminantProductFormula

/-! Corrected finite parity determinants for the proof of Lemma 8.1.
The central circle has index 2*M. The odd cutoff retains its extra
positive boundary pair, and the two prefactors are -1 and 4.
-/
noncomputable section
set_option autoImplicit false
open Set Metric Filter Topology NLS.ComplexAnalysis
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- Both literal parity cutoffs as determinants of the original contour restrictions. -/
theorem CompletePeriodicParityPairs.section8_cutoffs_eq_contourDeterminants
    {hp : p ≠ ⊤} {w : SpectralWeight}
    {φ : WeightedCoeffPair w.toWeight p} {N : ℕ} {ξ η : ℤ → ℂ}
    (h : CompletePeriodicParityPairs hp w φ N ξ η) (M : ℕ) (hM : N ≤ 2*M)
    (hc : sphere 0 (centralCircleRadius (2*M)) ⊆ resolventSet hp (weightedBaseToPair w φ))
    (he : enclosedPeriodicSpectrum hp (weightedBaseToPair w φ) 0 (centralCircleRadius (2*M)) =
      centralPeriodicSpectrum hp (weightedBaseToPair w φ) (2*M)) (z : ℂ) :
    evenSpectralPairCutoff ξ η z M =
      -parityContourDeterminant hp (weightedBaseToPair w φ) 0 (centralCircleRadius (2*M)) 0 z /
        centralParityNormalization (2*M) 0 ∧
    oddSpectralPairCutoff ξ η z M =
      (4*parityContourDeterminant hp (weightedBaseToPair w φ) 0 (centralCircleRadius (2*M)) 1 z /
        centralParityNormalization (2*M) 1) * spectralPairFactor ξ η z (2*(M : ℤ)+1) := by
  constructor
  · rw [h.evenCutoff_eq_central M hM z,
      centralParityPolynomial_eq_contourDeterminant hp _ h.even_potential (2*M) 0 hc he z]
  · rw [h.oddCutoff_eq_central M hM z,
      centralParityPolynomial_eq_contourDeterminant hp _ h.even_potential (2*M) 1 hc he z]

/-- One original source neighborhood supplies the contour hypotheses for every larger cutoff. -/
theorem exists_source_section8_cutoff_determinants (hp : p ≠ ⊤) (φ : CoeffPair p) :
    ∃ K : ℕ, 0 < K ∧ ∃ U : Set (CoeffPair p),
      IsOpen U ∧ Convex ℝ U ∧ φ ∈ U ∧ 0 ∈ U ∧
      ∀ ψ ∈ U, ∀ M : ℕ, K ≤ M → ∀ N : ℕ, N ≤ 2*M → ∀ ξ η : ℤ → ℂ,
      CompletePeriodicParityPairs hp SpectralWeight.one
        (unitBaseEquiv.symm (periodOnePotential ψ)) N ξ η → ∀ z : ℂ,
        evenSpectralPairCutoff ξ η z M =
          -parityContourDeterminant hp (periodOnePotential ψ) 0 (centralCircleRadius (2*M)) 0 z /
            centralParityNormalization (2*M) 0 ∧
        oddSpectralPairCutoff ξ η z M =
          (4*parityContourDeterminant hp (periodOnePotential ψ) 0 (centralCircleRadius (2*M)) 1 z /
            centralParityNormalization (2*M) 1) * spectralPairFactor ξ η z (2*(M : ℤ)+1) := by
  obtain ⟨K,V,hK,ho,hconv,hφ,h0,hV⟩ := exists_uniform_centralCircle hp (periodOnePotential φ)
  refine ⟨K,hK,periodOnePotential ⁻¹' V,ho.preimage (periodOnePotential (p := p)).continuous,
    hconv.linear_preimage ((periodOnePotential (p := p)).restrictScalars ℝ).toLinearMap,hφ,?_,?_⟩
  · simpa only [mem_preimage,map_zero] using h0
  · intro ψ hψ M hM N hN ξ η h z
    have hbase : weightedBaseToPair SpectralWeight.one
        (unitBaseEquiv.symm (periodOnePotential ψ)) = periodOnePotential ψ := by
      rw [← unitBaseEquiv_eq]
      exact unitBaseEquiv.apply_symm_apply _
    have hcircle := hV (periodOnePotential ψ) hψ (2*M) (by omega)
    have hh := h.section8_cutoffs_eq_contourDeterminants M hN
      (by simpa only [hbase] using hcircle.2.1)
      (by simpa only [hbase] using hcircle.2.2.1) z
    simpa only [hbase] using hh

/-- Counted source roots give both whole-plane limits, independently of their labeling. -/
theorem CompletePeriodicParityPairs.source_section8_limits
    {hp : p ≠ ⊤} (hp1 : 1 < p) {φ : CoeffPair p} {N : ℕ} {ξ η : ℤ → ℂ}
    (H : CompletePeriodicParityPairs hp SpectralWeight.one
      (unitBaseEquiv.symm (periodOnePotential φ)) N ξ η) :
    TendstoLocallyUniformlyOn (fun M z => evenSpectralPairCutoff ξ η z M)
      (fun z => canonicalDiscriminant hp (periodOnePotential φ) z-2) atTop univ ∧
    TendstoLocallyUniformlyOn (fun M z => oddSpectralPairCutoff ξ η z M)
      (fun z => canonicalDiscriminant hp (periodOnePotential φ) z+2) atTop univ := by
  have hbase : weightedBaseToPair SpectralWeight.one
      (unitBaseEquiv.symm (periodOnePotential φ)) = periodOnePotential φ := by
    rw [← unitBaseEquiv_eq]
    exact unitBaseEquiv.apply_symm_apply _
  have hh := H.canonicalParity_eq_products hp1
  rw [hbase] at hh
  have hf : evenSpectralPairProduct ξ η = fun z =>
      canonicalDiscriminant hp (periodOnePotential φ) z-2 :=
    hh.1.symm.trans (funext (canonicalEven_eq_discriminant_sub_two hp _))
  have hg : oddSpectralPairProduct ξ η = fun z =>
      canonicalDiscriminant hp (periodOnePotential φ) z+2 :=
    hh.2.symm.trans (funext (canonicalOdd_eq_discriminant_add_two_finite hp hp1 _
      (periodOnePotential_mem φ)))
  constructor
  · rw [← hf]
    exact tendstoLocallyUniformlyOn_evenSpectralPairProduct hp ξ η H.left_displacement H.right_displacement
  · rw [← hg]
    exact tendstoLocallyUniformlyOn_oddSpectralPairProduct hp ξ η H.left_displacement H.right_displacement

/-- Separate parity ordering preserves the common weighted neighborhood and every large cutoff. -/
theorem exists_uniform_section8_ordered_pairs
    (hp : p ≠ ⊤) (hp1 : 1 < p) (w : SpectralWeight) (φ : WeightedCoeffPair w.toWeight p) :
    ∃ K : ℕ, ∃ U : Set (WeightedCoeffPair w.toWeight p),
      IsOpen U ∧ Convex ℝ U ∧ φ ∈ U ∧ 0 ∈ U ∧
      ∀ ψ ∈ U, weightedBaseToPair w ψ ∈ pairParitySubspace 0 →
      ∀ N : ℕ, K ≤ N → ∃ ξ η : ℤ → ℂ,
        CompletePeriodicParityPairs hp w ψ N ξ η ∧
        (∀ n, complexLexLE (ξ n) (η n)) ∧
        ∀ i j : ℤ, i < j → i % 2 = j % 2 → complexLexLE (η i) (ξ j) := by
  obtain ⟨K,_,U,ho,hc,hφ,h0,hU⟩ := exists_uniform_completePeriodicParityPairs hp hp1 w φ
  refine ⟨K,U,ho,hc,hφ,h0,?_⟩
  intro ψ hψ he N hN
  obtain ⟨a,b,D⟩ := hU ψ hψ he N hN
  obtain ⟨ξ,η,H,hw,ho,_⟩ := D.exists_parity_ordered
  exact ⟨ξ,η,H,hw,ho⟩

/-- The source embedding into the unit-weight realization used by the counted parity data. -/
def section8SourceEmbedding : CoeffPair p →L[ℂ] WeightedCoeffPair SpectralWeight.one.toWeight p :=
  unitBaseEquiv.symm.toContinuousLinearMap.comp periodOnePotential

/-- The embedding has the original period-one potential as its underlying pair. -/
theorem section8SourceEmbedding_base (φ : CoeffPair p) :
    weightedBaseToPair SpectralWeight.one (section8SourceEmbedding φ) = periodOnePotential φ := by
  rw [← unitBaseEquiv_eq]
  exact unitBaseEquiv.apply_symm_apply _

/-- The unit-weight source embedding retains even Fourier support. -/
theorem section8SourceEmbedding_even (φ : CoeffPair p) :
    weightedBaseToPair SpectralWeight.one (section8SourceEmbedding φ) ∈ pairParitySubspace 0 := by
  rw [section8SourceEmbedding_base]
  exact periodOnePotential_mem φ

private theorem uniform_property_pullback
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (L : E →L[ℝ] F) (φ : E) (P : ℕ → F → Prop)
    (h : ∃ K : ℕ, ∃ V : Set F,
      IsOpen V ∧ Convex ℝ V ∧ L φ ∈ V ∧ 0 ∈ V ∧ ∀ ψ ∈ V, P K ψ) :
    ∃ K : ℕ, ∃ U : Set E,
      IsOpen U ∧ Convex ℝ U ∧ φ ∈ U ∧ 0 ∈ U ∧ ∀ ψ ∈ U, P K (L ψ) := by
  obtain ⟨K,V,ho,hc,hφ,h0,hV⟩ := h
  exact ⟨K,L ⁻¹' V,ho.preimage L.continuous,hc.linear_preimage L.toLinearMap,hφ,
    by simpa only [mem_preimage,map_zero] using h0,fun ψ hψ => hV (L ψ) hψ⟩

/-- Ordered source parity lists exist on one neighborhood at every sufficiently large cutoff. -/
theorem exists_uniform_source_section8_ordered_pairs
    (hp : p ≠ ⊤) (hp1 : 1 < p) (φ : CoeffPair p) :
    ∃ K : ℕ, ∃ U : Set (CoeffPair p),
      IsOpen U ∧ Convex ℝ U ∧ φ ∈ U ∧ 0 ∈ U ∧
      ∀ ψ ∈ U, ∀ N : ℕ, K ≤ N → ∃ ξ η : ℤ → ℂ,
        CompletePeriodicParityPairs hp SpectralWeight.one
          (unitBaseEquiv.symm (periodOnePotential ψ)) N ξ η ∧
        (∀ n, complexLexLE (ξ n) (η n)) ∧
        ∀ i j : ℤ, i < j → i % 2 = j % 2 → complexLexLE (η i) (ξ j) := by
  let L := (section8SourceEmbedding (p := p)).restrictScalars ℝ
  have h := uniform_property_pullback L φ
    (fun K ψ => weightedBaseToPair SpectralWeight.one ψ ∈ pairParitySubspace 0 →
      ∀ N : ℕ, K ≤ N → ∃ ξ η : ℤ → ℂ,
        CompletePeriodicParityPairs hp SpectralWeight.one ψ N ξ η ∧
        (∀ n, complexLexLE (ξ n) (η n)) ∧
        ∀ i j : ℤ, i < j → i % 2 = j % 2 → complexLexLE (η i) (ξ j))
    (exists_uniform_section8_ordered_pairs hp hp1 SpectralWeight.one (L φ))
  obtain ⟨K,U,ho,hc,hφ,h0,hU⟩ := h
  exact ⟨K,U,ho,hc,hφ,h0,fun ψ hψ N hN =>
    hU ψ hψ (section8SourceEmbedding_even ψ) N hN⟩

/-- One source neighborhood admits independently ordered parity roots, a common cutoff,
and both corrected determinant formulas, with locally uniform whole-plane limits. -/
theorem exists_source_section8_ordered_determinant_products
    (hp : p ≠ ⊤) (hp1 : 1 < p) (φ : CoeffPair p) :
    ∃ K : ℕ, 0 < K ∧ ∃ U : Set (CoeffPair p),
      IsOpen U ∧ Convex ℝ U ∧ φ ∈ U ∧ 0 ∈ U ∧
      ∀ ψ ∈ U, ∃ ξ η : ℤ → ℂ,
        CompletePeriodicParityPairs hp SpectralWeight.one
          (unitBaseEquiv.symm (periodOnePotential ψ)) (2*K) ξ η ∧
        (∀ n, complexLexLE (ξ n) (η n)) ∧
        (∀ i j : ℤ, i < j → i % 2 = j % 2 → complexLexLE (η i) (ξ j)) ∧
        TendstoLocallyUniformlyOn (fun M z => evenSpectralPairCutoff ξ η z M)
          (fun z => canonicalDiscriminant hp (periodOnePotential ψ) z-2) atTop univ ∧
        TendstoLocallyUniformlyOn (fun M z => oddSpectralPairCutoff ξ η z M)
          (fun z => canonicalDiscriminant hp (periodOnePotential ψ) z+2) atTop univ ∧
        ∀ M : ℕ, K ≤ M → ∀ z : ℂ,
          evenSpectralPairCutoff ξ η z M =
            -parityContourDeterminant hp (periodOnePotential ψ) 0 (centralCircleRadius (2*M)) 0 z /
              centralParityNormalization (2*M) 0 ∧
          oddSpectralPairCutoff ξ η z M =
            (4*parityContourDeterminant hp (periodOnePotential ψ) 0 (centralCircleRadius (2*M)) 1 z /
              centralParityNormalization (2*M) 1) * spectralPairFactor ξ η z (2*(M : ℤ)+1) := by
  obtain ⟨Kc,hKc,V,hoV,hcV,hφV,h0V,hV⟩ := exists_source_section8_cutoff_determinants hp φ
  obtain ⟨Kr,W,hoW,hcW,hφW,h0W,hW⟩ := exists_uniform_source_section8_ordered_pairs hp hp1 φ
  let K := max Kc Kr
  refine ⟨K,lt_of_lt_of_le hKc (le_max_left _ _),V ∩ W,
    hoV.inter hoW,hcV.inter hcW,⟨hφV,hφW⟩,⟨h0V,h0W⟩,?_⟩
  intro ψ hψ
  obtain ⟨ξ,η,H,hw,ho⟩ := hW ψ hψ.2 (2*K) (by dsimp [K]; omega)
  have ht := H.source_section8_limits hp1
  refine ⟨ξ,η,H,hw,ho,ht.1,ht.2,?_⟩
  intro M hM z
  exact hV ψ hψ.1 M (le_trans (le_max_left _ _) hM) (2*K) (by omega) ξ η H z

end NLS.ZakharovShabat
