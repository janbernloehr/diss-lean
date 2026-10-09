import NLS.ZakharovShabat.SourceFiniteGapWeightedLift
import NLS.ZakharovShabat.SourceTranslationFiniteTarget

/-! # Analytic weighted lifts of real finite-gap translations

Translation preserves the exact gap tail. The local weighted reconstruction
therefore identifies its analytic finite target with the original translated
source, using only continuity of the original translation curve.
-/

noncomputable section
open Filter Topology
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- Finite spectral support gives a fixed closed-gap cutoff. -/
theorem exists_sourceFiniteGap_closedGapTail (hp : p ≠ ⊤) (hp1 : 1 < p)
    (φ : realTypeSourceLocus p) (hf : φ ∈ sourceFiniteGapLocus hp hp1) :
    ∃ K : ℕ, ∀ n : ℤ, K ≤ n.natAbs → canonicalPeriodicGap hp hp1
      (periodOnePotential φ.val) (periodOnePotential_mem φ.val) n = 0 := by
  classical
  refine ⟨hf.toFinset.sup Int.natAbs + 1, ?_⟩
  intro n hn
  by_contra hne
  have hmem := hf.mem_toFinset.mpr hne
  have hle := Finset.le_sup (f := Int.natAbs) hmem
  omega

/-- Every source translation orbit is norm continuous at finite exponent. -/
theorem continuous_sourceSpatialTranslation_orbit (hp : p ≠ ⊤) (a : CoeffPair p) :
    Continuous (fun t : ℝ => sourceSpatialTranslation t a) := by
  have hpair : Continuous (fun t : ℝ => (t,a)) := continuous_id.prodMk continuous_const
  exact (continuous_sourceSpatialTranslation (p := p) hp).comp
    (f := fun t : ℝ => (t,a)) hpair

/-- Near time zero, the actual translation curve has an analytic lift through
any weighted realization of the same real finite-gap source. -/
theorem exists_analyticAt_sourceFiniteGap_translationLift (hp : p ≠ ⊤) (hp1 : 1 < p)
    (w : SpectralWeight) (φ : CoeffPair p) (hreal : IsRealType (CoeffPair.toMax p φ))
    (hf : (⟨normalizedWeightedSource w φ, normalizedWeightedSource_realType w φ hreal⟩ :
      realTypeSourceLocus p) ∈ sourceFiniteGapLocus hp hp1) :
    ∃ ξ : ℝ → CoeffPair p, AnalyticAt ℝ ξ 0 ∧ ξ 0 = φ ∧
      ∀ᶠ t in 𝓝 (0 : ℝ), normalizedWeightedSource w (ξ t) =
        sourceSpatialTranslation t (normalizedWeightedSource w φ) := by
  let a := normalizedWeightedSource w φ
  have ha : IsRealType (CoeffPair.toMax p a) := normalizedWeightedSource_realType w φ hreal
  obtain ⟨K,hK⟩ := exists_sourceFiniteGap_closedGapTail hp hp1 ⟨a,ha⟩ hf
  obtain ⟨N,_,g,hg,hbase,hdecode⟩ :=
    exists_analyticAt_sourceFiniteGap_finiteReconstruction hp hp1 w φ hreal hf K
  have hA : AnalyticAt ℝ g (normalizedWeightedTruncateCLM w N (sourceSpatialTranslation 0 a)) := by
    simpa only [sourceSpatialTranslation_zero] using hg.restrictScalars
  refine ⟨fun t => g (normalizedWeightedTruncateCLM w N (sourceSpatialTranslation t a)),
    hA.comp (f := fun t : ℝ => normalizedWeightedTruncateCLM w N (sourceSpatialTranslation t a))
      (analyticAt_normalizedWeightedTruncate_translation w N a 0), ?_, ?_⟩
  · simpa only [sourceSpatialTranslation_zero] using hbase
  · have hcont : Continuous (fun t : ℝ => sourceSpatialTranslation t a) :=
      continuous_sourceSpatialTranslation_orbit hp a
    have he := (hcont.continuousAt (x := 0)).eventually (by
      simpa only [sourceSpatialTranslation_zero] using hdecode)
    filter_upwards [he] with t ht
    exact ht (sourceSpatialTranslation_realType t a ha)
      (sourceSpatialTranslation_closedGapTail hp hp1 t a K hK)

end NLS.ZakharovShabat
