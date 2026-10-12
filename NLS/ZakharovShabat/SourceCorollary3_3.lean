import NLS.ZakharovShabat.SourceResolvent
import NLS.ZakharovShabat.HeightResolvent

/-! # Corollary 3.3 in the original source norms

The printed sufficient region remains valid despite the failure of the
original-norm p-to-one estimate in Lemma 3.2(ii). Its proof uses the valid
maximum-product Neumann estimate and the contractive potential conversion.
-/
noncomputable section
open Set Filter Topology
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The original norm-dependent sufficient region, with finite denominators. -/
def sourceHeightNeumannRegion (φ : CoeffPair p) : Set ℂ :=
  {z | z.im ≠ 0 ∧ (4*p.toReal/|z.im|^(1/p.toReal)+1/|z.im|)*‖φ‖ < 1}

/-- The source condition implies the valid maximum-product Neumann condition. -/
theorem sourceHeightNeumannRegion_subset_heightNeumannRegion (φ : CoeffPair p) :
    sourceHeightNeumannRegion φ ⊆ heightNeumannRegion (CoeffPair.toMax p φ) := by
  intro z hz
  refine ⟨hz.1, ?_⟩
  exact (mul_le_mul_of_nonneg_left (CoeffPair.norm_toMax_le φ) (by positivity)).trans_lt hz.2

/-- The printed source region lies in the complete original-norm resolvent set. -/
theorem sourceHeightNeumannRegion_subset_resolventSet (hp : p ≠ ⊤) (φ : CoeffPair p) :
    sourceHeightNeumannRegion φ ⊆ sourceResolventSet hp φ := by
  rw [sourceResolventSet_eq]
  exact (sourceHeightNeumannRegion_subset_heightNeumannRegion φ).trans
    (heightNeumannRegion_subset_resolventSet hp _)

omit [Fact (1 ≤ p)] in
/-- The finite-denominator numerical region is open. -/
theorem isOpen_sourceHeightNeumannRegion (φ : CoeffPair p) : IsOpen (sourceHeightNeumannRegion φ) := by
  apply isOpen_iff_mem_nhds.mpr
  intro z hz
  have hi : 0 < |z.im| := abs_pos.mpr hz.1
  have hc : ContinuousAt (fun w : ℂ => (4*p.toReal/|w.im|^(1/p.toReal)+1/|w.im|)*‖φ‖) z := by
    fun_prop (disch := positivity)
  have hn : {w : ℂ | w.im ≠ 0} ∈ nhds z :=
    (isOpen_ne.preimage Complex.continuous_im).mem_nhds hz.1
  exact Filter.inter_mem hn (hc.tendsto.eventually (gt_mem_nhds hz.2))

/-- A source-norm height condition controls both half-planes above that height. -/
theorem mem_sourceHeightNeumannRegion_of_height_le (hp : p ≠ ⊤) (φ : CoeffPair p)
    {H : ℝ} (hH : 0 < H)
    (hφ : (4 * p.toReal / H ^ (1 / p.toReal) + 1 / H) * ‖φ‖ < 1)
    {z : ℂ} (hz : H ≤ |z.im|) : z ∈ sourceHeightNeumannRegion φ := by
  have hpos : 0 < p.toReal := ENNReal.toReal_pos
    (ne_of_gt (zero_lt_one.trans_le (show 1 ≤ p from Fact.out))) hp
  refine ⟨abs_pos.mp (hH.trans_le hz), ?_⟩
  apply lt_of_le_of_lt _ hφ
  gcongr

/-- One height works for an entire ball measured in the original source norm. -/
theorem exists_uniform_sourceHeightNeumannRegion (hp : p ≠ ⊤) (M : ℝ) :
    ∃ H : ℝ, 0 < H ∧ ∀ φ : CoeffPair p, ‖φ‖ ≤ M →
      ∀ z : ℂ, H ≤ |z.im| → z ∈ sourceHeightNeumannRegion φ := by
  have ht : Tendsto (fun H : ℝ =>
      (4 * p.toReal / H ^ (1 / p.toReal) + 1 / H) * M) atTop (𝓝 0) := by
    simpa only [zero_mul] using (tendsto_freeL1_heightBound_zero hp).mul_const M
  obtain ⟨H, hH, hsmall⟩ := ((eventually_gt_atTop (0 : ℝ)).and
    (ht.eventually_lt_const zero_lt_one)).exists
  refine ⟨H, hH, fun φ hφ z hz => mem_sourceHeightNeumannRegion_of_height_le hp φ hH ?_ hz⟩
  exact (mul_le_mul_of_nonneg_left hφ (by positivity)).trans_lt hsmall

/-- The explicit numerical region is nonempty for every finite-exponent source. -/
theorem sourceHeightNeumannRegion_nonempty (hp : p ≠ ⊤) (φ : CoeffPair p) :
    (sourceHeightNeumannRegion φ).Nonempty := by
  obtain ⟨H, hH, h⟩ := exists_uniform_sourceHeightNeumannRegion hp ‖φ‖
  refine ⟨(H : ℂ) * Complex.I, h φ le_rfl _ ?_⟩
  simp [abs_of_pos hH]

/-- Corollary 3.3: compact analytic resolvent on the printed source-norm region,
with both inverse identities in the original one-derivative domain and discrete spectrum. -/
theorem sourceCorollary3_3 (hp : p ≠ ⊤) (φ : CoeffPair p) :
    IsOpen (sourceHeightNeumannRegion φ) ∧ (sourceHeightNeumannRegion φ).Nonempty ∧
    AnalyticOnNhd ℂ (sourceResolvent hp φ) (sourceHeightNeumannRegion φ) ∧
    (∀ z ∈ sourceHeightNeumannRegion φ,
      z ∈ sourceResolventSet hp φ ∧ IsCompactOperator (sourceResolvent hp φ z) ∧
      (∀ a : CoeffPair p, sourceSpectralPencil hp φ z (sourceResolventToDomain hp φ z a) = a) ∧
      (∀ a : WeightedCoeffPair (Weight.sobolev 1) p,
        sourceResolventToDomain hp φ z (sourceSpectralPencil hp φ z a) = a)) ∧
    DiscreteTopology ↥((sourceResolventSet hp φ)ᶜ) := by
  refine ⟨isOpen_sourceHeightNeumannRegion φ, sourceHeightNeumannRegion_nonempty hp φ,
    (analyticOnNhd_sourceResolvent hp φ).mono (sourceHeightNeumannRegion_subset_resolventSet hp φ),
    ?_, discreteTopology_sourceResolventSet_compl hp φ⟩
  intro z hz
  have hmem := sourceHeightNeumannRegion_subset_resolventSet hp φ hz
  exact ⟨hmem,isCompactOperator_sourceResolvent hp φ z,
    sourceSpectralPencil_sourceResolventToDomain hp φ z hmem,
    sourceResolventToDomain_sourceSpectralPencil hp φ z hmem⟩

end NLS.ZakharovShabat
