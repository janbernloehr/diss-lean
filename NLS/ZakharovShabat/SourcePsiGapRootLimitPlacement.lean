import NLS.ZakharovShabat.SourcePsiGapRootSubsequence
import NLS.ZakharovShabat.PeriodOneBoundaryInterlacing

/-!
# Gap placement survives strong limits

For a real-type limiting potential, canonical periodic endpoints vary
continuously. A root trapped between moving endpoints remains in the
limiting segment. Together with compactness this yields a subsequence
whose strong limit remains a gap-contained deleted-root vector.
-/

noncomputable section
open Set Filter Topology Complex
open scoped ENNReal
namespace NLS.ZakharovShabat

private theorem mem_segment_of_tendsto
    (u v w : ℕ → ℂ) (u₀ v₀ w₀ : ℂ)
    (hu : Tendsto u atTop (𝓝 u₀))
    (hv : Tendsto v atTop (𝓝 v₀))
    (hw : Tendsto w atTop (𝓝 w₀))
    (hmem : ∀ k, w k ∈ segment ℝ (u k) (v k)) :
    w₀ ∈ segment ℝ u₀ v₀ := by
  classical
  have hrep : ∀ k, ∃ t : ℝ, t ∈ Icc 0 1 ∧
      w k = (1-t) • u k + t • v k := by
    intro k
    have hk := hmem k
    rw [segment_eq_image] at hk
    obtain ⟨t,ht,he⟩ := hk
    exact ⟨t,ht,he.symm⟩
  choose t ht heq using hrep
  obtain ⟨t₀,ht₀,σ,hσ,htend⟩ :=
    (isCompact_Icc : IsCompact (Icc (0 : ℝ) 1)).tendsto_subseq (x := t) ht
  have hσt : Tendsto σ atTop atTop := hσ.tendsto_atTop
  have hformula : Tendsto
      (fun k => (1-t (σ k)) • u (σ k) + t (σ k) • v (σ k))
      atTop (𝓝 ((1-t₀) • u₀ + t₀ • v₀)) :=
    ((tendsto_const_nhds.sub htend).smul (hu.comp hσt)).add
      (htend.smul (hv.comp hσt))
  have hw' : Tendsto (w ∘ σ) atTop (𝓝 w₀) := hw.comp hσt
  have hformula_eq :
      (fun k => (1-t (σ k)) • u (σ k) + t (σ k) • v (σ k)) =
        w ∘ σ := by
    funext k
    exact (heq (σ k)).symm
  rw [hformula_eq] at hformula
  have hlimit : w₀ = (1-t₀) • u₀ + t₀ • v₀ :=
    tendsto_nhds_unique hw' hformula
  rw [segment_eq_image]
  exact ⟨t₀,ht₀,hlimit.symm⟩

/-- Strongly converging deleted roots that stay in the moving periodic
segments have a limit in the segments of a real-type source. -/
theorem deletedGapRoots_mem_segments_of_tendsto
    {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (φ : CoeffPair p) (hφ : IsRealType (CoeffPair.toMax p φ))
    (ψ : ℕ → CoeffPair p) (hψ : Tendsto ψ atTop (𝓝 φ))
    (n : ℤ) (a : ℕ → DeletedCoeff p n) (b : DeletedCoeff p n)
    (ha : Tendsto a atTop (𝓝 b))
    (hgap : ∀ k : ℕ, ∀ m : ℤ, m ≠ n →
      displacedRoots (a k : Coeff p) m ∈
        sourcePeriodicSegment hp hp1 (ψ k) m) :
    ∀ m : ℤ, m ≠ n →
      displacedRoots (b : Coeff p) m ∈
        sourcePeriodicSegment hp hp1 φ m := by
  intro m hmn
  let L (χ : CoeffPair p) :=
    canonicalPeriodicLeft hp hp1 (periodOnePotential χ) (periodOnePotential_mem χ) m
  let R (χ : CoeffPair p) :=
    canonicalPeriodicRight hp hp1 (periodOnePotential χ) (periodOnePotential_mem χ) m
  have hL : Tendsto (L ∘ ψ) atTop (𝓝 (L φ)) :=
    (continuousAt_canonicalPeriodicLeft_periodOne_of_realType hp hp1 φ hφ m).tendsto.comp hψ
  have hR : Tendsto (R ∘ ψ) atTop (𝓝 (R φ)) :=
    (continuousAt_canonicalPeriodicRight_periodOne_of_realType hp hp1 φ hφ m).tendsto.comp hψ
  have hEval : Continuous (fun c : Coeff p => c m) :=
    (lp.evalCLM ℂ (fun _ : ℤ => ℂ) p m).continuous
  have hroot : Continuous (fun c : DeletedCoeff p n =>
      displacedRoots (c : Coeff p) m) := by
    change Continuous (fun c : DeletedCoeff p n =>
      (Real.pi : ℂ) * m + (c : Coeff p) m)
    exact (continuous_const : Continuous (fun _ : DeletedCoeff p n =>
      (Real.pi : ℂ) * m)).add (hEval.comp continuous_subtype_val)
  have hw : Tendsto (fun k => displacedRoots (a k : Coeff p) m)
      atTop (𝓝 (displacedRoots (b : Coeff p) m)) :=
    hroot.continuousAt.tendsto.comp ha
  change displacedRoots (b : Coeff p) m ∈ segment ℝ (L φ) (R φ)
  apply mem_segment_of_tendsto (L ∘ ψ) (R ∘ ψ)
    (fun k => displacedRoots (a k : Coeff p) m) (L φ) (R φ)
    (displacedRoots (b : Coeff p) m) hL hR hw
  intro k
  exact hgap k m hmn

/-- Converging source potentials have a strongly convergent
subsequence of gap-contained deleted roots whose limit remains in
the periodic gaps at the real-type limiting source. -/
theorem exists_tendsto_subseq_deletedGapRoots_mem_limit_segments
    {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (φ : CoeffPair p) (hφ : IsRealType (CoeffPair.toMax p φ))
    (ψ : ℕ → CoeffPair p) (hψ : Tendsto ψ atTop (𝓝 φ))
    (n : ℤ) (a : ℕ → DeletedCoeff p n)
    (hgap : ∀ k : ℕ, ∀ m : ℤ, m ≠ n →
      displacedRoots (a k : Coeff p) m ∈
        sourcePeriodicSegment hp hp1 (ψ k) m) :
    ∃ b : DeletedCoeff p n, ∃ σ : ℕ → ℕ,
      StrictMono σ ∧ Tendsto (a ∘ σ) atTop (𝓝 b) ∧
      ∀ m : ℤ, m ≠ n →
        displacedRoots (b : Coeff p) m ∈
          sourcePeriodicSegment hp hp1 φ m := by
  obtain ⟨b,σ,hσ,hb⟩ :=
    exists_tendsto_subseq_deletedGapRoots_of_source_tendsto
      hp hp1 φ ψ hψ n a hgap
  refine ⟨b,σ,hσ,hb,?_⟩
  exact deletedGapRoots_mem_segments_of_tendsto hp hp1 φ hφ
    (ψ ∘ σ) (hψ.comp hσ.tendsto_atTop) n (a ∘ σ) b hb
    (fun k m hmn => hgap (σ k) m hmn)

end NLS.ZakharovShabat
