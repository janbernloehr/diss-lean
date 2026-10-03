import NLS.ZakharovShabat.SourceOpenGapComplement
import NLS.ZakharovShabat.SourceFiniteGap

/-! # The finite-gap exterior spectral domain

The union of the finitely many noncollapsed cuts is compact. Outside a
sufficiently large disc, the actual root and nonzero Floquet multiplier
are therefore analytic, as is the filled critical-root quotient.
-/
noncomputable section
open Set Complex Metric
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- Every closed periodic segment is compact, for complex sources as well. -/
theorem isCompact_sourcePeriodicSegment (hp : p ≠ ⊤) (hp1 : 1 < p)
    (φ : CoeffPair p) (n : ℤ) : IsCompact (sourcePeriodicSegment hp hp1 φ n) := by
  rw [sourcePeriodicSegment, segment_eq_image]
  exact isCompact_Icc.image (by fun_prop)

/-- At a finite-gap source, all noncollapsed cuts form one compact set. -/
theorem isCompact_compl_sourceOpenGapComplement_finiteGap (hp : p ≠ ⊤) (hp1 : 1 < p)
    (φ : realTypeSourceLocus p) (hf : φ ∈ sourceFiniteGapLocus hp hp1) :
    IsCompact (sourceOpenGapComplement hp hp1 φ.val)ᶜ := by
  have he : (sourceOpenGapComplement hp hp1 φ.val)ᶜ =
      ⋃ n ∈ {n : ℤ | canonicalPeriodicGap hp hp1 (periodOnePotential φ.val)
        (periodOnePotential_mem φ.val) n ≠ 0}, sourcePeriodicSegment hp hp1 φ.val n := by
    ext z
    simp [sourceOpenGapComplement]
  rw [he]
  exact hf.isCompact_biUnion fun n _ => isCompact_sourcePeriodicSegment hp hp1 φ.val n

theorem isOpen_sourceOpenGapComplement_finiteGap (hp : p ≠ ⊤) (hp1 : 1 < p)
    (φ : realTypeSourceLocus p) (hf : φ ∈ sourceFiniteGapLocus hp hp1) :
    IsOpen (sourceOpenGapComplement hp hp1 φ.val) := by
  exact isClosed_compl_iff.mp
    (isCompact_compl_sourceOpenGapComplement_finiteGap hp hp1 φ hf).isClosed

/-- No noncollapsed gap reaches beyond a sufficiently large disc. -/
theorem exists_exterior_subset_sourceOpenGapComplement_finiteGap (hp : p ≠ ⊤) (hp1 : 1 < p)
    (φ : realTypeSourceLocus p) (hf : φ ∈ sourceFiniteGapLocus hp hp1) :
    ∃ R : ℝ, 0 < R ∧ {z : ℂ | R < ‖z‖} ⊆ sourceOpenGapComplement hp hp1 φ.val := by
  obtain ⟨C, hC⟩ :=
    (isCompact_compl_sourceOpenGapComplement_finiteGap hp hp1 φ hf).isBounded.exists_norm_le
  refine ⟨max C 1, lt_of_lt_of_le zero_lt_one (le_max_right _ _), ?_⟩
  intro z hz
  by_contra hn
  have h := hC z hn
  exact (not_lt_of_ge (h.trans (le_max_left _ _))) hz

/-- All three actual spectral functions are analytic on a full exterior region;
the multiplier is everywhere nonzero there, including collapsed spectral points. -/
theorem exists_sourceFiniteGap_analytic_exterior (hp : p ≠ ⊤) (hp1 : 1 < p)
    (φ : realTypeSourceLocus p) (hf : φ ∈ sourceFiniteGapLocus hp hp1) :
    ∃ R : ℝ, 0 < R ∧
      AnalyticOnNhd ℂ (sourceCanonicalRoot hp hp1 φ.val) {z : ℂ | R < ‖z‖} ∧
      AnalyticOnNhd ℂ (sourceFloquetMultiplier hp hp1 φ.val) {z : ℂ | R < ‖z‖} ∧
      (∀ z : ℂ, R < ‖z‖ → sourceFloquetMultiplier hp hp1 φ.val z ≠ 0) ∧
      AnalyticOnNhd ℂ (sourceFloquetLogDerivative hp hp1 φ.val) {z : ℂ | R < ‖z‖} := by
  obtain ⟨R, hR, hsub⟩ := exists_exterior_subset_sourceOpenGapComplement_finiteGap hp hp1 φ hf
  refine ⟨R, hR, ?_, ?_, ?_, ?_⟩
  · exact (sourceCanonicalRoot_analyticOnNhd_openGapComplement hp hp1 φ.val φ.property).mono hsub
  · exact (sourceFloquetMultiplier_analyticOnNhd_openGapComplement hp hp1 φ.val φ.property).mono hsub
  · intro z hz
    exact sourceFloquetMultiplier_ne_zero_openGapComplement hp hp1 φ.val φ.property z (hsub hz)
  · exact (sourceFloquetLogDerivative_analyticOnNhd hp hp1 φ.val φ.property).mono hsub

end NLS.ZakharovShabat
