import NLS.ZakharovShabat.SourceAuxiliaryPotentialPhase
import NLS.ZakharovShabat.SourceBoundaryHeightCounterexample

/-!
# Counterexample to Proposition 5.2's unrestricted printed height

For every natural P≥1024, inverse phase rotation of the finite triangular
input preserves its original norm and gives an actual auxiliary D* eigenvalue
i·2^P. It lies outside both the printed-height central box and every high
quarter-pi disk, independently of the cutoff. No replacement bound is adopted;
the separately proved p=2 theorem and height-N localization remain valid.
-/

noncomputable section
open scoped ENNReal
namespace NLS.ZakharovShabat
open BoundaryCondition NLS.Fourier
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The explicit auxiliary counterexample remains small in the literal original norm. -/
theorem norm_sourceAuxiliaryHeightCounterexample_le {P : ℕ} [Fact (1 ≤ (P : ℝ≥0∞))]
    (hP : 1024 ≤ P) :
    ‖(sourceAuxiliaryPotentialPhase (ENNReal.natCast_ne_top P)).symm
      (CoeffPair.ofFinsupp (p := (P : ℝ≥0∞)) (triangularNormalizedCoefficients P,0))‖ ≤ 3/32 := by
  rw [LinearIsometryEquiv.norm_map]
  exact norm_triangularNormalized_source_le_three_div_thirtytwo hP

/-- A norm-preserving rotation of a finite triangular input violates every printed cutoff box. -/
theorem sourceAuxiliaryPrintedHeight_counterexample {P : ℕ}
    [Fact (1 ≤ (P : ℝ≥0∞))] (hP : 1024 ≤ P) (hp1 : 1 < (P : ℝ≥0∞)) (N : ℕ) :
    let φ := (sourceAuxiliaryPotentialPhase (ENNReal.natCast_ne_top P)).symm
      (CoeffPair.ofFinsupp (p := (P : ℝ≥0∞)) (triangularNormalizedCoefficients P,0))
    ((2 : ℂ)^P)*Complex.I ∈ sourceAuxiliarySpectrum .dirichlet (ENNReal.natCast_ne_top P)
      (sourceAuxiliaryReflectedPotential hp1 (ENNReal.natCast_ne_top P) φ)
      (sourceAuxiliaryReflectedPotential_mem hp1 (ENNReal.natCast_ne_top P) φ) ∧
    ((2 : ℂ)^P)*Complex.I ∉ heightSpectralBox N ((1+8*‖φ‖)^((P : ℝ≥0∞).toReal)) ∪
      highSpectralDisks N (Real.pi/4) := by
  dsimp only
  rw [sourceAuxiliarySpectrum_eq_sourcePhaseBoundary, LinearIsometryEquiv.apply_symm_apply,
    LinearIsometryEquiv.norm_map]
  exact sourceBoundaryPrintedHeight_counterexample hP hp1 N

section Concrete
local instance auxiliaryHeightCounterexampleExponentFact : Fact (1 ≤ (1024 : ℝ≥0∞)) := ⟨by norm_num⟩
local instance auxiliaryHeightCounterexampleNatExponentFact : Fact (1 ≤ ((1024 : ℕ) : ℝ≥0∞)) := ⟨by norm_num⟩

/-- The all-input printed exhaustion claim fails already at p=1024. -/
theorem not_sourceProposition5_2_printed_exhaustion :
    ¬ ∀ φ : CoeffPair 1024, ∃ N : ℕ,
      sourceAuxiliarySpectrum .dirichlet (by norm_num)
        (sourceAuxiliaryReflectedPotential (by norm_num) (by norm_num) φ)
        (sourceAuxiliaryReflectedPotential_mem (by norm_num) (by norm_num) φ) ⊆
      heightSpectralBox N ((1+8*‖φ‖)^((1024 : ℝ≥0∞).toReal)) ∪ highSpectralDisks N (Real.pi/4) := by
  intro h
  obtain ⟨N,hN⟩ := h ((sourceAuxiliaryPotentialPhase (by norm_num)).symm
    (CoeffPair.ofFinsupp (triangularNormalizedCoefficients 1024,0)))
  have hc := sourceAuxiliaryPrintedHeight_counterexample (P := 1024) (by omega) (by norm_num) N
  exact hc.2 (hN hc.1)
end Concrete
end NLS.ZakharovShabat
