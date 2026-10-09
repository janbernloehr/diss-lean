import NLS.ZakharovShabat.TriangularNormalizedBand
import NLS.ZakharovShabat.SourceBoundaryPrintedHeight

/-! # A counterexample to Theorem 1.4's printed boundary height

For every natural exponent P at least 1024, a finite triangular Fourier
potential has source norm at most 3/32 and an actual Dirichlet eigenvalue at
i*2^P. This lies above the printed height (1+8*norm)^P and outside every
quarter-pi disk about a real free frequency, independently of the cutoff.
This concerns the original source norm. It makes no claim against the
periodic height of Theorem 1.1 or the verified Hilbert boundary theorem.
-/
noncomputable section
open Set Complex
open scoped ENNReal
namespace NLS.ZakharovShabat

/-- The imaginary height of the explicit eigenvalue. -/
theorem abs_im_triangular_height (P : ℕ) :
    |(((2 : ℂ)^P)*I).im| = (2 : ℝ)^P := by
  have he : (2 : ℂ)^P = Complex.ofReal ((2 : ℝ)^P) := by norm_cast
  rw [he]
  rw [mul_im,ofReal_re,ofReal_im,I_re,I_im,mul_one,mul_zero,add_zero]
  exact abs_of_nonneg (by positivity)

/-- Large exponents make the original source norm uniformly small. -/
theorem norm_triangularNormalized_source_le_three_div_thirtytwo {P : ℕ}
    [Fact (1 ≤ (P : ℝ≥0∞))] (hP : 1024 ≤ P) :
    ‖CoeffPair.ofFinsupp (p := (P : ℝ≥0∞)) (triangularNormalizedCoefficients P,0)‖ ≤
      3/32 := by
  have hP0 : 0 < P := by omega
  apply (norm_triangularNormalizedCoefficients_source_le hP0).trans
  apply (div_le_iff₀ (by exact_mod_cast hP0 : 0 < (P : ℝ))).mpr
  have hPr : (1024 : ℝ) ≤ P := by exact_mod_cast hP
  linarith

/-- The actual eigenvalue is strictly above the unchanged printed height. -/
theorem triangular_height_gt_printed {P : ℕ} [Fact (1 ≤ (P : ℝ≥0∞))]
    (hP : 1024 ≤ P) :
    (1+8*‖CoeffPair.ofFinsupp (p := (P : ℝ≥0∞))
      (triangularNormalizedCoefficients P,0)‖)^((P : ℝ≥0∞).toReal) <
      |(((2 : ℂ)^P)*I).im| := by
  rw [ENNReal.toReal_natCast,Real.rpow_natCast,abs_im_triangular_height]
  apply pow_lt_pow_left₀ _ (by positivity) (by omega : P ≠ 0)
  have h := norm_triangularNormalized_source_le_three_div_thirtytwo hP
  linarith

/-- The eigenvalue also escapes all of the high disks, at every cutoff. -/
theorem triangular_height_not_mem_highSpectralDisks {P : ℕ} (hP : 0 < P) (N : ℕ) :
    ((2 : ℂ)^P)*I ∉ highSpectralDisks N (Real.pi/4) := by
  intro hz
  obtain ⟨n,hn⟩ := Set.mem_iUnion.mp hz
  obtain ⟨_,hn⟩ := Set.mem_iUnion.mp hn
  have hd : ‖((2 : ℂ)^P)*I-(Real.pi : ℂ)*n‖ < Real.pi/4 := by
    simpa only [Metric.mem_ball,dist_eq_norm] using hn
  have him := Complex.abs_im_le_norm (((2 : ℂ)^P)*I-(Real.pi : ℂ)*n)
  have he : |(((2 : ℂ)^P)*I-(Real.pi : ℂ)*n).im| = (2 : ℝ)^P := by
    simpa using abs_im_triangular_height P
  rw [he] at him
  have htwo : (2 : ℝ) ≤ 2^P := by
    simpa using pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) hP
  linarith [Real.pi_lt_four]

/-- A concrete finite polynomial violates printed-box exhaustion at every cutoff. -/
theorem sourceBoundaryPrintedHeight_counterexample {P : ℕ}
    [Fact (1 ≤ (P : ℝ≥0∞))] (hP : 1024 ≤ P)
    (hp1 : 1 < (P : ℝ≥0∞)) (N : ℕ) :
    let φ := CoeffPair.ofFinsupp (p := (P : ℝ≥0∞)) (triangularNormalizedCoefficients P,0)
    ((2 : ℂ)^P)*I ∈ BoundaryCondition.spectrum .dirichlet (ENNReal.natCast_ne_top P)
      (periodOneBoundaryPotential (ENNReal.natCast_ne_top P) hp1 φ).val
      (periodOneBoundaryPotential (ENNReal.natCast_ne_top P) hp1 φ).property ∧
    ((2 : ℂ)^P)*I ∉ heightSpectralBox N ((1+8*‖φ‖)^((P : ℝ≥0∞).toReal)) ∪
      highSpectralDisks N (Real.pi/4) := by
  dsimp only
  refine ⟨mem_sourceDirichletSpectrum_triangularNormalized hp1, ?_⟩
  intro hz
  rcases hz with hbox | hdisks
  · exact (not_le_of_gt (triangular_height_gt_printed hP)) hbox.2
  · exact triangular_height_not_mem_highSpectralDisks (by omega) N hdisks

section Concrete
local instance triangularCounterexampleExponentFact : Fact (1 ≤ (1024 : ℝ≥0∞)) := ⟨by norm_num⟩
local instance triangularCounterexampleNatExponentFact : Fact (1 ≤ ((1024 : ℕ) : ℝ≥0∞)) := ⟨by norm_num⟩

/-- The original all-p exhaustion assertion is false already at p=1024. -/
theorem not_sourceTheorem1_4_printed_exhaustion :
    ¬ ∀ φ : CoeffPair 1024, ∃ N : ℕ,
      BoundaryCondition.spectrum .dirichlet (by norm_num)
        (periodOneBoundaryPotential (by norm_num) (by norm_num) φ).val
        (periodOneBoundaryPotential (by norm_num) (by norm_num) φ).property ⊆
      heightSpectralBox N ((1+8*‖φ‖)^((1024 : ℝ≥0∞).toReal)) ∪
        highSpectralDisks N (Real.pi/4) := by
  intro h
  obtain ⟨N,hN⟩ := h (CoeffPair.ofFinsupp (triangularNormalizedCoefficients 1024,0))
  have hc := sourceBoundaryPrintedHeight_counterexample (P := 1024) (by omega) (by norm_num) N
  exact hc.2 (hN hc.1)
end Concrete

end NLS.ZakharovShabat
