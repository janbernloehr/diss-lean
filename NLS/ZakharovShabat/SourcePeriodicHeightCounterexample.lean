import NLS.ZakharovShabat.DyadicNormalizationBound

/-! # A counterexample to the all-exponent printed periodic height

Ordered continuous dyadic profiles, followed by exact monodromy normalization
and diagonal balancing, give original sources of norm at most 1/16 with an
actual periodic spectral point at i*2^P for every integer P >= 100000000.
The point escapes the printed box and every quarter-pi disk. No corrected
height is adopted here, and the verified p <= 4 result remains valid.
-/
noncomputable section
open Set Complex NLS.Fourier
open scoped ENNReal
namespace NLS.ZakharovShabat

/-- A balanced actual source with a quantitative norm tending to zero. -/
theorem exists_balanced_dyadicSource_norm_le (P : ℕ)
    [Fact (1 ≤ (P : ℝ≥0∞))] (hP : 3 ≤ P) :
    ∃ ψ : CoeffPair (P : ℝ≥0∞), ‖ψ.fst‖ = ‖ψ.snd‖ ∧
      I*(2^P : ℝ) ∈ periodicSpectrum (ENNReal.natCast_ne_top P) (periodOnePotential ψ) ∧
      ‖ψ‖ ≤ 2*Real.sqrt (69120/(P-2 : ℕ)) := by
  have h2p : (2 : ℝ≥0∞) ≤ P := by exact_mod_cast (show 2 ≤ P by omega)
  obtain ⟨ψ,hbal,hspec,hnorm⟩ := exists_balanced_orderedDyadicSource
    (ENNReal.natCast_ne_top P) h2p P hP
  refine ⟨ψ,hbal,hspec,?_⟩
  rw [hnorm,ENNReal.toReal_natCast]
  have hP1 : (1 : ℝ) ≤ P := by exact_mod_cast (show 1 ≤ P by omega)
  have hfactor : (2 : ℝ)^(1/(P : ℝ)) ≤ 2 := by
    calc
      _ ≤ (2 : ℝ)^(1 : ℝ) := Real.rpow_le_rpow_of_exponent_le (by norm_num)
        ((div_le_one (by linarith : (0 : ℝ) < P)).mpr hP1)
      _ = 2 := Real.rpow_one _
  apply mul_le_mul hfactor _ (Real.sqrt_nonneg _) (by norm_num)
  apply Real.sqrt_le_sqrt
  calc
    _ ≤ ((12 : ℝ)/(P-2 : ℕ))*640*9 := by
      apply mul_le_mul
        (mul_le_mul (norm_orderedDyadicNormalization_le P hP)
          (norm_dyadicTentSumCoefficients_twice_exponent_le P hP)
          (norm_nonneg _) (by positivity))
        (norm_lowerDyadicTentCoefficients_twice_exponent_le P hP)
        (norm_nonneg _) (by positivity)
    _ = _ := by ring

/-- A deliberately generous explicit threshold avoids any numerical approximation. -/
theorem exists_small_dyadicSource (P : ℕ)
    [Fact (1 ≤ (P : ℝ≥0∞))] (hP : 100000000 ≤ P) :
    ∃ ψ : CoeffPair (P : ℝ≥0∞), ‖ψ.fst‖ = ‖ψ.snd‖ ∧
      I*(2^P : ℝ) ∈ periodicSpectrum (ENNReal.natCast_ne_top P) (periodOnePotential ψ) ∧
      ‖ψ‖ ≤ 1/16 := by
  obtain ⟨ψ,hbal,hspec,hnorm⟩ := exists_balanced_dyadicSource_norm_le P (by omega)
  refine ⟨ψ,hbal,hspec,hnorm.trans ?_⟩
  have hD : (99999998 : ℝ) ≤ (P-2 : ℕ) := by exact_mod_cast (show 99999998 ≤ P-2 by omega)
  have hsqrt : Real.sqrt (69120/(P-2 : ℕ)) ≤ 1/32 := by
    apply (Real.sqrt_le_iff).mpr
    refine ⟨by norm_num,?_⟩
    apply (div_le_iff₀ (by linarith : (0 : ℝ) < (P-2 : ℕ))).mpr
    nlinarith
  linarith

/-- This imaginary point lies outside every high-frequency disk, regardless of the cutoff. -/
theorem dyadic_height_not_mem_highSpectralDisks (P : ℕ) (hP : 0 < P) (N : ℕ) :
    I*(2^P : ℝ) ∉ highSpectralDisks N (Real.pi/4) := by
  intro hz
  obtain ⟨n,hn⟩ := Set.mem_iUnion.mp hz
  obtain ⟨_,hn⟩ := Set.mem_iUnion.mp hn
  have hd : ‖I*(2^P : ℝ)-(Real.pi : ℂ)*n‖ < Real.pi/4 := by
    simpa only [Metric.mem_ball,dist_eq_norm] using hn
  have him := Complex.abs_im_le_norm (I*(2^P : ℝ)-(Real.pi : ℂ)*n)
  have he : |(I*(2^P : ℝ)-(Real.pi : ℂ)*n).im| = (2 : ℝ)^P := by
    simp only [sub_im,mul_im,I_re,I_im,ofReal_re,ofReal_im,intCast_re,intCast_im,
      zero_mul,one_mul,mul_zero,zero_add,add_zero,sub_zero]
    exact abs_of_nonneg (by positivity)
  rw [he] at him
  have htwo : (2 : ℝ) ≤ 2^P := by
    simpa using pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) hP
  linarith [Real.pi_lt_four]

/-- A single balanced source violates the printed exhaustion at every cutoff. -/
theorem sourcePeriodicPrintedHeight_counterexample (P : ℕ)
    [Fact (1 ≤ (P : ℝ≥0∞))] (hP : 100000000 ≤ P) :
    ∃ ψ : CoeffPair (P : ℝ≥0∞), ‖ψ.fst‖ = ‖ψ.snd‖ ∧ ‖ψ‖ ≤ 1/16 ∧
      I*(2^P : ℝ) ∈ periodicSpectrum (ENNReal.natCast_ne_top P) (periodOnePotential ψ) ∧
      ∀ N : ℕ, I*(2^P : ℝ) ∉
        heightSpectralBox N ((1+8*‖ψ‖)^((P : ℝ≥0∞).toReal)) ∪ highSpectralDisks N (Real.pi/4) := by
  obtain ⟨ψ,hbal,hspec,hnorm⟩ := exists_small_dyadicSource P hP
  refine ⟨ψ,hbal,hnorm,hspec,?_⟩
  have him : |(I*(2^P : ℝ)).im| = (2 : ℝ)^P := by
    simp only [mul_im,I_re,I_im,ofReal_re,ofReal_im,zero_mul,one_mul,zero_add]
    exact abs_of_nonneg (by positivity)
  have hheight : (1+8*‖ψ‖)^((P : ℝ≥0∞).toReal) < |(I*(2^P : ℝ)).im| := by
    rw [ENNReal.toReal_natCast,Real.rpow_natCast,him]
    apply pow_lt_pow_left₀ (by linarith) (by positivity) (by omega : P ≠ 0)
  intro N hz
  rcases hz with hbox | hdisks
  · exact (not_le_of_gt hheight) hbox.2
  · exact dyadic_height_not_mem_highSpectralDisks P (by omega) N hdisks

section Concrete
local instance dyadicCounterexampleExponentFact : Fact (1 ≤ (100000000 : ℝ≥0∞)) := ⟨by norm_num⟩
local instance dyadicCounterexampleNatExponentFact : Fact (1 ≤ ((100000000 : ℕ) : ℝ≥0∞)) := ⟨by norm_num⟩

/-- The original all-p exhaustion assertion fails at a concrete finite exponent. -/
theorem not_sourceTheorem1_1_printed_exhaustion :
    ¬ ∀ ψ : CoeffPair 100000000, ∃ N : ℕ,
      periodicSpectrum (by norm_num) (periodOnePotential ψ) ⊆
        heightSpectralBox N ((1+8*‖ψ‖)^((100000000 : ℝ≥0∞).toReal)) ∪
          highSpectralDisks N (Real.pi/4) := by
  intro h
  obtain ⟨ψ,_,_,hspec,houtside⟩ := sourcePeriodicPrintedHeight_counterexample 100000000 (by omega)
  obtain ⟨N,hN⟩ := h ψ
  exact houtside N (hN hspec)
end Concrete

end NLS.ZakharovShabat
