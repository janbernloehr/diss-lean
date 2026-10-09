import NLS.ZakharovShabat.SourcePeriodicHeightCounterexample

/-! # Necessary exponent dependence of a periodic height coefficient

The balanced dyadic family rules out every fixed nonnegative replacement
for the printed constant eight. A universal coefficient C at integer P>=3
must satisfy P-2 <= 276480*C^2, even with a freely chosen central cutoff.
-/
noncomputable section
open Set Complex
open scoped ENNReal
namespace NLS.ZakharovShabat

/-- The dyadic family defeats a coefficient whose square is too small. -/
theorem exists_sourcePeriodicHeightCoefficient_counterexample (P : ℕ)
    [Fact (1 ≤ (P : ℝ≥0∞))] (hP : 3 ≤ P) {C : ℝ} (hC : 0 ≤ C)
    (hPC : 276480*C^2 < (P-2 : ℕ)) :
    ∃ ψ : CoeffPair (P : ℝ≥0∞), ‖ψ.fst‖ = ‖ψ.snd‖ ∧
      I*(2^P : ℝ) ∈ periodicSpectrum (ENNReal.natCast_ne_top P) (periodOnePotential ψ) ∧
      (1+C*‖ψ‖)^((P : ℝ≥0∞).toReal) < |(I*(2^P : ℝ)).im| := by
  obtain ⟨ψ,hbal,hspec,hnorm⟩ := exists_balanced_dyadicSource_norm_le P hP
  refine ⟨ψ,hbal,hspec,?_⟩
  have hD : (0 : ℝ) < (P-2 : ℕ) := by exact_mod_cast (show 0 < P-2 by omega)
  have he : (2*C*Real.sqrt (69120/(P-2 : ℕ)))^2 = 276480*C^2/(P-2 : ℕ) := by
    rw [mul_pow,Real.sq_sqrt (by positivity)]
    ring
  have hs : (2*C*Real.sqrt (69120/(P-2 : ℕ)))^2 < 1 := by
    rw [he,div_lt_one hD]
    exact hPC
  have hcsmall : C*‖ψ‖ < 1 := by
    have hn := mul_le_mul_of_nonneg_left hnorm hC
    nlinarith [sq_nonneg (2*C*Real.sqrt (69120/(P-2 : ℕ))-1)]
  have him : |(I*(2^P : ℝ)).im| = (2 : ℝ)^P := by
    simp only [mul_im,I_re,I_im,ofReal_re,ofReal_im,zero_mul,one_mul,zero_add]
    exact abs_of_nonneg (by positivity)
  rw [ENNReal.toReal_natCast,Real.rpow_natCast,him]
  exact pow_lt_pow_left₀ (by linarith) (by positivity) (by omega : P ≠ 0)

/-- Any universal source-norm periodic strip coefficient grows at least as sqrt(P-2). -/
theorem sourcePeriodicHeightCoefficient_necessary {P : ℕ}
    [Fact (1 ≤ (P : ℝ≥0∞))] (hP : 3 ≤ P) {C : ℝ} (hC : 0 ≤ C)
    (hheight : ∀ ψ : CoeffPair (P : ℝ≥0∞), ∀ z ∈
      periodicSpectrum (ENNReal.natCast_ne_top P) (periodOnePotential ψ),
      |z.im| ≤ (1+C*‖ψ‖)^((P : ℝ≥0∞).toReal)) :
    ((P-2 : ℕ) : ℝ) ≤ 276480*C^2 := by
  by_contra h
  obtain ⟨ψ,_,hspec,hlt⟩ := exists_sourcePeriodicHeightCoefficient_counterexample P hP hC (lt_of_not_ge h)
  exact (not_le_of_gt hlt) (hheight ψ _ hspec)

/-- Allowing a source-dependent cutoff and the high disks does not avoid the lower bound. -/
theorem sourcePeriodicCountingHeightCoefficient_necessary {P : ℕ}
    [Fact (1 ≤ (P : ℝ≥0∞))] (hP : 3 ≤ P) {C : ℝ} (hC : 0 ≤ C)
    (hcount : ∀ ψ : CoeffPair (P : ℝ≥0∞), ∃ N : ℕ,
      periodicSpectrum (ENNReal.natCast_ne_top P) (periodOnePotential ψ) ⊆
        heightSpectralBox N ((1+C*‖ψ‖)^((P : ℝ≥0∞).toReal)) ∪ highSpectralDisks N (Real.pi/4)) :
    ((P-2 : ℕ) : ℝ) ≤ 276480*C^2 := by
  by_contra h
  obtain ⟨ψ,_,hspec,hlt⟩ := exists_sourcePeriodicHeightCoefficient_counterexample P hP hC (lt_of_not_ge h)
  obtain ⟨N,hN⟩ := hcount ψ
  rcases hN hspec with hbox | hdisks
  · exact (not_le_of_gt hlt) hbox.2
  · exact dyadic_height_not_mem_highSpectralDisks P (by omega) N hdisks

/-- No fixed nonnegative coefficient bounds the original periodic spectra at all integer exponents. -/
theorem not_exists_uniform_sourcePeriodicHeightCoefficient :
    ¬ ∃ C : ℝ, 0 ≤ C ∧ ∀ P : ℕ, ∀ hP : 3 ≤ P,
      let _ : Fact (1 ≤ (P : ℝ≥0∞)) := ⟨by exact_mod_cast (show 1 ≤ P by omega)⟩
      ∀ ψ : CoeffPair (P : ℝ≥0∞), ∀ z ∈
        periodicSpectrum (ENNReal.natCast_ne_top P) (periodOnePotential ψ),
        |z.im| ≤ (1+C*‖ψ‖)^((P : ℝ≥0∞).toReal) := by
  rintro ⟨C,hC,h⟩
  obtain ⟨K,hK⟩ := exists_nat_gt (max (276480*C^2) 0)
  let P := K+3
  have hP : 3 ≤ P := by omega
  let _ : Fact (1 ≤ (P : ℝ≥0∞)) := ⟨by exact_mod_cast (show 1 ≤ P by omega)⟩
  have hn := sourcePeriodicHeightCoefficient_necessary hP hC (h P hP)
  have hk : 276480*C^2 < (K : ℝ) := (le_max_left _ _).trans_lt hK
  have he : ((P-2 : ℕ) : ℝ) = (K : ℝ)+1 := by dsimp [P]; push_cast; ring
  rw [he] at hn
  linarith

/-- No fixed nonnegative replacement for eight repairs the all-exponent counting-box assertion. -/
theorem not_exists_uniform_sourcePeriodicCountingHeightCoefficient :
    ¬ ∃ C : ℝ, 0 ≤ C ∧ ∀ P : ℕ, ∀ hP : 3 ≤ P,
      let _ : Fact (1 ≤ (P : ℝ≥0∞)) := ⟨by exact_mod_cast (show 1 ≤ P by omega)⟩
      ∀ ψ : CoeffPair (P : ℝ≥0∞), ∃ N : ℕ,
        periodicSpectrum (ENNReal.natCast_ne_top P) (periodOnePotential ψ) ⊆
          heightSpectralBox N ((1+C*‖ψ‖)^((P : ℝ≥0∞).toReal)) ∪ highSpectralDisks N (Real.pi/4) := by
  rintro ⟨C,hC,h⟩
  obtain ⟨K,hK⟩ := exists_nat_gt (max (276480*C^2) 0)
  let P := K+3
  have hP : 3 ≤ P := by omega
  let _ : Fact (1 ≤ (P : ℝ≥0∞)) := ⟨by exact_mod_cast (show 1 ≤ P by omega)⟩
  have hn := sourcePeriodicCountingHeightCoefficient_necessary hP hC (h P hP)
  have hk : 276480*C^2 < (K : ℝ) := (le_max_left _ _).trans_lt hK
  have he : ((P-2 : ℕ) : ℝ) = (K : ℝ)+1 := by dsimp [P]; push_cast; ring
  rw [he] at hn
  linarith

end NLS.ZakharovShabat
