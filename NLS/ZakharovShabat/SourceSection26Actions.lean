import NLS.ZakharovShabat.SourceH1HigherActionEstimates
import NLS.ZakharovShabat.SourcePiSobolevCoordinates
import NLS.ZakharovShabat.SourceHigherSobolevFiniteGapDensity
import NLS.ZakharovShabat.SourceIndexedHigherActionReal

/-! # Proposition 26.1 for the original indexed actions

All real H¹ sources and every natural odd level are covered, including
collapsed gaps. The norm is the exact physical pair norm.
-/
noncomputable section
open Set
namespace NLS.ZakharovShabat

/-- The printed two-sided exterior estimate, including the exact threshold boundary. -/
theorem sourceSection26_exterior (a : realTypeHigherSobolevSourceLocus 1)
    (n : ℤ) (hn0 : n ≠ 0)
    (hn : 8*‖sourcePiSobolevCoordinates 1 1 le_rfl a.val‖^2 ≤ 1+|(n:ℝ)|) (m : ℕ) :
    let ψ := higherSobolevSourceInclusion 1 a.val
    ((2:ℝ)⁻¹)^m*(1+|((2*n:ℤ):ℝ)*Real.pi|)^(2*m)*
        (sourceIndexedAction (by simp) (by norm_num) n ψ).re ≤
      4^m*(sourceIndexedHigherAction (by simp) (by norm_num) n (2*m) ψ).re ∧
    4^m*(sourceIndexedHigherAction (by simp) (by norm_num) n (2*m) ψ).re ≤
      (1+|((2*n:ℤ):ℝ)*Real.pi|)^(2*m)*
        (sourceIndexedAction (by simp) (by norm_num) n ψ).re := by
  let ψ : realTypeSourceSubmodule 2 := ⟨higherSobolevSourceInclusion 1 a.val,a.property⟩
  have h := sourceRealHigherAction_H1_exterior_bounds ψ
    (normalizedWeightedPeriodOne _ (sourcePiSobolevCoordinates 1 1 le_rfl a.val))
    (weightedBaseToPair_sourcePiSobolevOne 1 le_rfl a.val) n hn0
    (by simpa only [norm_normalizedWeightedPeriodOne] using hn) m
  have he := sourceIndexedHigherAction_eq_real (by simp) (by norm_num) ψ n (2*m)
  dsimp only [ψ] at he
  simpa only [he, Complex.ofReal_re,
    sourceIndexedAction_eq_sourceRealAction (hφ := a.property)] using h

/-- The central estimate uses the original complex action norm and includes index zero. -/
theorem sourceSection26_central (a : realTypeHigherSobolevSourceLocus 1)
    (n : ℤ) (hn : 1+|(n:ℝ)| < 8*‖sourcePiSobolevCoordinates 1 1 le_rfl a.val‖^2) (m : ℕ) :
    let ψ := higherSobolevSourceInclusion 1 a.val
    4^m*‖sourceIndexedHigherAction (by simp) (by norm_num) n (2*m) ψ‖ ≤
      (16*Real.pi)^(2*m)*‖sourcePiSobolevCoordinates 1 1 le_rfl a.val‖^(4*m)*
        (sourceIndexedAction (by simp) (by norm_num) n ψ).re := by
  let ψ : realTypeSourceSubmodule 2 := ⟨higherSobolevSourceInclusion 1 a.val,a.property⟩
  have h := sourceRealHigherAction_H1_central_bound ψ
    (normalizedWeightedPeriodOne _ (sourcePiSobolevCoordinates 1 1 le_rfl a.val))
    (weightedBaseToPair_sourcePiSobolevOne 1 le_rfl a.val) n
    (by simpa only [norm_normalizedWeightedPeriodOne] using hn) m
  have he := sourceIndexedHigherAction_eq_real (by simp) (by norm_num) ψ n (2*m)
  dsimp only [ψ] at he
  simpa only [he, Complex.norm_real, Real.norm_eq_abs,
    sourceIndexedAction_eq_sourceRealAction (hφ := a.property), norm_normalizedWeightedPeriodOne] using h

/-- An actual gap point gives the mean-value identity and the exact quadratic radius. -/
theorem sourceSection26_meanValue (a : realTypeHigherSobolevSourceLocus 1)
    (n : ℤ) (hn : 8*‖sourcePiSobolevCoordinates 1 1 le_rfl a.val‖^2 ≤ 1+|(n:ℝ)|) (m : ℕ) :
    let ψ := higherSobolevSourceInclusion 1 a.val
    ∃ ζ ∈ Icc
      (canonicalPeriodicLeft (by simp) (by norm_num) (periodOnePotential ψ) (periodOnePotential_mem ψ) n).re
      (canonicalPeriodicRight (by simp) (by norm_num) (periodOnePotential ψ) (periodOnePotential_mem ψ) n).re,
      (sourceIndexedHigherAction (by simp) (by norm_num) n (2*m) ψ).re =
        ζ^(2*m)*(sourceIndexedAction (by simp) (by norm_num) n ψ).re ∧
      |ζ-Real.pi*n| ≤ quadraticLocalizationRadius ‖sourcePiSobolevCoordinates 1 1 le_rfl a.val‖ n := by
  let ψ : realTypeSourceSubmodule 2 := ⟨higherSobolevSourceInclusion 1 a.val,a.property⟩
  have h := sourceRealHigherAction_H1_meanValue_localization ψ
    (normalizedWeightedPeriodOne _ (sourcePiSobolevCoordinates 1 1 le_rfl a.val))
    (weightedBaseToPair_sourcePiSobolevOne 1 le_rfl a.val) n
    (by simpa only [norm_normalizedWeightedPeriodOne] using hn) m
  have he := sourceIndexedHigherAction_eq_real (by simp) (by norm_num) ψ n (2*m)
  dsimp only [ψ] at he
  simpa only [he, Complex.ofReal_re,
    sourceIndexedAction_eq_sourceRealAction (hφ := a.property), norm_normalizedWeightedPeriodOne] using h

/-- The mean-value formula also holds as a literal complex equality of the original contour actions. -/
theorem sourceSection26_meanValue_complex (a : realTypeHigherSobolevSourceLocus 1)
    (n : ℤ) (hn : 8*‖sourcePiSobolevCoordinates 1 1 le_rfl a.val‖^2 ≤ 1+|(n:ℝ)|) (m : ℕ) :
    let ψ := higherSobolevSourceInclusion 1 a.val
    ∃ ζ ∈ Icc
      (canonicalPeriodicLeft (by simp) (by norm_num) (periodOnePotential ψ) (periodOnePotential_mem ψ) n).re
      (canonicalPeriodicRight (by simp) (by norm_num) (periodOnePotential ψ) (periodOnePotential_mem ψ) n).re,
      sourceIndexedHigherAction (by simp) (by norm_num) n (2*m) ψ =
        (ζ:ℂ)^(2*m)*sourceIndexedAction (by simp) (by norm_num) n ψ ∧
      |ζ-Real.pi*n| ≤ quadraticLocalizationRadius ‖sourcePiSobolevCoordinates 1 1 le_rfl a.val‖ n := by
  let ψ : realTypeSourceSubmodule 2 := ⟨higherSobolevSourceInclusion 1 a.val,a.property⟩
  let φ := normalizedWeightedPeriodOne (SpectralWeight.piSobolev 1 (by norm_num))
    (sourcePiSobolevCoordinates 1 1 le_rfl a.val)
  have hφ := weightedBaseToPair_sourcePiSobolevOne 1 le_rfl a.val
  obtain ⟨ζ,hζ,he⟩ := sourceIndexedHigherAction_eq_power_mul_action (by simp) (by norm_num) ψ n (2*m)
  refine ⟨ζ,hζ,he,?_⟩
  have heven : weightedBaseToPair (SpectralWeight.piSobolev 1 (by norm_num)) φ ∈ pairParitySubspace 0 :=
    hφ ▸ periodOnePotential_mem ψ.val
  have h := H1_gap_point_localization φ heven n
    (by simpa only [φ,norm_normalizedWeightedPeriodOne] using hn) ζ
    (by simpa only [φ,hφ] using hζ)
  simpa only [φ,norm_normalizedWeightedPeriodOne] using h

end NLS.ZakharovShabat
