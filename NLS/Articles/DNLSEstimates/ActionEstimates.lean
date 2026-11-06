import NLS.Articles.DNLSEstimates.HigherActions
import NLS.Articles.DNLSEstimates.Hierarchy
import NLS.ZakharovShabat.SourceSection26Actions
import NLS.ZakharovShabat.SourceSection26Sum

/-! # Article Section 4: comparisons of the actual indexed actions -/
noncomputable section
open Set NLS.ZakharovShabat
namespace NLS.Articles.DNLSEstimates

/-- Proposition 12's mean-value point lies in the actual periodic gap and
satisfies the precise localization radius, including collapsed gaps and m=0. -/
theorem proposition_twelve_mean_value (a : realTypeHigherSobolevSourceLocus 1)
    (n : ℤ) (hn : 8*‖sourcePiSobolevCoordinates 1 1 le_rfl a.val‖^2 ≤ 1+|(n : ℝ)|)
    (m : ℕ) :
    let ψ := higherSobolevSourceInclusion 1 a.val
    ∃ ζ ∈ Icc
      (canonicalPeriodicLeft (by simp) (by norm_num)
        (periodOnePotential ψ) (periodOnePotential_mem ψ) n).re
      (canonicalPeriodicRight (by simp) (by norm_num)
        (periodOnePotential ψ) (periodOnePotential_mem ψ) n).re,
      sourceIndexedHigherAction (by simp) (by norm_num) n (2*m) ψ =
        (ζ : ℂ)^(2*m)*sourceIndexedAction (by simp) (by norm_num) n ψ ∧
      |ζ-Real.pi*n| ≤ quadraticLocalizationRadius
        ‖sourcePiSobolevCoordinates 1 1 le_rfl a.val‖ n :=
  sourceSection26_meanValue_complex a n hn m

/-- Proposition 12's exterior comparison at every nonzero signed index. -/
theorem proposition_twelve_exterior (a : realTypeHigherSobolevSourceLocus 1)
    (n : ℤ) (hn0 : n ≠ 0)
    (hn : 8*‖sourcePiSobolevCoordinates 1 1 le_rfl a.val‖^2 ≤ 1+|(n : ℝ)|) (m : ℕ) :
    let ψ := higherSobolevSourceInclusion 1 a.val
    ((2 : ℝ)⁻¹)^m*(1+|((2*n : ℤ) : ℝ)*Real.pi|)^(2*m)*
        (sourceIndexedAction (by simp) (by norm_num) n ψ).re ≤
      4^m*(sourceIndexedHigherAction (by simp) (by norm_num) n (2*m) ψ).re ∧
    4^m*(sourceIndexedHigherAction (by simp) (by norm_num) n (2*m) ψ).re ≤
      (1+|((2*n : ℤ) : ℝ)*Real.pi|)^(2*m)*
        (sourceIndexedAction (by simp) (by norm_num) n ψ).re :=
  sourceSection26_exterior a n hn0 hn m

/-- Proposition 12's central estimate under its actual strict low-frequency
hypothesis. It is not applied to index zero when that hypothesis fails. -/
theorem proposition_twelve_central (a : realTypeHigherSobolevSourceLocus 1)
    (n : ℤ) (hn : 1+|(n : ℝ)| < 8*‖sourcePiSobolevCoordinates 1 1 le_rfl a.val‖^2)
    (m : ℕ) :
    let ψ := higherSobolevSourceInclusion 1 a.val
    4^m*‖sourceIndexedHigherAction (by simp) (by norm_num) n (2*m) ψ‖ ≤
      (16*Real.pi)^(2*m)*‖sourcePiSobolevCoordinates 1 1 le_rfl a.val‖^(4*m)*
        (sourceIndexedAction (by simp) (by norm_num) n ψ).re :=
  sourceSection26_central a n hn m

/-- Lemma 13: the Hamiltonian sign is the article's raw Riccati convention,
so (-1)^(m+1)*H_(2m+1) is the positive-leading physical Hamiltonian. -/
theorem lemma_thirteen (m : ℕ) (hm : 1 ≤ m)
    (a : realTypeHigherSobolevSourceLocus m) :
    actionMoment ⟨higherSobolevSourceInclusion m a.val, a.property⟩ m ≤
      (1+16*Real.pi)^(2*m)*
        (1+‖sourcePiSobolevCoordinates m 1 hm a.val‖)^(4*m)*
          ‖higherSobolevSourceInclusion m a.val‖^2 +
      2^m*((-1 : ℂ)^(m+1)*articleOddHamiltonian m hm a.val).re := by
  rw [articleOddHamiltonian_normalized]
  exact sourceSection26_action_estimate m hm a

end NLS.Articles.DNLSEstimates
