import NLS.Articles.DNLSEstimates.MainEstimates
import NLS.ZakharovShabat.SourceIndexedHigherActionReal
import NLS.ZakharovShabat.SourceIndexedHigherActionTrace
import NLS.ZakharovShabat.SourceSection19Original
import NLS.ZakharovShabat.SourceH1ConverseActionEstimate

/-!
# Higher actions and the article's trace formula

The article's level k+1 is spectral power k in `sourceIndexedHigherAction`.
The first Hamiltonian is the positive mass displayed in Section 2. For
levels at least two the Hamiltonian is the literal Riccati density mean in
Appendix B. The appendix's first-level sign is corrected to agree with the
positive mass convention. No Hamiltonian is defined through spectral actions.
-/
noncomputable section
open Set NLS.ZakharovShabat
namespace NLS.Articles.DNLSEstimates

/-- The level-one action in Section 2 is the original indexed action. -/
theorem higherAction_level_one (n : ℤ) (a : CoeffPair 2) :
    sourceIndexedHigherAction (by simp) (by norm_num) n 0 a =
      sourceIndexedAction (by simp) (by norm_num) n a :=
  sourceIndexedHigherAction_zero (by simp) (by norm_num) n a

/-- Section 2: every higher action has a real value on the real source form. -/
theorem higherAction_real (a : realTypeSourceSubmodule 2) (n : ℤ) (k : ℕ) :
    (sourceIndexedHigherAction (by simp) (by norm_num) n k a.val).im = 0 :=
  sourceIndexedHigherAction_real (by simp) (by norm_num) a n k

/-- Section 2: all odd printed levels 2m+1 are nonnegative. -/
theorem higherAction_odd_nonneg (a : realTypeSourceSubmodule 2) (n : ℤ) (m : ℕ) :
    0 ≤ (sourceIndexedHigherAction (by simp) (by norm_num) n (2*m) a.val).re :=
  sourceIndexedHigherAction_even_nonneg (by simp) (by norm_num) a n m

/-- The valid gap-detection converse includes every odd printed level.
The unrestricted all-level converse in the prose on p. 9 is qualified. -/
theorem higherAction_odd_zero_iff_gap_zero
    (a : realTypeSourceSubmodule 2) (n : ℤ) (m : ℕ) :
    sourceIndexedHigherAction (by simp) (by norm_num) n (2*m) a.val = 0 ↔
      canonicalPeriodicGap (by simp) (by norm_num)
        (periodOnePotential a.val) (periodOnePotential_mem a.val) n = 0 :=
  sourceIndexedHigherAction_even_eq_zero_iff (by simp) (by norm_num) a n m

/-- Formula (8), with one point inside the actual nth periodic gap. -/
theorem higherAction_mean_value (a : realTypeSourceSubmodule 2) (n : ℤ) (m : ℕ) :
    ∃ ζ ∈ Icc
      (canonicalPeriodicLeft (by simp) (by norm_num)
        (periodOnePotential a.val) (periodOnePotential_mem a.val) n).re
      (canonicalPeriodicRight (by simp) (by norm_num)
        (periodOnePotential a.val) (periodOnePotential_mem a.val) n).re,
      sourceIndexedHigherAction (by simp) (by norm_num) n (2*m) a.val =
        (ζ : ℂ)^(2*m) * sourceIndexedAction (by simp) (by norm_num) n a.val :=
  sourceIndexedHigherAction_eq_power_mul_action (by simp) (by norm_num) a n (2*m)

/-- The Section 2 analyticity assertion holds at every original higher level
on the common complex neighborhood, without Sobolev regularity assumptions. -/
theorem higherAction_analytic {W U : Set (CoeffPair 2)}
    (Q : SourceSection19Data (by simp) (by norm_num) W U) (n : ℤ) (k : ℕ) :
    AnalyticOnNhd ℂ (sourceIndexedHigherAction (by simp) (by norm_num) n k) U :=
  Q.analytic_indexedHigherAction n k

/-- Every collapsed complex gap has zero action at every printed level.
The converse is asserted separately for the valid odd real levels. -/
theorem higherAction_collapsed {W U : Set (CoeffPair 2)}
    (Q : SourceSection19Data (by simp) (by norm_num) W U)
    (a : CoeffPair 2) (ha : a ∈ U) (n : ℤ) (k : ℕ)
    (hg : canonicalPeriodicGap (by simp) (by norm_num)
      (periodOnePotential a) (periodOnePotential_mem a) n = 0) :
    sourceIndexedHigherAction (by simp) (by norm_num) n k a = 0 :=
  Q.indexedHigherAction_of_collapsed a ha n k hg

/-- The article Hamiltonian of order k+1, defined by the physical Riccati
Fourier mean. Order one uses the positive physical mass from Section 2;
Appendix B's literal negative mean at that order is corrected. -/
def hierarchyHamiltonian (s k : ℕ) (hk : k ≤ s) (a : SobolevSource s) : ℂ :=
  if k = 0 then sobolevNLSHamiltonian s a 1 (by omega)
  else ∑' j : ℤ, a.1.val (-j) * (sobolevRiccatiDensity s a k hk).val j

/-- Theorem 4 on the full chosen complex source domain, with the printed
factor -1/(2i)^k and absolute convergence. The Hamiltonian order is k+1. -/
theorem theorem_four {W U : Set (CoeffPair 2)}
    (Q : SourceSection19Data (by simp) (by norm_num) W U)
    (k : ℕ) (hk : 1 ≤ k) (a : SobolevSource k)
    (ha : higherSobolevSourceInclusion k a ∈ U) :
    Summable (fun n : ℤ => ‖sourceIndexedHigherAction (by simp) (by norm_num) n k
      (higherSobolevSourceInclusion k a)‖) ∧
    (∑' n : ℤ, sourceIndexedHigherAction (by simp) (by norm_num) n k
      (higherSobolevSourceInclusion k a)) =
        -hierarchyHamiltonian k k le_rfl a / (2*Complex.I)^k := by
  refine ⟨Q.summable_norm_indexedHigherAction k k (by omega) a ha, ?_⟩
  rw [Q.indexedHigherAction_hamiltonian_trace k k le_rfl a ha,
    sobolevNLSHamiltonian_succ_eq_tsum k k le_rfl]
  rw [hierarchyHamiltonian, if_neg (by omega : k ≠ 0)]
  have hc (z : ℂ) : (-Complex.I)^(k+2)*z/(2 : ℂ)^k = -z/(2*Complex.I)^k := by
    have hsq : (-Complex.I)^2 = (-1 : ℂ) := by norm_num [Complex.I_sq]
    rw [pow_add, hsq, mul_pow]
    simp only [div_eq_mul_inv, mul_inv_rev]
    simp only [← inv_pow, Complex.inv_I]
    ring
  exact hc _

/-- Theorem 4's complex domain and its proof data exist before the level
and potential are chosen. No trace hypothesis is supplied by a caller. -/
theorem exists_theorem_four_domain :
    ∃ W U : Set (CoeffPair 2),
      SourceSection19Data (by simp) (by norm_num) W U ∧
      ∀ k : ℕ, ∀ _hk : 1 ≤ k, ∀ a : SobolevSource k,
        higherSobolevSourceInclusion k a ∈ U →
        Summable (fun n : ℤ => ‖sourceIndexedHigherAction (by simp) (by norm_num) n k
          (higherSobolevSourceInclusion k a)‖) ∧
        (∑' n : ℤ, sourceIndexedHigherAction (by simp) (by norm_num) n k
          (higherSobolevSourceInclusion k a)) =
          -hierarchyHamiltonian k k le_rfl a / (2*Complex.I)^k := by
  obtain ⟨W₀,W,V,s,D,A,U,_,Q⟩ := sourceSection19_original
    (p := 2) (by simp) (by norm_num)
  exact ⟨A,U,Q,fun k hk a ha => theorem_four Q k hk a ha⟩

/-- Lemma 15, including both printed consequences. All action moments use
original indexed actions and the exact physical frequency 2*pi*n. -/
theorem lemma_fifteen (a : realTypeSobolevSourceLocus) :
    ((periodOneSobolevHamiltonian a.val).re -
        2*(periodOneSobolevMass a.val).re^2 ≤
      ∑' n : ℤ, (2*Real.pi*(n : ℝ))^2 *
        ‖sourceIndexedAction (by simp) (by norm_num) n (sourceH1RealSource a).val‖) ∧
    ((periodOneSobolevHamiltonian a.val).re ≤
      actionMoment (sourceH1RealSource a) 1 + 2*(actionMoment (sourceH1RealSource a) 0)^2) ∧
    ((1/3 : ℝ)*‖sourcePhysicalH1Coordinates a.val‖^2 ≤
      actionMoment (sourceH1RealSource a) 1 + (actionMoment (sourceH1RealSource a) 0)^2) := by
  refine ⟨?_, ?_, ?_⟩
  · have he (n : ℤ) :
        ‖sourceIndexedAction (by simp) (by norm_num) n (sourceH1RealSource a).val‖ =
        (sourceRealAction (by simp) (by norm_num) (sourceH1RealSource a).val
          (sourceH1RealSource a).property n).re := by
      rw [sourceIndexedAction_eq_sourceRealAction (by simp) (by norm_num)
        n (sourceH1RealSource a).val (sourceH1RealSource a).property,
        norm_sourceRealAction]
    simp_rw [he]
    exact sourceH1_energy_action_bound a
  · simp only [actionMoment]
    simp_rw [sourceIndexedWeightedActionTerm_eq]
    exact sourceH1_energy_le_weighted_actions a
  · simp only [actionMoment]
    simp_rw [sourceIndexedWeightedActionTerm_eq]
    exact sourceH1_third_norm_sq_le_actions a

end NLS.Articles.DNLSEstimates
