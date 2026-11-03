import NLS.KdV.HillHminusOneGluedActionLabels
import NLS.Articles.KdVPseudomeasures.OriginalHillLabels

/-! # Glued high contour actions on the full original physical domain

The entire original real mean-zero period-one H-minus-one distribution
is retained. For all sufficiently high ORIGINAL indices, the glued gap
square is the square of the original canonical gap, with exact action
normalization and vanishing equivalence. Low indices and the full
Birkhoff construction remain separate obligations.
-/
noncomputable section
set_option autoImplicit false
open Set Complex
namespace NLS.Articles.KdVPseudomeasures
open NLS.KdV

def originalHighHillAction (n : ℕ+) (q : OriginalHminusOnePotential) : ℂ :=
  hillHminusGluedHighAction n (originalPeriodOneCoefficients q)

def originalHighHillActionRatio (n : ℕ+) (q : OriginalHminusOnePotential) : ℂ :=
  hillHminusGluedHighActionRatio n (originalPeriodOneCoefficients q)

theorem exists_originalHighHillGapSquare_eq_canonical
    (q : OriginalHminusOnePotential) :
    ∃ N : ℕ, 2 ≤ N ∧ ∀ n : ℕ+, N ≤ (n : ℕ) →
      hillHminusGluedHighGapSquare n (originalPeriodOneCoefficients q) =
        originalCanonicalGapValues q (n : ℕ)^2 := by
  obtain ⟨N,hN,hlabels⟩ := exists_hillHminusGluedHighGapSquare_eq_labels
    (originalPeriodOneCoefficients q) (originalPeriodOneCoefficients_real q)
  refine ⟨N,hN,?_⟩
  intro n hn
  have he := (hlabels n hn).2
  have hn0 : ((n : ℕ) : ℤ) ≠ 0 := by exact_mod_cast n.ne_zero
  simpa only [originalCanonicalGapValues,if_neg hn0,Int.natAbs_natCast,originalHillLabels,
    ofReal_sub] using he

theorem exists_originalHighHillAction_factorization
    (q : OriginalHminusOnePotential) :
    ∃ N : ℕ, 2 ≤ N ∧ ∀ n : ℕ+, N ≤ (n : ℕ) →
      originalHighHillAction n q = originalCanonicalGapValues q (n : ℕ)^2 /
        (8*((Real.pi : ℂ)*(n : ℕ)))*originalHighHillActionRatio n q := by
  obtain ⟨N,hN,hgap⟩ := exists_originalHighHillGapSquare_eq_canonical q
  refine ⟨N,hN,?_⟩
  intro n hn
  rw [originalHighHillAction,hillHminusGluedHighAction,hgap n hn,originalHighHillActionRatio]

theorem exists_originalHighHillAction_normalization
    (q : OriginalHminusOnePotential) (epsilon : ℝ) (hepsilon : 0 < epsilon) :
    ∃ N : ℕ, 2 ≤ N ∧ ∀ n : ℕ+, N ≤ (n : ℕ) →
      ‖originalHighHillActionRatio n q-1‖ ≤ epsilon ∧
      ‖(8*((Real.pi : ℂ)*(n : ℕ)))*originalHighHillAction n q-originalCanonicalGapValues q (n : ℕ)^2‖ ≤
        ‖originalCanonicalGapValues q (n : ℕ)‖^2*epsilon ∧
      (originalHighHillAction n q = 0 ↔ originalCanonicalGapValues q (n : ℕ) = 0) := by
  obtain ⟨M,hM,hgap⟩ := exists_originalHighHillGapSquare_eq_canonical q
  obtain ⟨L,V,_,_,hqV,hfamily⟩ := exists_hillHminus_uniform_glued_high_actions
    (originalPeriodOneCoefficients q) epsilon hepsilon
  refine ⟨max M L,hM.trans (le_max_left _ _),?_⟩
  intro n hn
  have hnM : M ≤ (n : ℕ) := (le_max_left _ _).trans hn
  have hnL : L ≤ (n : ℕ) := (le_max_right _ _).trans hn
  obtain ⟨hR,_,hzero,herror⟩ := (hfamily n hnL).2 _ hqV
  rw [hgap n hnM,norm_pow] at herror
  rw [hgap n hnM,sq_eq_zero_iff] at hzero
  exact ⟨hR,herror,hzero⟩

end NLS.Articles.KdVPseudomeasures
