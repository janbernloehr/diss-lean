import NLS.Articles.KdVPseudomeasures.SourceWienerSpectralAdapter
import NLS.Articles.KdVPseudomeasures.WeightedComplexMidpoints

/-! The actual full complex gap and midpoint sequences on the original
Wiener source, including their exact positive indices and uniform prefix bounds. -/
noncomputable section
open scoped ENNReal
open NLS.KdV NLS.Fourier NLS.Fourier.PeriodicFourierLebesgue
namespace NLS.Articles.KdVPseudomeasures

theorem sourceWienerAdmissible : AdmissiblePredualOrder 0 := ⟨by norm_num,by norm_num⟩

def sourceWienerGapValues (w : SpectralWeight)
    (q : PeriodicFourierLebesgue (2:ℝ) (w.negativeSobolev 0) 1) (k : ℤ) : ℂ :=
  sourceWeightedCanonicalGapValues w 0 sourceWienerAdmissible (sourceWienerInfinity w q) k

def sourceWienerMidpointValues (w : SpectralWeight)
    (q : PeriodicFourierLebesgue (2:ℝ) (w.negativeSobolev 0) 1)
    (hp : IsPeriodicDistribution 1 q.val.toTempered) (k : ℤ) : ℂ :=
  sourceWeightedDirichletMidpointValues w 0 sourceWienerAdmissible (sourceWienerInfinity w q)
    (by rw [sourceWienerInfinity_val]; exact hp) k

theorem sourceWienerGapValues_nat (w : SpectralWeight)
    (q : PeriodicFourierLebesgue (2:ℝ) (w.negativeSobolev 0) 1) (n : ℕ) (hn : 1 ≤ n) :
    sourceWienerGapValues w q (n:ℤ) =
      sourceHillComplexLabels 0 sourceWienerAdmissible (sourceWienerPlain w q) (2*n)-
        sourceHillComplexLabels 0 sourceWienerAdmissible (sourceWienerPlain w q) (2*n-1) :=
  sourceWeightedCanonicalGaps_nat_apply w 0 sourceWienerAdmissible (sourceWienerInfinity w q) n hn

theorem sourceWienerMidpointValues_nat (w : SpectralWeight)
    (q : PeriodicFourierLebesgue (2:ℝ) (w.negativeSobolev 0) 1)
    (hp : IsPeriodicDistribution 1 q.val.toTempered) (n : ℕ+) :
    sourceWienerMidpointValues w q hp (n:ℤ) =
      sourceComplexDirichletMidpoint 0 sourceWienerAdmissible (sourceWienerPlain w q)
        (by rw [sourceWienerPlain_val]; exact hp) n :=
  sourceWeightedDirichletMidpoints_nat_apply w 0 sourceWienerAdmissible (sourceWienerInfinity w q)
    (by rw [sourceWienerInfinity_val]; exact hp) n

theorem sourceWienerGapValues_neg (w : SpectralWeight)
    (q : PeriodicFourierLebesgue (2:ℝ) (w.negativeSobolev 0) 1) (k : ℤ) :
    sourceWienerGapValues w q (-k) = sourceWienerGapValues w q k :=
  sourceWeightedCanonicalGapValues_neg w 0 sourceWienerAdmissible (sourceWienerInfinity w q) k

theorem sourceWienerMidpointValues_neg (w : SpectralWeight)
    (q : PeriodicFourierLebesgue (2:ℝ) (w.negativeSobolev 0) 1)
    (hp : IsPeriodicDistribution 1 q.val.toTempered) (k : ℤ) :
    sourceWienerMidpointValues w q hp (-k) = sourceWienerMidpointValues w q hp k := by
  simp only [sourceWienerMidpointValues,sourceWeightedDirichletMidpointValues,neg_eq_zero,Int.natAbs_neg]

theorem sourceWienerSpectralValues_uniform_infinity (w : SpectralWeight) (R : ℝ) :
    ∃ B₁ B₂ : ℝ, 0 ≤ B₁ ∧ 0 ≤ B₂ ∧
      ∀ q : PeriodicFourierLebesgue (2:ℝ) (w.negativeSobolev 0) 1, ‖q‖ ≤ R →
        ∀ hp : IsPeriodicDistribution 1 q.val.toTempered, ∀ k : ℤ,
          ‖(w k:ℂ)*sourceWienerGapValues w q k‖ ≤ B₁ ∧
          ‖(w k:ℂ)*sourceWienerMidpointValues w q hp k‖ ≤ B₂ := by
  obtain ⟨B₁,hB₁,hgap⟩ := (sourceTheorem2_1_i w 0 sourceWienerAdmissible).2 R
  obtain ⟨B₂,hB₂,hmid⟩ := (sourceTheorem2_1_ii w 0 sourceWienerAdmissible).2 R
  refine ⟨B₁,B₂,hB₁,hB₂,?_⟩
  intro q hq hp k
  have hQ : ‖sourceWienerInfinity w q‖ ≤ R := (norm_sourceWienerInfinity_le w q).trans hq
  have hpQ : IsPeriodicDistribution 1 (sourceWienerInfinity w q).val.toTempered := by
    rw [sourceWienerInfinity_val]
    exact hp
  have hg := (lp.norm_apply_le_norm (by simp : (⊤:ℝ≥0∞) ≠ 0)
    (WeightedCoeff.weightEquiv _ ⊤ (sourceWeightedCanonicalGaps w 0 sourceWienerAdmissible
      (sourceWienerInfinity w q))) k).trans (hgap _ hQ)
  have hm := (lp.norm_apply_le_norm (by simp : (⊤:ℝ≥0∞) ≠ 0)
    (WeightedCoeff.weightEquiv _ ⊤ (sourceWeightedDirichletMidpoints w 0 sourceWienerAdmissible
      (sourceWienerInfinity w q) hpQ)) k).trans (hmid _ hQ hpQ)
  change ‖(w.negativeSobolev 0 k:ℂ)*sourceWienerGapValues w q k‖ ≤ B₁ at hg
  change ‖(w.negativeSobolev 0 k:ℂ)*sourceWienerMidpointValues w q hp k‖ ≤ B₂ at hm
  simp only [SpectralWeight.negativeSobolev_apply,Weight.sobolev_zero_apply,div_one] at hg hm
  exact ⟨hg,hm⟩

end NLS.Articles.KdVPseudomeasures
