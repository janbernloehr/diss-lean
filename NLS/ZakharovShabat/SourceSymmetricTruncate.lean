import NLS.ZakharovShabat.SourceRealTypeFiniteApproximation
import NLS.SequenceSpaces.Compact

/-! # Compact symmetric source projections

The finite Fourier cutoff is a bounded complex linear map in the native
pair norm, including the Banach endpoints one and infinity.
-/

noncomputable section
open Set Filter Topology Metric
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- Keep both components on the symmetric finite interval in the native pair norm. -/
def sourceSymmetricTruncateCLM (M : ℕ) : CoeffPair p →L[ℂ] CoeffPair p :=
  (CoeffPair.toMax p).symm.toContinuousLinearMap.comp
    (((Coeff.truncateCLM (Finset.Icc (-(M:ℤ)) M)).prodMap
      (Coeff.truncateCLM (Finset.Icc (-(M:ℤ)) M))).comp (CoeffPair.toMax p).toContinuousLinearMap)

@[simp] theorem sourceSymmetricTruncateCLM_apply (M : ℕ) (a : CoeffPair p) :
    sourceSymmetricTruncateCLM M a = sourceSymmetricTruncate M a := rfl

/-- Finite output support gives compactness at every Banach sequence exponent. -/
theorem isCompactOperator_sourceSymmetricTruncateCLM (M : ℕ) :
    IsCompactOperator (sourceSymmetricTruncateCLM (p := p) M) := by
  let T := Coeff.truncateCLM (p := p) (Finset.Icc (-(M:ℤ)) M)
  have hT : IsCompactOperator T := Coeff.isCompactOperator_truncateCLM _
  have h₁ := (hT.comp_clm (ContinuousLinearMap.fst ℂ (Coeff p) (Coeff p))).clm_comp
    (ContinuousLinearMap.inl ℂ (Coeff p) (Coeff p))
  have h₂ := (hT.comp_clm (ContinuousLinearMap.snd ℂ (Coeff p) (Coeff p))).clm_comp
    (ContinuousLinearMap.inr ℂ (Coeff p) (Coeff p))
  have hprod : IsCompactOperator (T.prodMap T) := by
    have he : (T.prodMap T : (Coeff p × Coeff p) → (Coeff p × Coeff p)) =
        (fun a => (T a.1,0))+(fun a => (0,T a.2)) := by
      funext a
      change (T a.1,T a.2) = (T a.1+0,0+T a.2)
      simp
    rw [he]
    exact h₁.add h₂
  exact (hprod.comp_clm (CoeffPair.toMax p).toContinuousLinearMap).clm_comp
    (CoeffPair.toMax p).symm.toContinuousLinearMap

end NLS.ZakharovShabat
