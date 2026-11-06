import NLS.KdV.HillInfiniteNormingGardner

noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology MeasureTheory
open NLS.ComplexAnalysis NLS.LinearVolterra NLS.FunctionalAnalysis NLS.ZakharovShabat
open scoped ENNReal ComplexConjugate Classical

namespace NLS.KdV



variable
    (h0q : SpectralWeight.one.toCoeff (0 : WeightedCoeff SpectralWeight.one.toWeight 2)∈Coeff.paritySubspace 0)
    (h0r : IsRealHillPotential (SpectralWeight.one.toCoeff (0 : WeightedCoeff SpectralWeight.one.toWeight 2)))
include h0q h0r

/-- Adding one actual norming cotangent preserves the absolutely convergent
physical norming span and its genuine spatial derivative domain. -/
theorem exists_hillInfiniteNormingGradient_add_term
    (q : RealPeriodOneHillPotential) (c : ℕ → ℂ) (hc : Summable (fun k => ‖c k‖))
    (j : ℕ) (a : ℂ) :
    ∃ d : ℕ → ℂ, Summable (fun k : ℕ => ‖d k‖) ∧
      hillInfiniteNormingGradient q d=hillInfiniteNormingGradient q c+
        a • hillLogNormingGradientCurve q (j+1) (by omega) := by
  let d : ℕ → ℂ := fun k => c k+(if k=j then a else 0)
  have hsingle : Summable (fun k : ℕ => if k=j then ‖a‖ else 0) := (hasSum_ite_eq j ‖a‖).summable
  have hd : Summable (fun k : ℕ => ‖d k‖) := by
    apply (hc.add hsingle).of_nonneg_of_le (fun k => norm_nonneg _)
    intro k
    by_cases hk : k=j
    · simpa only [d,if_pos hk] using norm_add_le (c k) a
    · simp only [d,if_neg hk,add_zero,le_refl]
  have hsG := (hillNormingGradientSeries_norm_summable h0q h0r q c hc).1.of_norm
  have hvec : Summable (fun k : ℕ => if k=j then a • hillLogNormingGradientCurve q (j+1) (by omega) else 0) :=
    (hasSum_ite_eq j _).summable
  have hpoint (k : ℕ) :
      d k • hillLogNormingGradientCurve q (k+1) (by omega)=
        c k • hillLogNormingGradientCurve q (k+1) (by omega)+
          (if k=j then a • hillLogNormingGradientCurve q (j+1) (by omega) else 0) := by
    by_cases hk : k=j
    · subst k
      simp only [d,if_true]
      exact add_smul (c j) a (hillLogNormingGradientCurve q (j+1) (by omega))
    · simp only [d,if_neg hk,add_zero]
  refine ⟨d,hd,?_⟩
  change (∑' k : ℕ,d k • hillLogNormingGradientCurve q (k+1) (by omega))=_
  rw [tsum_congr hpoint,hsG.tsum_add hvec,tsum_ite_eq]
  rfl

end NLS.KdV
