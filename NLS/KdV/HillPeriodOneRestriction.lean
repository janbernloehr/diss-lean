import NLS.KdV.HillComplexWeightedEmbedding
import NLS.SequenceSpaces.WeightedRestriction

noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology MeasureTheory
open NLS.ComplexAnalysis NLS.ZakharovShabat
open scoped ENNReal ComplexConjugate Classical

namespace NLS.KdV



/-- Extract original period-one coefficients from the even Hill indices. -/
def hillPeriodOneRestriction (w : SpectralWeight) :
    WeightedCoeff w.toWeight 2 →L[ℂ] WeightedCoeff w.doubleIndex.toWeight 2 :=
  WeightedCoeff.restrictIndicesCLM w.toWeight (Coeff.parityEmbedding 0)

theorem hillPeriodOneRestriction_apply (w : SpectralWeight) (q : WeightedCoeff w.toWeight 2) (k : ℤ) :
    (hillPeriodOneRestriction w q).val k=q.val (2*k) := by
  unfold hillPeriodOneRestriction
  have ht := WeightedCoeff.restrictIndicesCLM_apply (p := (2 : ℝ≥0∞)) w.toWeight (Coeff.parityEmbedding 0) q k
  simp only [Coeff.parityEmbedding_apply,add_zero] at ht
  exact ht

theorem norm_hillPeriodOneRestriction_le (w : SpectralWeight) (q : WeightedCoeff w.toWeight 2) :
    ‖hillPeriodOneRestriction w q‖≤‖q‖ :=
  WeightedCoeff.norm_restrictIndicesCLM_le _ _ q

theorem hillPeriodOneCoefficientMap_restriction (w : SpectralWeight) (q : WeightedCoeff w.toWeight 2) :
    hillPeriodOneCoefficientMap w (hillPeriodOneRestriction w q)=Coeff.parityProjection 0 (w.toCoeff q) := by
  ext k
  by_cases hk : k%2=0
  · have he : k=2*(k/2) := by omega
    rw [he]
    change w.toCoeff (hillPeriodOnePotential w (hillPeriodOneRestriction w q)) (2*(k/2))=_
    rw [SpectralWeight.toCoeff_apply,hillPeriodOnePotential_even,hillPeriodOneRestriction_apply,Coeff.parityProjection_apply]
    simp only [show (2*(k/2))%2=(0 : ℤ)%2 by omega,if_pos,SpectralWeight.toCoeff_apply]
  · have he : k=2*(k/2)+1 := by omega
    rw [he]
    change w.toCoeff (hillPeriodOnePotential w (hillPeriodOneRestriction w q)) (2*(k/2)+1)=_
    rw [SpectralWeight.toCoeff_apply,hillPeriodOnePotential_odd,Coeff.parityProjection_apply]
    simp only [show (2*(k/2)+1)%2≠(0 : ℤ)%2 by omega,if_false]

theorem hillPeriodOneCoefficientMap_restriction_even (w : SpectralWeight) (q : WeightedCoeff w.toWeight 2)
    (hq : w.toCoeff q∈Coeff.paritySubspace 0) :
    hillPeriodOneCoefficientMap w (hillPeriodOneRestriction w q)=w.toCoeff q := by
  rw [hillPeriodOneCoefficientMap_restriction]
  exact (Coeff.parityProjection_eq_self_iff 0 _).mpr hq

end NLS.KdV
