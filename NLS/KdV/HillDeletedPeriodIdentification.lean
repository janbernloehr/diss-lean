import NLS.KdV.HillUniformComplexPeriodRootBounds
import NLS.KdV.HillComplexSupportedPeriodMap
import NLS.KdV.HillHighIntrinsicPeriodComparison

noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology
open NLS.ComplexAnalysis NLS.ZakharovShabat
open scoped ENNReal Classical

namespace NLS.KdV



variable
    (h0q : SpectralWeight.one.toCoeff (0 : WeightedCoeff SpectralWeight.one.toWeight 2)∈Coeff.paritySubspace 0)
    (h0r : IsRealHillPotential (SpectralWeight.one.toCoeff (0 : WeightedCoeff SpectralWeight.one.toWeight 2)))

/-- The common-chart map is definitionally the existing original supported
period map used by the physical normalization interfaces. -/
theorem hillComplexFreeSupportedPeriodMap_eq_original (n : ℕ) :
    hillComplexFreeSupportedPeriodMap h0q h0r n=hillComplexSupportedPeriodMap h0q h0r n := rfl

/-- Deleting the unused own-root coordinate preserves the literal
original entire numerator, at every energy. -/
theorem hillAbelianHilbertPsi_positiveDeletedProjection (n : ℕ) (E : ℂ) (a : Coeff 2) :
    hillAbelianHilbertPsi n (E,Coeff.positiveDeletedProjection 2 (n : ℤ) a)=hillAbelianHilbertPsi n (E,a) := by
  rw [hillAbelianHilbertPsi,hillAbelianHilbertPsi]
  congr 1
  rw [hillAbelianHilbertProduct_eq_tprod,hillAbelianHilbertProduct_eq_tprod]
  apply tprod_congr
  intro k
  simp only [hillAbelianComplexNumeratorFactor]
  by_cases hkn : k+1=n
  · rw [if_pos hkn,if_pos hkn]
  · rw [if_neg hkn,if_neg hkn,Coeff.positiveDeletedProjection_apply,
      if_pos (show (0 : ℤ)<((k+1 : ℕ) : ℤ) ∧ ((k+1 : ℕ) : ℤ)≠n by constructor <;> omega)]

theorem hillAbelianHilbertPeriod_positiveDeletedProjection
    (q : WeightedCoeff SpectralWeight.one.toWeight 2)
    (hq : SpectralWeight.one.toCoeff q∈Coeff.paritySubspace 0)
    (hr : IsRealHillPotential (SpectralWeight.one.toCoeff q)) (n k : ℕ) (a : Coeff 2) :
    hillAbelianHilbertPeriod q hq hr n k (Coeff.positiveDeletedProjection 2 (n : ℤ) a)=
      hillAbelianHilbertPeriod q hq hr n k a := by
  unfold hillAbelianHilbertPeriod
  simp_rw [hillAbelianHilbertPsi_positiveDeletedProjection]

/-- The verified common free-contour control is exactly cutoff-one tail
control, so the existing physical period comparison applies to every gap. -/
theorem hillAbelianComplexPeriod_near_free_eq_physical (ε D : ℝ)
    (hc : HillComplexPeriodControl h0q h0r ε D)
    (q : WeightedCoeff SpectralWeight.one.toWeight 2)
    (hq : SpectralWeight.one.toCoeff q∈Coeff.paritySubspace 0)
    (hr : IsRealHillPotential (SpectralWeight.one.toCoeff q))
    (hp : ‖SpectralWeight.one.toCoeff q‖≤ε) (n k : ℕ) (hk : 1≤k) (a : Coeff 2) :
    hillAbelianComplexPeriod 0 h0q h0r n k (a,SpectralWeight.one.toCoeff q)=
      hillAbelianHilbertPeriod q hq hr n k a := by
  have hcTail : HillComplexTailPeriodControl h0q h0r 1 ε D := hc
  exact hillHighAbelianComplexPeriod_eq_intrinsic_physical h0q h0r 1 (by norm_num) ε D hcTail q hq hr hp n k hk a

end NLS.KdV
