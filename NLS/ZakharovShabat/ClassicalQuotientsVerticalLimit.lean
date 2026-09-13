import NLS.ZakharovShabat.ClassicalProductQuotients
import NLS.ZakharovShabat.CanonicalProductsVerticalLimit
import NLS.ZakharovShabat.ClassicalHalfPlaneAsymptotics
import NLS.ComplexAnalysis.CommonNormalizationLimits

/-!
# Vertical limits determine bounded entire normalization factors

The common free normalization makes the filled classical/canonical quotients
tend to one. For a compatible continuous Hilbert potential they are entire,
so proving boundedness is now sufficient for the exact product identity.
-/

noncomputable section
open Set Complex Filter Topology MeasureTheory NLS.Fourier NLS.LinearVolterra NLS.ComplexAnalysis
namespace NLS.ZakharovShabat

theorem tendsto_classicalParityProductQuotient_upper {α : Type*} {l : Filter α}
    {y : α → ℝ} (hy : Tendsto y l atTop)
    (φ : PairSpace 2) (hφ : φ ∈ pairParitySubspace 0) (Φ : Curve (ℂ × ℂ))
    (r : ℤ) (hr : r = 0 ∨ r = 1) (x : ℝ) :
    Tendsto (fun i => classicalParityProductQuotient φ Φ r (verticalSpectralPoint x (y i)))
      l (𝓝 1) := by
  apply tendsto_filled_quotient_of_common_normalization
    (fun i => classicalDiscriminant Φ (verticalSpectralPoint x (y i))-2*wave r 1)
    (fun i => canonicalParityProduct (by simp) φ r (verticalSpectralPoint x (y i)))
    (fun i => freeDiscriminant (verticalSpectralPoint x (y i))-2*wave r 1)
  · apply tendsto_classicalDiscriminant_sub_div_free_upper
    simpa only [verticalSpectralPoint_im] using hy
  · exact tendsto_canonicalParity_div_free_vertical (tendsto_abs_atTop_atTop.comp hy)
      (by simp) (by norm_num) φ hφ r hr x
  · intro i hi
    exact classicalParityProductQuotient_eq_div φ hφ Φ r hr _ hi

theorem tendsto_classicalParityProductQuotient_lower {α : Type*} {l : Filter α}
    {y : α → ℝ} (hy : Tendsto y l atBot)
    (φ : PairSpace 2) (hφ : φ ∈ pairParitySubspace 0) (Φ : Curve (ℂ × ℂ))
    (r : ℤ) (hr : r = 0 ∨ r = 1) (x : ℝ) :
    Tendsto (fun i => classicalParityProductQuotient φ Φ r (verticalSpectralPoint x (y i)))
      l (𝓝 1) := by
  apply tendsto_filled_quotient_of_common_normalization
    (fun i => classicalDiscriminant Φ (verticalSpectralPoint x (y i))-2*wave r 1)
    (fun i => canonicalParityProduct (by simp) φ r (verticalSpectralPoint x (y i)))
    (fun i => freeDiscriminant (verticalSpectralPoint x (y i))-2*wave r 1)
  · apply tendsto_classicalDiscriminant_sub_div_free_lower
    simpa only [verticalSpectralPoint_im] using hy
  · exact tendsto_canonicalParity_div_free_vertical (tendsto_abs_atBot_atTop.comp hy)
      (by simp) (by norm_num) φ hφ r hr x
  · intro i hi
    exact classicalParityProductQuotient_eq_div φ hφ Φ r hr _ hi

theorem tendsto_classicalPeriodicProductQuotient_upper {α : Type*} {l : Filter α}
    {y : α → ℝ} (hy : Tendsto y l atTop)
    (φ : PairSpace 2) (hφ : φ ∈ pairParitySubspace 0) (Φ : Curve (ℂ × ℂ)) (x : ℝ) :
    Tendsto (fun i => classicalPeriodicProductQuotient φ Φ (verticalSpectralPoint x (y i)))
      l (𝓝 1) := by
  apply tendsto_filled_quotient_of_common_normalization
    (fun i => (classicalDiscriminant Φ (verticalSpectralPoint x (y i)))^2-4)
    (fun i => canonicalPeriodicProduct (by simp) φ (verticalSpectralPoint x (y i)))
    (fun i => (freeDiscriminant (verticalSpectralPoint x (y i)))^2-4)
  · apply tendsto_classicalDiscriminant_sq_div_free_upper
    simpa only [verticalSpectralPoint_im] using hy
  · exact tendsto_canonicalPeriodic_div_free_vertical (tendsto_abs_atTop_atTop.comp hy)
      (by simp) (by norm_num) φ hφ x
  · intro i hi
    exact classicalPeriodicProductQuotient_eq_div φ Φ _ hi

theorem tendsto_classicalPeriodicProductQuotient_lower {α : Type*} {l : Filter α}
    {y : α → ℝ} (hy : Tendsto y l atBot)
    (φ : PairSpace 2) (hφ : φ ∈ pairParitySubspace 0) (Φ : Curve (ℂ × ℂ)) (x : ℝ) :
    Tendsto (fun i => classicalPeriodicProductQuotient φ Φ (verticalSpectralPoint x (y i)))
      l (𝓝 1) := by
  apply tendsto_filled_quotient_of_common_normalization
    (fun i => (classicalDiscriminant Φ (verticalSpectralPoint x (y i)))^2-4)
    (fun i => canonicalPeriodicProduct (by simp) φ (verticalSpectralPoint x (y i)))
    (fun i => (freeDiscriminant (verticalSpectralPoint x (y i)))^2-4)
  · apply tendsto_classicalDiscriminant_sq_div_free_lower
    simpa only [verticalSpectralPoint_im] using hy
  · exact tendsto_canonicalPeriodic_div_free_vertical (tendsto_abs_atBot_atTop.comp hy)
      (by simp) (by norm_num) φ hφ x
  · intro i hi
    exact classicalPeriodicProductQuotient_eq_div φ Φ _ hi

/-- The parity identity now requires only boundedness of the entire factor. -/
theorem canonicalParity_eq_classical_of_bounded_quotient
    (φ : PairSpace 2) (hφ : φ ∈ pairParitySubspace 0)
    (Φ : Curve (ℂ × ℂ)) (hΦ : physicalBase φ =ᵐ[volume.restrict (Ioc 0 1)] extend Φ)
    (r : ℤ) (hr : r = 0 ∨ r = 1)
    (hb : Bornology.IsBounded (range (classicalParityProductQuotient φ Φ r))) (z : ℂ) :
    canonicalParityProduct (by simp) φ r z = classicalDiscriminant Φ z-2*wave r 1 := by
  have ha := analyticOnNhd_classicalParityProductQuotient φ hφ Φ hΦ r hr
  have hc := eq_const_of_bounded_entire_of_tendsto_path
    (fun w => (ha w (mem_univ _)).differentiableAt) hb
    (fun y : ℝ => verticalSpectralPoint 0 y) 1
    (tendsto_classicalParityProductQuotient_upper tendsto_id φ hφ Φ r hr 0)
  simpa only [hc z, one_mul] using classicalParityProductQuotient_mul φ hφ Φ hΦ r hr z

/-- The full identity likewise reduces to boundedness of its entire factor. -/
theorem canonicalPeriodic_eq_classical_of_bounded_quotient
    (φ : PairSpace 2) (hφ : φ ∈ pairParitySubspace 0)
    (Φ : Curve (ℂ × ℂ)) (hΦ : physicalBase φ =ᵐ[volume.restrict (Ioc 0 1)] extend Φ)
    (hb : Bornology.IsBounded (range (classicalPeriodicProductQuotient φ Φ))) (z : ℂ) :
    canonicalPeriodicProduct (by simp) φ z = (classicalDiscriminant Φ z)^2-4 := by
  have ha := analyticOnNhd_classicalPeriodicProductQuotient φ hφ Φ hΦ
  have hc := eq_const_of_bounded_entire_of_tendsto_path
    (fun w => (ha w (mem_univ _)).differentiableAt) hb
    (fun y : ℝ => verticalSpectralPoint 0 y) 1
    (tendsto_classicalPeriodicProductQuotient_upper tendsto_id φ hφ Φ 0)
  simpa only [hc z, one_mul] using classicalPeriodicProductQuotient_mul φ hφ Φ hΦ z

end NLS.ZakharovShabat
