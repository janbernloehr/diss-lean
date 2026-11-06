import NLS.KdV.HillPrescribedCharacteristicAngle

noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology MeasureTheory
open NLS.ComplexAnalysis NLS.ZakharovShabat
open scoped ENNReal ComplexConjugate Classical

namespace NLS.KdV



/-- At a periodic Dirichlet terminal, the actual sheeted angle can be chosen
at zero or pi, with the exact physical sine and cosine terminal equations. -/
theorem exists_hillDirichlet_endpoint_base_angle
    (q : RealPeriodOneHillPotential) (k : ℕ) (hk : 1≤k)
    (hlog : hillDirichletLogMultiplier q.val q.property.1 q.property.2 k hk=0) :
    ∃ e : ℂ, (e=0 ∨ e=(Real.pi : ℂ)) ∧
      cosineGapPoint (hillRealGapCenter q.val q.property.1 q.property.2 k)
        (hillRealGapHalfLength q.val q.property.1 q.property.2 k) e=
        (hillDirichletEnergy q.val q.property.1 q.property.2 k hk : ℂ) ∧
      Complex.sin e=hillDirichletGapSine q.val q.property.1 q.property.2 k hk := by
  have hsheet : hillDirichletSheetRoot (SpectralWeight.one.toCoeff q.val)
      (hillDirichletEnergy q.val q.property.1 q.property.2 k hk)=0 := by
    rw [hillDirichletSheetRoot_at_dirichlet_eq_norming,hlog,Real.sinh_zero,mul_zero,ofReal_zero]
  have hsin : hillDirichletGapSine q.val q.property.1 q.property.2 k hk=0 := by
    rw [hillDirichletGapSine,hsheet,mul_zero,zero_div]
  rcases (hillDirichletLogMultiplier_eq_zero_iff_endpoint q.val q.property.1 q.property.2 k hk).mp hlog with hl | hu
  · refine ⟨(Real.pi : ℂ),Or.inr rfl,?_,?_⟩
    · rw [hl]
      simp only [cosineGapPoint,Complex.cos_pi,mul_neg_one]
      change ((hillRealGapCenter q.val q.property.1 q.property.2 k : ℝ) : ℂ)-
        (hillRealGapHalfLength q.val q.property.1 q.property.2 k : ℝ)=_
      rw [←ofReal_sub]
      congr 1
      dsimp only [hillRealGapCenter,hillRealGapHalfLength]
      ring
    · rw [Complex.sin_pi,hsin]
  · refine ⟨0,Or.inl rfl,?_,?_⟩
    · rw [hu]
      simp only [cosineGapPoint,Complex.cos_zero,mul_one]
      rw [←ofReal_add]
      congr 1
      dsimp only [hillRealGapCenter,hillRealGapHalfLength]
      ring
    · rw [Complex.sin_zero,hsin]

end NLS.KdV
