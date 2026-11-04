import NLS.KdV.ClassicalHillVariationWronskian

/-! Actual potential-variation Green kernels at EVERY complex potential
and energy, with the original unit initial columns and no division by a
spectral gap, Dirichlet value, or energy. -/
noncomputable section
open Set Complex MeasureTheory NLS.LinearVolterra
namespace NLS.KdV

theorem classicalHillPotentialVariation_kernels (q h : Curve ℂ) (μ : ℂ) (v : ℂ × ℂ)
    (t : Icc (0:ℝ) 1) :
    (classicalHillPotentialVariation q h μ v t).1=
      (classicalHillFlow q μ (0,1) t).1*
        (∫ s in (0:ℝ)..t.val, extend h s*(classicalHillFlow q μ (1,0) s).1*(classicalHillFlow q μ v s).1)-
      (classicalHillFlow q μ (1,0) t).1*
        (∫ s in (0:ℝ)..t.val, extend h s*(classicalHillFlow q μ (0,1) s).1*(classicalHillFlow q μ v s).1) ∧
    (classicalHillPotentialVariation q h μ v t).2=
      (classicalHillFlow q μ (0,1) t).2*
        (∫ s in (0:ℝ)..t.val, extend h s*(classicalHillFlow q μ (1,0) s).1*(classicalHillFlow q μ v s).1)-
      (classicalHillFlow q μ (1,0) t).2*
        (∫ s in (0:ℝ)..t.val, extend h s*(classicalHillFlow q μ (0,1) s).1*(classicalHillFlow q μ v s).1) := by
  have hC := classicalHillVariationWronskian_integral q h μ (1,0) v t
  have hS := classicalHillVariationWronskian_integral q h μ (0,1) v t
  have hdet := classicalHillFundamental_wronskian q μ t
  rw [hC,hS]
  dsimp only [classicalHillVariationWronskian]
  constructor
  · linear_combination -(classicalHillPotentialVariation q h μ v t).1*hdet
  · linear_combination -(classicalHillPotentialVariation q h μ v t).2*hdet

end NLS.KdV
