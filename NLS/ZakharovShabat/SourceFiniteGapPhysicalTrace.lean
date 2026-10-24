import NLS.ZakharovShabat.ClassicalBoundaryFirstCoefficient
import NLS.ZakharovShabat.SourceFiniteGapBoundaryCoefficient
import NLS.ZakharovShabat.SourceFiniteGapSmoothRealization
import NLS.ZakharovShabat.ContinuousSourceBoundaryRealization
import Mathlib.Analysis.Calculus.Deriv.Slope

/-! # The physical finite-gap boundary trace

The exact finite root quotient and the classical Volterra asymptotics
identify the physical potential sum at zero. Its norm is bounded by the
sum of the actual open gap lengths. This is a trace bound, not yet a
properness or global uniqueness theorem.
-/
noncomputable section
open Set Complex Filter Topology NLS.Fourier NLS.LinearVolterra
open scoped ENNReal
namespace NLS.ZakharovShabat

/-- Differentiation of a normalized germ recovers its coefficient along the upper imaginary ray. -/
theorem tendsto_germ_first_coefficient_vertical {g : ℂ → ℂ} {c : ℂ}
    (hg : HasDerivAt g c 0) (h0 : g 0 = 1) :
    Tendsto (fun y : ℝ => ((y : ℂ)*I) * (g (((y : ℂ)*I)⁻¹)-1)) atTop (𝓝 c) := by
  have ht : Tendsto (fun y : ℝ => ((y : ℂ)*I)⁻¹) atTop (𝓝 0) := by
    have h := (Complex.continuous_ofReal.continuousAt.tendsto.comp
      (tendsto_inv_atTop_zero : Tendsto (fun y : ℝ => y⁻¹) atTop (𝓝 0))).mul_const I⁻¹
    simpa only [Function.comp_def,Complex.ofReal_inv,Complex.ofReal_zero,zero_mul,mul_zero,mul_inv_rev,mul_comm] using! h
  have ht' : Tendsto (fun y : ℝ => ((y : ℂ)*I)⁻¹) atTop (𝓝[≠] 0) := by
    apply tendsto_nhdsWithin_iff.mpr
    refine ⟨ht,?_⟩
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with y hy
    exact inv_ne_zero (mul_ne_zero (Complex.ofReal_ne_zero.mpr hy.ne') I_ne_zero)
  have h := hg.tendsto_slope.comp ht'
  simpa only [Function.comp_def,slope_def_field,sub_zero,h0,div_eq_mul_inv,inv_inv,mul_comm] using! h

/-- The actual finite-gap root trace equals minus the physical potential sum;
in particular that sum is bounded by the total length of the open gaps. -/
theorem exists_sourceFiniteGap_physical_boundary_trace
    (φ : realTypeSourceSubmodule 2)
    (hf : φ ∈ sourceFiniteGapLocus (by simp) (by norm_num)) :
    ∃ s : Finset ℤ,
      (∀ n : ℤ, n ∈ s ↔ canonicalPeriodicGap (by simp) (by norm_num)
        (periodOnePotential φ.val) (periodOnePotential_mem φ.val) n ≠ 0) ∧
      (∑ n ∈ s, (canonicalPeriodOneBoundaryRoots (by simp) (by norm_num) .neumann φ.val n -
        canonicalPeriodOneBoundaryRoots (by simp) (by norm_num) .dirichlet φ.val n)) =
        -((sourceFiniteGapPhysicalPair (by simp) (by norm_num) φ hf).1 0 +
          (sourceFiniteGapPhysicalPair (by simp) (by norm_num) φ hf).2 0) ∧
      ‖(sourceFiniteGapPhysicalPair (by simp) (by norm_num) φ hf).1 0 +
          (sourceFiniteGapPhysicalPair (by simp) (by norm_num) φ hf).2 0‖ ≤
        ∑ n ∈ s, ‖canonicalPeriodicGap (by simp) (by norm_num)
          (periodOnePotential φ.val) (periodOnePotential_mem φ.val) n‖ := by
  obtain ⟨s,g,hs,h0,hg,hbound,hquot⟩ :=
    exists_sourceFiniteGap_boundaryCharacteristic_germ (by simp) (by norm_num) φ hf
  let a : Coeff 1 := ⟨_,(sourceFiniteGap_memlp_one (by simp) (by norm_num) φ hf).1⟩
  let b : Coeff 1 := ⟨_,(sourceFiniteGap_memlp_one (by simp) (by norm_num) φ hf).2⟩
  let Φ := absoluteSourceCurve a b
  have hchar (θ : BoundaryCondition) (z : ℂ) :
      periodOneBoundaryCharacteristic (by simp) (by norm_num) θ φ.val z =
        classicalSeparatedCharacteristic θ Φ z :=
    periodOneBoundaryCharacteristic_eq_classical_of_continuous θ φ.val Φ
      (physicalBase_absoluteSourceCurve φ.val a b (fun _ => rfl) (fun _ => rfl)) z
  have hevent : (fun y : ℝ => ((y : ℂ)*I) * (g (((y : ℂ)*I)⁻¹)-1)) =ᶠ[atTop]
      (fun y : ℝ => ((y : ℂ)*I) *
        (classicalSeparatedCharacteristic .dirichlet Φ ((y : ℂ)*I) /
          classicalSeparatedCharacteristic .neumann Φ ((y : ℂ)*I)-1)) := by
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with y hy
    rw [hquot _ (by simpa using hy.ne'),hchar,hchar]
  have he := tendsto_nhds_unique (tendsto_germ_first_coefficient_vertical hg h0)
    ((tendsto_classicalBoundaryRatio_first_coefficient Φ).congr' hevent.symm)
  have hp : (Φ ⟨1,by norm_num⟩).2 = periodOneSynthesis b 0 := by
    change periodOneSynthesis b 1 = periodOneSynthesis b 0
    simpa only [zero_add] using periodOneSynthesis_periodic b 0
  rw [hp] at he
  change (∑ n ∈ s, (_ - _)) = -(periodOneSynthesis a 0+periodOneSynthesis b 0) at he
  refine ⟨s,hs,he,?_⟩
  rw [hg.deriv,he,norm_neg] at hbound
  exact hbound

end NLS.ZakharovShabat
