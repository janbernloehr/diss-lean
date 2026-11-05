import NLS.KdV.HillLogNormingGardnerBrackets
import NLS.FunctionalAnalysis.UnitComplexCurvePairing

noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology MeasureTheory
open NLS.ComplexAnalysis NLS.ZakharovShabat NLS.FunctionalAnalysis NLS.LinearVolterra
open scoped ENNReal ComplexConjugate Classical

namespace NLS.KdV



/-- A finite genuine physical log-norming cotangent combination. -/
def hillFiniteNormingGradient (q : RealPeriodOneHillPotential) (s : Finset ℕ) (c : ℕ → ℂ) : Curve ℂ :=
  ∑ j∈s,c j • hillLogNormingGradientCurve q (j+1) (by omega)

private theorem extend_curve_sum_smul (s : Finset ℕ) (c : ℕ → ℂ) (F : ℕ → Curve ℂ) :
    NLS.LinearVolterra.extend (∑ j∈s,c j • F j)=
      (fun x : ℝ => ∑ j∈s,c j*NLS.LinearVolterra.extend (F j) x) := by
  funext x
  change (∑ j∈s,c j • F j) (projIcc (0 : ℝ) 1 (by norm_num) x)=_
  simp only [ContinuousMap.sum_apply,ContinuousMap.smul_apply,smul_eq_mul]
  rfl

private theorem finite_norming_ac (q : RealPeriodOneHillPotential) (s : Finset ℕ) (c : ℕ → ℂ) :
    AbsolutelyContinuousOnInterval (fun x : ℝ =>
      ∑ j∈s,c j*NLS.LinearVolterra.extend (hillLogNormingGradientCurve q (j+1) (by omega)) x) 0 1 := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    have hz := (absolutelyContinuousOnInterval_hillLogNormingGradientCurve q 1 (by omega)).const_smul (0 : ℂ)
    simpa only [Finset.sum_empty,zero_smul] using hz
  | @insert i s hi ih =>
    have hh := ((absolutelyContinuousOnInterval_hillLogNormingGradientCurve q (i+1) (by omega)).const_smul (c i)).add ih
    convert! hh using 1
    funext x
    exact Finset.sum_insert hi

/-- The actual spatial derivative of every finite norming cotangent sum. -/
theorem ae_hasDerivAt_hillFiniteNormingGradient
    (q : RealPeriodOneHillPotential) (s : Finset ℕ) (c : ℕ → ℂ) :
    ∀ᵐ x ∂volume.restrict (Ioc (0 : ℝ) 1),
      HasDerivAt (NLS.LinearVolterra.extend (hillFiniteNormingGradient q s c))
        ((NLS.LinearVolterra.extend (∑ j∈s,c j • hillLogNormingGradientSpatialCurve q (j+1) (by omega))) x) x := by
  have hd : ∀ᵐ x ∂volume.restrict (Ioc (0 : ℝ) 1), ∀ j : ℕ,
      HasDerivAt (NLS.LinearVolterra.extend (hillLogNormingGradientCurve q (j+1) (by omega)))
        (NLS.LinearVolterra.extend (hillLogNormingGradientSpatialCurve q (j+1) (by omega)) x) x :=
    ae_all_iff.mpr (fun j => ae_hasDerivAt_hillLogNormingGradientCurve q (j+1) (by omega))
  filter_upwards [hd] with x hx
  have hs := HasDerivAt.fun_sum (u := s) (fun j _ => (hx j).const_mul (c j))
  simpa only [hillFiniteNormingGradient,extend_curve_sum_smul] using hs

/-- Finite norming cotangent combinations have genuine physical H1 regularity. -/
theorem hillFiniteNormingGradient_H1
    (q : RealPeriodOneHillPotential) (s : Finset ℕ) (c : ℕ → ℂ) :
    AbsolutelyContinuousOnInterval (NLS.LinearVolterra.extend (hillFiniteNormingGradient q s c)) 0 1 ∧
      MemLp (NLS.LinearVolterra.extend (hillFiniteNormingGradient q s c)) 2 (volume.restrict (Ioc (0 : ℝ) 1)) ∧
      MemLp (deriv (NLS.LinearVolterra.extend (hillFiniteNormingGradient q s c))) 2 (volume.restrict (Ioc (0 : ℝ) 1)) := by
  have hmem (f : Curve ℂ) : MemLp (NLS.LinearVolterra.extend f) 2 (volume.restrict (Ioc (0 : ℝ) 1)) :=
    (memLp_two_iff_integrable_sq_norm (continuous_extend f).aestronglyMeasurable).mpr
      (((continuous_extend f).norm.pow 2).intervalIntegrable 0 1).1
  refine ⟨?_,hmem _,?_⟩
  · rw [hillFiniteNormingGradient,extend_curve_sum_smul]
    exact finite_norming_ac q s c
  · apply (hmem (∑ j∈s,c j • hillLogNormingGradientSpatialCurve q (j+1) (by omega))).ae_eq
    filter_upwards [ae_hasDerivAt_hillFiniteNormingGradient q s c] with x hx
    exact hx.deriv.symm

private theorem norming_spatial_pairing_zero (q : RealPeriodOneHillPotential) (i j : ℕ) :
    unitComplexCurvePairing (hillLogNormingGradientCurve q (i+1) (by omega))
      (hillLogNormingGradientSpatialCurve q (j+1) (by omega))=0 := by
  have he : unitComplexCurvePairing (hillLogNormingGradientCurve q (i+1) (by omega))
      (hillLogNormingGradientSpatialCurve q (j+1) (by omega))=
      hillLogNormingGardnerBracket q (i+1) (j+1) (by omega) (by omega) := by
    rw [unitComplexCurvePairing_apply,hillLogNormingGardnerBracket]
    apply intervalIntegral.integral_congr_ae_restrict
    rw [uIoc_of_le (by norm_num : (0 : ℝ)≤1)]
    filter_upwards [ae_hasDerivAt_hillLogNormingGradientCurve q (j+1) (by omega)] with x hx
    rw [hx.deriv]
    rfl
  exact he.trans (hillLogNormingGardnerBracket_eq_zero q (i+1) (j+1) (by omega) (by omega))

/-- Every two finite physical norming cotangent combinations commute under the
genuine Gardner derivative bracket. -/
theorem hillFiniteNormingGradient_GardnerBracket_eq_zero
    (q : RealPeriodOneHillPotential) (s t : Finset ℕ) (c d : ℕ → ℂ) :
    (∫ x in (0 : ℝ)..1,NLS.LinearVolterra.extend (hillFiniteNormingGradient q s c) x*
      deriv (NLS.LinearVolterra.extend (hillFiniteNormingGradient q t d)) x)=0 := by
  have he : (∫ x in (0 : ℝ)..1,NLS.LinearVolterra.extend (hillFiniteNormingGradient q s c) x*
      deriv (NLS.LinearVolterra.extend (hillFiniteNormingGradient q t d)) x)=
      unitComplexCurvePairing (hillFiniteNormingGradient q s c)
        (∑ j∈t,d j • hillLogNormingGradientSpatialCurve q (j+1) (by omega)) := by
    rw [unitComplexCurvePairing_apply]
    apply intervalIntegral.integral_congr_ae_restrict
    rw [uIoc_of_le (by norm_num : (0 : ℝ)≤1)]
    filter_upwards [ae_hasDerivAt_hillFiniteNormingGradient q t d] with x hx
    rw [hx.deriv]
    rfl
  rw [he,hillFiniteNormingGradient]
  simp only [map_sum,map_smul,sum_apply,smul_apply,smul_eq_mul,norming_spatial_pairing_zero,
    mul_zero,Finset.sum_const_zero]

end NLS.KdV
