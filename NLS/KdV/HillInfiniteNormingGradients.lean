import NLS.KdV.HillUniformNormingGradients
import NLS.KdV.HillFiniteNormingGradients
import NLS.FunctionalAnalysis.UnitComplexCurvePrimitive

noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology MeasureTheory
open NLS.ComplexAnalysis NLS.LinearVolterra NLS.FunctionalAnalysis NLS.ZakharovShabat
open scoped ENNReal ComplexConjugate Classical

namespace NLS.KdV



/-- The actual infinite physical norming-gradient combination. -/
def hillInfiniteNormingGradient (q : RealPeriodOneHillPotential) (c : ℕ → ℂ) : Curve ℂ :=
  ∑' j : ℕ,c j • hillLogNormingGradientCurve q (j+1) (by omega)

/-- The corresponding infinite actual spatial derivative curve. -/
def hillInfiniteNormingGradientSpatial (q : RealPeriodOneHillPotential) (c : ℕ → ℂ) : Curve ℂ :=
  ∑' j : ℕ,c j • hillLogNormingGradientSpatialCurve q (j+1) (by omega)

variable
    (h0q : SpectralWeight.one.toCoeff (0 : WeightedCoeff SpectralWeight.one.toWeight 2)∈Coeff.paritySubspace 0)
    (h0r : IsRealHillPotential (SpectralWeight.one.toCoeff (0 : WeightedCoeff SpectralWeight.one.toWeight 2)))
include h0q h0r

/-- Absolutely summable scalar coefficients give absolutely convergent
physical norming-gradient and spatial-derivative curves. -/
theorem hillNormingGradientSeries_norm_summable
    (q : RealPeriodOneHillPotential) (c : ℕ → ℂ) (hc : Summable (fun j => ‖c j‖)) :
    Summable (fun j : ℕ => ‖c j • hillLogNormingGradientCurve q (j+1) (by omega)‖) ∧
    Summable (fun j : ℕ => ‖c j • hillLogNormingGradientSpatialCurve q (j+1) (by omega)‖) := by
  obtain ⟨N,hN,hbound⟩ := exists_hillLogNormingGradient_uniform_high_bounds h0q h0r
    ‖SpectralWeight.one.toCoeff q.val‖
  constructor
  · apply (hc.mul_right 132).of_norm_bounded_eventually_nat
    filter_upwards [eventually_ge_atTop N] with j hj
    have hh := (hbound q le_rfl (j+1) (by omega)).1
    have hjR : (1 : ℝ)≤((j+1 : ℕ) : ℝ) := by exact_mod_cast (show 1≤j+1 by omega)
    have hg : ‖hillLogNormingGradientCurve q (j+1) (by omega)‖≤132 :=
      hh.trans ((div_le_self (by norm_num) hjR))
    rw [norm_norm,norm_smul]
    exact mul_le_mul_of_nonneg_left hg (norm_nonneg _)
  · apply (hc.mul_right 264).of_norm_bounded_eventually_nat
    filter_upwards [eventually_ge_atTop N] with j hj
    have hh := (hbound q le_rfl (j+1) (by omega)).2
    rw [norm_norm,norm_smul]
    exact mul_le_mul_of_nonneg_left hh (norm_nonneg _)

omit h0q h0r in
private theorem norming_gradient_eq_primitive (q : RealPeriodOneHillPotential) (j : ℕ) :
    hillLogNormingGradientCurve q (j+1) (by omega)=
      unitComplexCurvePrimitive (hillLogNormingGradientSpatialCurve q (j+1) (by omega)) := by
  have hh := curve_eq_constant_add_unitComplexCurvePrimitive
    (hillLogNormingGradientCurve q (j+1) (by omega))
    (hillLogNormingGradientSpatialCurve q (j+1) (by omega))
    (absolutelyContinuousOnInterval_hillLogNormingGradientCurve q (j+1) (by omega))
    (ae_hasDerivAt_hillLogNormingGradientCurve q (j+1) (by omega))
  simpa only [(hillLogNormingGradientCurve_endpoints q (j+1) (by omega)).1,
    ContinuousMap.const_zero,zero_add] using hh

/-- The genuine spatial derivative graph is closed under these infinite
cotangent sums, using the bounded physical primitive operator. -/
theorem hillInfiniteNormingGradient_eq_primitive
    (q : RealPeriodOneHillPotential) (c : ℕ → ℂ) (hc : Summable (fun j => ‖c j‖)) :
    hillInfiniteNormingGradient q c=unitComplexCurvePrimitive (hillInfiniteNormingGradientSpatial q c) := by
  have hs := (hillNormingGradientSeries_norm_summable h0q h0r q c hc).2.of_norm
  calc
    _ = ∑' j : ℕ,unitComplexCurvePrimitive (c j • hillLogNormingGradientSpatialCurve q (j+1) (by omega)) := by
      apply tsum_congr
      intro j
      rw [map_smul,←norming_gradient_eq_primitive]
    _ = _ := (unitComplexCurvePrimitive.map_tsum hs).symm

/-- The actual a.e. spatial derivative of the full infinite cotangent. -/
theorem ae_hasDerivAt_hillInfiniteNormingGradient
    (q : RealPeriodOneHillPotential) (c : ℕ → ℂ) (hc : Summable (fun j => ‖c j‖)) :
    ∀ᵐ x ∂volume.restrict (Ioc (0 : ℝ) 1),
      HasDerivAt (extend (hillInfiniteNormingGradient q c))
        (extend (hillInfiniteNormingGradientSpatial q c) x) x := by
  rw [hillInfiniteNormingGradient_eq_primitive h0q h0r q c hc]
  exact ae_hasDerivAt_unitComplexCurvePrimitive _

/-- The full absolutely convergent physical norming combination belongs
to the genuine Gardner cotangent domain. -/
theorem hillInfiniteNormingGradient_H1
    (q : RealPeriodOneHillPotential) (c : ℕ → ℂ) (hc : Summable (fun j => ‖c j‖)) :
    AbsolutelyContinuousOnInterval (extend (hillInfiniteNormingGradient q c)) 0 1 ∧
      MemLp (extend (hillInfiniteNormingGradient q c)) 2 (volume.restrict (Ioc (0 : ℝ) 1)) ∧
      MemLp (deriv (extend (hillInfiniteNormingGradient q c))) 2 (volume.restrict (Ioc (0 : ℝ) 1)) := by
  have hmem (f : Curve ℂ) : MemLp (extend f) 2 (volume.restrict (Ioc (0 : ℝ) 1)) :=
    (memLp_two_iff_integrable_sq_norm (continuous_extend f).aestronglyMeasurable).mpr
      (((continuous_extend f).norm.pow 2).intervalIntegrable 0 1).1
  refine ⟨?_,hmem _,?_⟩
  · rw [hillInfiniteNormingGradient_eq_primitive h0q h0r q c hc]
    exact absolutelyContinuousOnInterval_unitComplexCurvePrimitive _
  · apply (hmem (hillInfiniteNormingGradientSpatial q c)).ae_eq
    filter_upwards [ae_hasDerivAt_hillInfiniteNormingGradient h0q h0r q c hc] with x hx
    exact hx.deriv.symm

end NLS.KdV
