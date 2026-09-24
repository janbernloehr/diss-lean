import NLS.ComplexAnalysis.ConvexHolomorphicPrimitive

/-!
# Primitive cancellation on singular endpoint detours

When a primitive has the same relative boundary value at two
singular starting points, the integrals of two connectors and a
regular crossing telescope. The connectors need only be integrable
and smooth with interiors in the primitive's domain.
-/

noncomputable section
open Set Filter Topology Complex
open scoped unitInterval
namespace NLS.ComplexAnalysis

/-- Two integrable singular connectors and a regular crossing form a
curve-integrable detour with zero integral when the primitive has the
same boundary value at the two singular endpoints. -/
theorem curveIntegral_singular_detour_eq_zero_of_primitive_boundary
    (f F : ℂ → ℂ) (s : Set ℂ)
    (hF : ∀ z ∈ s, HasDerivAt F (f z) z)
    {a b c d : ℂ}
    (left : Path a b) (crossing : Path b c) (right : Path d c)
    (hleft : ContDiffOn ℝ 1 left.extend (Icc 0 1))
    (hcross : ContDiffOn ℝ 1 crossing.extend (Icc 0 1))
    (hright : ContDiffOn ℝ 1 right.extend (Icc 0 1))
    (hlefts : ∀ t ∈ Ioo (0:ℝ) 1, left.extend t ∈ s)
    (hcrosss : ∀ t ∈ Icc (0:ℝ) 1, crossing.extend t ∈ s)
    (hrights : ∀ t ∈ Ioo (0:ℝ) 1, right.extend t ∈ s)
    (hleftInt : CurveIntegrable (holomorphicOneForm f) left)
    (hcrossInt : CurveIntegrable (holomorphicOneForm f) crossing)
    (hrightInt : CurveIntegrable (holomorphicOneForm f) right)
    {A : ℂ}
    (hboundaryA : Tendsto F (𝓝[s] a) (𝓝 A))
    (hboundaryD : Tendsto F (𝓝[s] d) (𝓝 A)) :
    CurveIntegrable (holomorphicOneForm f)
      ((left.trans crossing).trans right.symm) ∧
    (∫ᶜ z in (left.trans crossing).trans right.symm,
      holomorphicOneForm f z) = 0 := by
  have hb : b ∈ s := by
    simpa only [Path.extend_zero] using hcrosss 0 (by norm_num)
  have hc : c ∈ s := by
    simpa only [Path.extend_one] using hcrosss 1 (by norm_num)
  have hleftVal := curveIntegral_eq_sub_of_primitive_boundary_start
    f F s hF left hleft hlefts hb hleftInt hboundaryA
  have hcrossVal := curveIntegral_eq_sub_of_primitive
    f F s hF crossing hcross hcrosss hcrossInt
  have hrightVal := curveIntegral_eq_sub_of_primitive_boundary_start
    f F s hF right hright hrights hc hrightInt hboundaryD
  constructor
  · exact (hleftInt.trans hcrossInt).trans hrightInt.symm
  · rw [curveIntegral_trans (hleftInt.trans hcrossInt) hrightInt.symm,
      curveIntegral_trans hleftInt hcrossInt, curveIntegral_symm,
      hleftVal,hcrossVal,hrightVal]
    ring

end NLS.ComplexAnalysis
