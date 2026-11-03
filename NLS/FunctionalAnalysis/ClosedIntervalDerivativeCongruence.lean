import NLS.FunctionalAnalysis.ComplexAbsoluteContinuity

/-! # Closed-interval values preserve the almost-everywhere derivative

The assertion concerns the original open interior almost everywhere. No
regularity or equality outside the closed interval is imposed.
-/
noncomputable section
open Set MeasureTheory Filter Topology
namespace NLS.FunctionalAnalysis

/-- Functions agreeing on the closed interval have the same prescribed
almost-everywhere derivative there, irrespective of their values outside it. -/
theorem ae_hasDerivAt_Ioc_congr_of_eqOn_Icc
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {a b : ℝ} {f g v : ℝ → E} (hfg : EqOn f g (Icc a b))
    (hd : ∀ᵐ x ∂volume.restrict (Ioc a b), HasDerivAt f (v x) x) :
    ∀ᵐ x ∂volume.restrict (Ioc a b), HasDerivAt g (v x) x := by
  have hne : ∀ᵐ x : ℝ ∂volume, x ≠ b := by simp [ae_iff]
  filter_upwards [hd, ae_restrict_mem measurableSet_Ioc, ae_restrict_of_ae hne]
    with x hx hxi hxb
  apply hx.congr_of_eventuallyEq
  filter_upwards [Ioo_mem_nhds hxi.1 (lt_of_le_of_ne hxi.2 hxb)] with y hy
  exact (hfg ⟨hy.1.le,hy.2.le⟩).symm

end NLS.FunctionalAnalysis
