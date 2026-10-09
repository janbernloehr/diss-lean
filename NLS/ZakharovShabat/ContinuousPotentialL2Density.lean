import NLS.ZakharovShabat.ContinuousPotentialL2Class

/-! # Continuous potentials are dense in the original physical L2 space

Approximate both scalar Lebesgue classes by bounded continuous functions,
then restrict those functions to the unit interval. No endpoint matching or
periodicity is required, and the component-sum Hilbert norm is preserved.
-/
noncomputable section
open Set MeasureTheory Filter Topology
open scoped BoundedContinuousFunction
open NLS.LinearVolterra
namespace NLS.ZakharovShabat

/-- Every physical L2 pair can be approximated by actual continuous potentials. -/
theorem denseRange_continuousPotentialL2Class : DenseRange continuousPotentialL2Class := by
  let μ := volume.restrict (Ioc (0:ℝ) 1)
  let L := BoundedContinuousFunction.toLp 2 μ ℂ (E := ℂ)
  let e := WithLp.prodContinuousLinearEquiv 2 ℂ IntervalL2 IntervalL2
  have hL : DenseRange L := BoundedContinuousFunction.toLp_denseRange ℂ μ ℂ (by norm_num)
  have hd : DenseRange (fun fg : (ℝ →ᵇ ℂ) × (ℝ →ᵇ ℂ) => e.symm (L fg.1,L fg.2)) :=
    e.symm.surjective.denseRange.comp (hL.prodMap hL) e.symm.continuous
  refine hd.mono ?_
  rintro u ⟨⟨f,g⟩,rfl⟩
  let φ : Curve (ℂ × ℂ) := ⟨fun t => (f t,g t),
    (f.continuous.comp continuous_subtype_val).prodMk (g.continuous.comp continuous_subtype_val)⟩
  refine ⟨φ,?_⟩
  apply intervalL2Representative_injective
  have hf := BoundedContinuousFunction.coeFn_toLp 2 μ ℂ f
  have hg := BoundedContinuousFunction.coeFn_toLp 2 μ ℂ g
  filter_upwards [continuousPotentialL2Class_representative φ,hf,hg,
    ae_restrict_mem measurableSet_Ioc] with s hφ hfs hgs hs
  rw [hφ]
  change extend φ s = ((L f) s,(L g) s)
  rw [hfs,hgs]
  simp only [NLS.LinearVolterra.extend,projIcc_of_mem _ (Ioc_subset_Icc_self hs),φ,ContinuousMap.coe_mk]

/-- Arbitrarily accurate approximation, measured in the actual physical norm. -/
theorem exists_continuousPotential_L2_approximation (u : IntervalPairL2) (ε : ℝ) (hε : 0 < ε) :
    ∃ φ : Curve (ℂ × ℂ), dist u (continuousPotentialL2Class φ) < ε :=
  Metric.denseRange_iff.mp denseRange_continuousPotentialL2Class u ε hε

end NLS.ZakharovShabat
