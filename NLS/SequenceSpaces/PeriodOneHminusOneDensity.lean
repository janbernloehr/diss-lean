import NLS.SequenceSpaces.PeriodOneMiuraShift
import NLS.SequenceSpaces.WeightedFiniteCoefficients

/-! # Density for gluing functions on complex H^-1 neighborhoods

The unit-period L2 inclusion has dense range. Continuous functions on
any open H^-1 set are determined by their values on that range, so local
spectral extensions agreeing on physical L2 inputs agree on overlaps.
-/
noncomputable section
set_option autoImplicit false
open Set
namespace NLS

theorem denseRange_periodOneL2Inclusion : DenseRange periodOneL2Inclusion := by
  have hsub : range (WeightedCoeff.ofFinsupp (Weight.sobolev (-1)) 2) ⊆
      range periodOneL2Inclusion := by
    rintro _ ⟨a,rfl⟩
    refine ⟨Coeff.ofFinsupp a,?_⟩
    apply Subtype.ext
    funext k
    rw [periodOneL2Inclusion_apply,Coeff.ofFinsupp_apply,WeightedCoeff.ofFinsupp_apply]
  intro q
  exact closure_mono hsub (WeightedCoeff.denseRange_ofFinsupp _ 2 (by simp) q)

theorem eqOn_of_eqOn_periodOneL2Inclusion
    {Y : Type*} [TopologicalSpace Y] [T2Space Y]
    {U : Set PeriodOneHminusOne} (hU : IsOpen U) {f g : PeriodOneHminusOne → Y}
    (hf : ContinuousOn f U) (hg : ContinuousOn g U)
    (he : ∀ a : Coeff 2, periodOneL2Inclusion a ∈ U →
      f (periodOneL2Inclusion a) = g (periodOneL2Inclusion a)) : EqOn f g U := by
  have hfg : EqOn f g (U ∩ range periodOneL2Inclusion) := by
    rintro _ ⟨ha,a,rfl⟩
    exact he a ha
  exact hfg.of_subset_closure hf hg inter_subset_left
    (fun q hq => hU.inter_closure ⟨hq,denseRange_periodOneL2Inclusion q⟩)

end NLS
