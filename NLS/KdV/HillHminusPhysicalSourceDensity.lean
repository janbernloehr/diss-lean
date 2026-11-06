import NLS.KdV.HillHminusOriginalSourceAdapter
import NLS.KdV.HillUnitRealSourceUnembed

/-! # Original physical real L2 sources are dense in real Hminus1 -/
noncomputable section
set_option autoImplicit false
open Set Complex
namespace NLS.KdV

theorem periodOneRealL2Inclusion_mem_range_physical (u : PeriodOneRealL2) :
    periodOneRealL2Inclusion u ∈ Set.range hillPhysicalHminusEmbedding := by
  let p := hillRealWeightedEmbedding SpectralWeight.one
    (hillUnitRealSourceLift u.val ((periodOneL2Conjugation_fixed_iff _).mpr u.property))
  refine ⟨p,?_⟩
  apply Subtype.ext
  apply Subtype.ext
  funext k
  rw [hillPhysicalHminusEmbedding_apply]
  have he : SpectralWeight.one.toCoeff p.val = Coeff.periodDouble u.val := by
    rw [hillRealWeightedEmbedding_toCoeff,hillUnitRealSourceLift_toCoeff]
  change SpectralWeight.one.toCoeff p.val (2*k) = (periodOneL2Inclusion u.val).val k
  rw [periodOneL2Inclusion_apply,he,Coeff.periodDouble_even]

theorem denseRange_hillPhysicalHminusEmbedding : DenseRange hillPhysicalHminusEmbedding := by
  have hsub : Set.range periodOneRealL2Inclusion ⊆ Set.range hillPhysicalHminusEmbedding := by
    rintro _ ⟨u,rfl⟩
    exact periodOneRealL2Inclusion_mem_range_physical u
  intro q
  exact closure_mono hsub (denseRange_periodOneRealL2Inclusion q)

end NLS.KdV
