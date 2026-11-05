import NLS.Articles.KdVPseudomeasures.OriginalHillNativeZeroFiber
import NLS.Articles.KdVPseudomeasures.OriginalHillL2Properness
import NLS.Articles.KdVPseudomeasures.OriginalHillL2LocalHomeomorph
import NLS.FunctionalAnalysis.ClosedLocalHomeomorph
import Mathlib.Analysis.Normed.Module.Connected

/-! The ACTUAL KdV native map is a global real-analytic homeomorphism on
the genuine mean-zero physical L2 and signed-positive-half Banach models.
This does not assert native Hminus surjectivity. -/
noncomputable section
open Set Filter Topology NLS.KdV
namespace NLS.Articles.KdVPseudomeasures

theorem hillL2NativeMap_eq_zero_iff (u : HillRealL2BanachSource) : hillL2NativeMap u=0 ↔ u=0 := by
  constructor
  · intro hu
    apply hillL2SourceInclusion_injective
    rw [map_zero]
    apply (hillRealSignedMap_eq_zero_iff _).mp
    rw [← hillL2NativeMap_inclusion,hu,map_zero]
  · rintro rfl
    exact hillL2NativeMap_zero

theorem bijective_hillL2NativeMap : Function.Bijective hillL2NativeMap := by
  apply NLS.FunctionalAnalysis.bijective_of_closed_localHomeomorph_singleton_fiber
    hillL2NativeMap isLocalHomeomorph_hillL2NativeMap isClosedMap_hillL2NativeMap 0
  intro u hu
  exact (hillL2NativeMap_eq_zero_iff u).mp (hu.trans hillL2NativeMap_zero)

def hillL2NativeHomeomorph : HillRealL2BanachSource ≃ₜ HillRealSignedHalfTarget :=
  isLocalHomeomorph_hillL2NativeMap.toHomeomorphOfBijective bijective_hillL2NativeMap

theorem hillL2NativeHomeomorph_apply (u : HillRealL2BanachSource) :
    hillL2NativeHomeomorph u=hillL2NativeMap u := rfl

theorem analyticAt_hillL2NativeHomeomorph_symm (z : HillRealSignedHalfTarget) :
    AnalyticAt ℝ hillL2NativeHomeomorph.symm z := by
  let u := hillL2NativeHomeomorph.symm z
  have hu : hillL2NativeMap u=z := hillL2NativeHomeomorph.apply_symm_apply z
  obtain ⟨g,hg,_,_,hr⟩ := exists_hillL2NativeMap_localInverse u
  rw [hu] at hg hr
  apply hg.congr
  filter_upwards [hr] with y hy
  apply bijective_hillL2NativeMap.1
  exact hy.trans (hillL2NativeHomeomorph.apply_symm_apply y).symm

theorem norm_sq_hillL2NativeHomeomorph_symm (z : HillRealSignedHalfTarget) :
    ‖hillL2NativeHomeomorph.symm z‖^2=2*Real.pi*‖z‖^2 := by
  have h := norm_sq_hillL2NativeMap (hillL2NativeHomeomorph.symm z)
  rw [show hillL2NativeMap (hillL2NativeHomeomorph.symm z)=z from hillL2NativeHomeomorph.apply_symm_apply z] at h
  exact h

end NLS.Articles.KdVPseudomeasures
