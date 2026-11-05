import NLS.Articles.KdVPseudomeasures.MainTheorem14

/-! The SAME actual native map is a global homeomorphism in the
original physical rough Banach norms, with a real analytic inverse. -/
noncomputable section
open Set Filter Topology NLS.KdV
namespace NLS.Articles.KdVPseudomeasures

theorem bijective_hillRealSignedMap : Function.Bijective hillRealSignedMap :=
  ⟨injective_hillRealSignedMap,surjective_hillRealSignedMap⟩

def hillNativeHomeomorph : HillRealMeanZeroSource ≃ₜ HillRealSignedTarget :=
  hillPhysicalNativeMap_isLocalHomeomorph.toHomeomorphOfBijective bijective_hillRealSignedMap

theorem hillNativeHomeomorph_apply (q : HillRealMeanZeroSource) :
    hillNativeHomeomorph q=hillRealSignedMap q := rfl

theorem analyticAt_hillNativeHomeomorph_symm (z : HillRealSignedTarget) :
    AnalyticAt ℝ hillNativeHomeomorph.symm z := by
  let q := hillNativeHomeomorph.symm z
  have hq : hillRealSignedMap q=z := hillNativeHomeomorph.apply_symm_apply z
  obtain ⟨g,hg,_,_,hr,_⟩ := hillPhysicalNativeMap_localInverse q
  rw [hq] at hg hr
  apply hg.congr
  filter_upwards [hr] with y hy
  apply injective_hillRealSignedMap
  exact hy.trans (hillNativeHomeomorph.apply_symm_apply y).symm

end NLS.Articles.KdVPseudomeasures
