import NLS.Articles.KdVPseudomeasures.OriginalHillNegativeJacobian
import NLS.Articles.KdVPseudomeasures.SourceNegativeNativeInverseMembership
import NLS.Articles.KdVPseudomeasures.OriginalHillGlobalNativeInverse
import NLS.Articles.KdVPseudomeasures.OriginalHillNativeCompactFibers
import NLS.SequenceSpaces.SignedOrderLinearInclusions

/-! The actual canonical map is a global analytic equivalence, with
analytic inverse, throughout the strict negative fractional Hilbert interval. -/
noncomputable section
open Filter Topology NLS.KdV NLS.WeightedCoeff
namespace NLS.Articles.KdVPseudomeasures

local instance negativeEquivalenceSourceNormed (r : ℝ) : NormedSpace ℝ (HillRealNegativeSource r) :=
  fourierRealZeroSubmodule_normedSpace (Weight.sobolev (-r))
local instance negativeEquivalenceTargetNormed (r : ℝ) : NormedSpace ℝ (HillRealFractionalTarget r) :=
  fourierRealZeroSubmodule_normedSpace (Weight.signedSobolev (1/2-r))

theorem injective_hillNegativeNativeMap (r : ℝ) (hr : 0 ≤ r) (hr1 : r < 1) :
    Function.Injective (hillNegativeNativeMap r hr hr1) := by
  intro q a he
  apply hillNegativeSourceInclusion_injective r hr1
  apply injective_hillRealSignedMap
  rw [← hillNegativeNativeMap_inclusion r hr hr1 q,
    ← hillNegativeNativeMap_inclusion r hr hr1 a, he]

theorem surjective_hillNegativeNativeMap (r : ℝ) (hr : 0 ≤ r) (hr1 : r < 1) :
    Function.Surjective (hillNegativeNativeMap r hr hr1) := by
  intro z
  obtain ⟨q,hq⟩ := surjective_hillRealSignedMap (hillNegativeTargetInclusion r hr1 z)
  let Z := signedOrderInclusion (-r+1/2) (1/2-r) (by linarith) 2 z.val.val
  have hz (k : ℤ) : Z.val k = (hillRealSignedMap q).val.val.val k := by
    rw [signedOrderInclusion_apply, hq, hillNegativeTargetInclusion_apply]
  have hmem := hillReal_negative_sobolev_of_native_output r hr hr1 q Z hz
  obtain ⟨u,hu⟩ := exists_hillNegativeSource_of_memlp r hr1 q hmem
  refine ⟨u,?_⟩
  apply hillNegativeTargetInclusion_injective r hr1
  rw [hillNegativeNativeMap_inclusion, hu, hq]

def hillNegativeNativeEquiv (r : ℝ) (hr : 0 ≤ r) (hr1 : r < 1) :
    HillRealNegativeSource r ≃ HillRealFractionalTarget r :=
  Equiv.ofBijective (hillNegativeNativeMap r hr hr1)
    ⟨injective_hillNegativeNativeMap r hr hr1, surjective_hillNegativeNativeMap r hr hr1⟩

theorem analyticAt_hillNegativeNativeEquiv_symm (r : ℝ) (hr : 0 ≤ r) (hr1 : r < 1)
    (z : HillRealFractionalTarget r) : AnalyticAt ℝ (hillNegativeNativeEquiv r hr hr1).symm z := by
  let e := hillNegativeNativeEquiv r hr hr1
  let q := e.symm z
  have hq : hillNegativeNativeMap r hr hr1 q = z := e.apply_symm_apply z
  obtain ⟨g,hg,_,_,hh⟩ := hillNegativeNativeMap_localInverse r hr hr1 q
  rw [hq] at hg hh
  apply hg.congr
  filter_upwards [hh] with a ha
  apply injective_hillNegativeNativeMap r hr hr1
  exact ha.trans (e.apply_symm_apply a).symm

theorem exists_hillNegativeNativeEquiv (r : ℝ) (hr : 0 ≤ r) (hr1 : r < 1) :
    ∃ e : HillRealNegativeSource r ≃ HillRealFractionalTarget r,
      (∀ q k, (e q).val.val.val k =
        (hillRealSignedMap (hillNegativeSourceInclusion r hr1 q)).val.val.val k) ∧
      (∀ q, AnalyticAt ℝ e q) ∧ (∀ z, AnalyticAt ℝ e.symm z) :=
  ⟨hillNegativeNativeEquiv r hr hr1, hillNegativeNativeMap_apply r hr hr1,
    analyticAt_hillNegativeNativeMap r hr hr1, analyticAt_hillNegativeNativeEquiv_symm r hr hr1⟩

end NLS.Articles.KdVPseudomeasures
