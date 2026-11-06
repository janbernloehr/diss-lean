import NLS.Articles.KdVKdV2Frequencies.PhysicalHilbertActionReindex
import NLS.Articles.KdVKdV2Frequencies.OriginalHierarchyActionFrequencies
import NLS.Articles.KdVKdV2Frequencies.NativeFiniteGapHamiltonianVariation
import NLS.Articles.KdVConvexity.IntrinsicPhysicalFrequencies
import NLS.KdV.NativeHillH1PhysicalComparison

/-! The independent original KdV action Hamiltonians agree on the ENTIRE
original positive cubic-weight action cone. Exact physical source, action,
period and native-energy comparisons discharge every matching obligation. -/
noncomputable section
set_option autoImplicit false
open Set Complex NLS.KdV NLS.ZakharovShabat NLS.Articles.KdVConvexity
namespace NLS.Articles.KdVKdV2Frequencies
namespace GlobalRoughAbelianForwardData

/-- The actual physical Hilbert actions are exactly the original native
actions of the SAME fixed map, with no change of labels or amplitude. -/
theorem native_physicalHilbertActions_eq (D : GlobalRoughAbelianForwardData)
    (q : physicalRealMeanZeroWeightedSubmodule (Weight.sobolev ((1 : ℕ) : ℝ))) :
    physicalHilbertActions hillH1SpectralWeight (nativeRealHillH1 q.val q.property.1)=
      originalActionInclusion (physicalHilbertActionReindex (D.nativeSourceActionSequence 1 3 (by norm_num) q)) := by
  ext n
  rw [physicalHilbertActions_apply,originalActionInclusion_apply,physicalHilbertActionReindex_coefficient,
    Equiv.apply_symm_apply,D.nativeSourceActionSequence_eq_gap_integral]
  let p := hillWeightedPhysicalSource hillH1SpectralWeight (nativeRealHillH1 q.val q.property.1)
  change (hillRealGapIntegral p.val p.property.1 p.property.2 n 0 : ℂ)=_
  exact congrArg (fun s : RealPeriodOneHillPotential =>
    (hillRealGapIntegral s.val s.property.1 s.property.2 n 0 : ℂ))
      (nativeRealHillH1_physical q.val q.property.1)

/-- The independently chosen original action representative has precisely
ALL prescribed actions in the original weighted norm. -/
theorem originalActionPotential_source_actions (D : GlobalRoughAbelianForwardData)
    (a : WeightedCoeff.positiveActionLocus (Weight.sobolev 3) 1) :
    let q : physicalRealMeanZeroWeightedSubmodule (Weight.sobolev ((1 : ℕ) : ℝ)) :=
      ⟨D.originalActionPotential 1 3 (by norm_num) a,
        D.originalActionPotential_real 1 3 (by norm_num) a,D.originalActionPotential_zero 1 3 (by norm_num) a⟩
    D.nativeSourceActionSequence 1 3 (by norm_num) q=a.val := by
  intro q
  let z := originalActionTarget 1 3 (by norm_num) a
  have hcoord (j : ℤ) : (D.signed (nativeHillSource 1 q.val)).val j=z.val.val j := by
    have h := congrArg (fun b : WeightedCoeff (Weight.sobolev (-1/2)) 2 => b.val j)
      (D.rawIntegerInverseSource_signed 1 z)
    simpa only [WeightedCoeff.sobolevInclusion_apply] using! h
  apply Subtype.ext
  funext j
  rw [D.nativeSourceActionSequence_apply,hcoord j,hcoord (-j)]
  have h := congrArg (fun b : WeightedCoeff (Weight.sobolev 3) 1 => b.val j)
    (originalActionTarget_actions 1 3 (by norm_num) a)
  simpa only [sobolevSignedActionSequence_apply] using h

/-- Equality of the TWO independently defined physical action energies on
EVERY original positive action point, including all closed and infinite gaps. -/
theorem physicalActionEnergy_eq_original (D : GlobalRoughAbelianForwardData)
    (a : WeightedCoeff.positiveActionLocus (Weight.sobolev 3) 1) :
    originalPhysicalActionEnergy
      ⟨physicalHilbertActionReindex a.val,physicalHilbertActionReindex_nonnegative a.val a.property.1⟩=
        (D.originalActionHamiltonian 1 3 (by norm_num) a : ℂ) := by
  let q : physicalRealMeanZeroWeightedSubmodule (Weight.sobolev ((1 : ℕ) : ℝ)) :=
    ⟨D.originalActionPotential 1 3 (by norm_num) a,
      D.originalActionPotential_real 1 3 (by norm_num) a,D.originalActionPotential_zero 1 3 (by norm_num) a⟩
  let p := nativeRealHillH1 q.val q.property.1
  let b : WeightedCoeff.nonnegativeLocus originalActionWeight 1 :=
    ⟨physicalHilbertActionReindex a.val,physicalHilbertActionReindex_nonnegative a.val a.property.1⟩
  have hm : p.val.val 0=0 := by
    change (nativeToHillH1 q.val).val 0=0
    rw [nativeToHillH1_coefficient]
    exact q.property.2
  have ha := D.native_physicalHilbertActions_eq q
  rw [D.originalActionPotential_source_actions a] at ha
  have he := originalPhysicalActionEnergy_eq_source b p hm ha
  rw [←hillNativeH1Hamiltonian_eq_physical_integral] at he
  have hp : hillNativeH1Hamiltonian p.val=nativeKdVHamiltonian q.val := nativeToHillH1_hamiltonian q.val
  exact he.trans (hp.trans (by
    rw [D.originalActionHamiltonian_complex_value,nativeHillHierarchyHamiltonian_one]))

end GlobalRoughAbelianForwardData
end NLS.Articles.KdVKdV2Frequencies
