import NLS.MKdV.MiuraRealCartesianMap
import NLS.ComplexAnalysis.RealAnalyticNativeInverseNeighborhoods

/-! # A physical real inverse chart at the free scalar profile

Both domains are full open neighborhoods in the genuine physical real L²
and positive half-order Cartesian/real-mean Banach spaces. This local chart
does not assert global invertibility or Gardner canonicity.
-/
noncomputable section
open Set Complex Filter Topology NLS.ZakharovShabat NLS.ComplexAnalysis
open scoped ENNReal ComplexConjugate
namespace NLS.MKdV

theorem exists_miuraPhysicalCartesian_localInverse_at_zero :
    ∃ U : Set (Coeff.physicalRealSubmodule 2), ∃ V : Set MiuraRealCartesianTarget,
      IsOpen U ∧ IsOpen V ∧ (0 : Coeff.physicalRealSubmodule 2) ∈ U ∧ (0 : MiuraRealCartesianTarget) ∈ V ∧
      miuraPhysicalCartesianMap '' U = V ∧ BijOn miuraPhysicalCartesianMap U V ∧
      ∃ G : MiuraRealCartesianTarget → Coeff.physicalRealSubmodule 2,
        AnalyticOnNhd ℝ miuraPhysicalCartesianMap U ∧ AnalyticOnNhd ℝ G V ∧ G 0 = 0 ∧
        (∀ a ∈ U, G (miuraPhysicalCartesianMap a) = a) ∧
        (∀ z ∈ V, G z ∈ U ∧ miuraPhysicalCartesianMap (G z) = z) := by
  exact @exists_real_analytic_inverse_neighborhoods_of_fderiv_equiv
    (Coeff.physicalRealSubmodule 2) MiuraRealCartesianTarget
    inferInstance inferInstance inferInstance inferInstance inferInstance inferInstance
    miuraPhysicalCartesianMap (analyticAt_miuraPhysicalCartesianMap 0)
    miuraCartesianRealFreeEquiv fderiv_miuraPhysicalCartesianMap_zero miuraPhysicalCartesianMap_zero

/-- Every complex left inverse germ of the actual Cartesian map preserves
physical reality on nearby genuine real target data. -/
theorem miuraPositiveCartesian_complex_inverse_real_germ
    (g : MiuraPositiveCartesianTarget → Coeff 2)
    (hl : ∀ᶠ b in 𝓝 (0 : Coeff 2), g (miuraPositiveCartesianMap b) = b) :
    ∀ᶠ z in 𝓝 (0 : MiuraRealCartesianTarget), g z.val ∈ Coeff.physicalRealSubmodule 2 := by
  obtain ⟨_,V,_,hV,_,h0V,_,_,G,_,hGA,hG0,_,hG⟩ := exists_miuraPhysicalCartesian_localInverse_at_zero
  have hbase : G (miuraPhysicalCartesianMap 0) = 0 := by rw [miuraPhysicalCartesianMap_zero,hG0]
  have hc : ContinuousAt G (miuraPhysicalCartesianMap 0) := by
    rw [miuraPhysicalCartesianMap_zero]
    exact (hGA 0 h0V).continuousAt
  have hr : ∀ᶠ z in 𝓝 (miuraPhysicalCartesianMap 0), miuraPhysicalCartesianMap (G z) = z := by
    rw [miuraPhysicalCartesianMap_zero]
    filter_upwards [hV.mem_nhds h0V] with z hz
    exact (hG z hz).2
  have he := inverse_germ_preserves_subspace
    (fun b : Coeff.physicalRealSubmodule 2 => b.val) continuous_subtype_val
    (fun z : MiuraRealCartesianTarget => z.val) miuraPositiveCartesianMap miuraPhysicalCartesianMap
    0 g G hc hbase hl hr miuraPhysicalCartesianMap_inclusion
    (fun b => b ∈ Coeff.physicalRealSubmodule 2) (fun b => b.property)
  simpa only [miuraPhysicalCartesianMap_zero] using he

theorem continuous_miuraPhysicalCartesianMap : Continuous miuraPhysicalCartesianMap :=
  continuous_iff_continuousAt.mpr (fun a => (analyticAt_miuraPhysicalCartesianMap a).continuousAt)

/-- Properness also holds in the genuine real target. -/
theorem isProperMap_miuraPhysicalCartesianMap : IsProperMap miuraPhysicalCartesianMap := by
  apply isProperMap_iff_isCompact_preimage.mpr
  refine ⟨continuous_miuraPhysicalCartesianMap,?_⟩
  intro K hK
  have hIK := hK.image miuraCartesianRealSubmodule.subtypeL.continuous
  have hCK := isProperMap_miuraRealPositiveCartesianMap.isCompact_preimage hIK
  apply hCK.of_isClosed_subset (hK.isClosed.preimage continuous_miuraPhysicalCartesianMap)
  intro a ha
  exact ⟨miuraPhysicalCartesianMap a,ha,miuraPhysicalCartesianMap_inclusion a⟩

end NLS.MKdV
