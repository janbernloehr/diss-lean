import NLS.MKdV.MiuraL2MassActionFrequency
import NLS.MKdV.MiuraZeroSobolevActionCoordinates

/-! # The native mass frequency and intrinsic frequencies at every order

The literal H⁰/L² coefficient identification transports any native
normal form to a full physical mass normal form. Thus the intrinsic
raw-action frequency framework now includes s=0 with the same formula.
-/
noncomputable section
open Set Complex NLS.ZakharovShabat
open scoped ENNReal ComplexConjugate
namespace NLS.MKdV.MiuraNativeHamiltonianActionData

theorem mass_pullback_contains (D : MiuraNativeHamiltonianActionData 0) (b : MiuraRealL2) :
    (miuraNativeActionMeanEquiv 0).symm (miuraRealL2ActionMeanMap b) ∈ D.domain := by
  obtain ⟨a,ha⟩ := miuraPhysicalSobolevL2SourceInclusion_zero_surjective b
  rw [miuraNativeActionMean_zero_of_L2_representative a b ha]
  exact D.contains a

theorem mass_pullback_recovery (D : MiuraNativeHamiltonianActionData 0) (b : MiuraRealL2) :
    D.hamiltonian ((miuraNativeActionMeanEquiv 0).symm (miuraRealL2ActionMeanMap b)) = miuraL2Mass b.val := by
  obtain ⟨a,ha⟩ := miuraPhysicalSobolevL2SourceInclusion_zero_surjective b
  rw [miuraNativeActionMean_zero_of_L2_representative a b ha,D.recovery a]
  exact miuraSpectralHillHamiltonian_zero_of_L2_representative a b ha

def toL2MassData (D : MiuraNativeHamiltonianActionData 0) : MiuraL2MassActionData :=
  MiuraL2MassActionData.ofLinearPullback (miuraNativeActionMeanEquiv 0).symm.toContinuousLinearMap
    D.domain D.hamiltonian D.domain_open D.analytic D.mass_pullback_contains D.mass_pullback_recovery

theorem toL2MassData_frequency (D : MiuraNativeHamiltonianActionData 0) (n : ℤ)
    (b : MiuraNativeActionMeanTarget 0) (hb : b ∈ D.domain) :
    D.toL2MassData.frequency n (miuraNativeActionMeanEquiv 0 b) = D.frequency n b := by
  let E := miuraNativeActionMeanEquiv 0
  have hF : HasFDerivAt D.hamiltonian (fderiv ℂ D.hamiltonian b) (E.symm (E b)) := by
    rw [ContinuousLinearEquiv.symm_apply_apply]
    exact (D.analytic b hb).differentiableAt.hasFDerivAt
  have hd := hF.comp (E b) E.symm.toContinuousLinearMap.hasFDerivAt
  change fderiv ℂ (fun z => D.hamiltonian (E.symm z)) (E b)
    (WeightedCoeff.single (p := 1) (Weight.sobolev 1) n 1,0) = D.frequency n b
  change HasFDerivAt (fun z => D.hamiltonian (E.symm z)) _ (E b) at hd
  rw [hd.fderiv]
  change fderiv ℂ D.hamiltonian b (E.symm (WeightedCoeff.single (p := 1) (Weight.sobolev 1) n 1,0)) = _
  rw [miuraNativeActionMeanEquiv_zero_symm_single]
  rfl

theorem frequency_mass_eq (D : MiuraNativeHamiltonianActionData 0) (a : MiuraRealSobolevSource 0)
    (n : ℤ) (hn : 0 < n) : D.frequency n (miuraNativeActionMeanMap 0 a.val) = 2*(Real.pi : ℂ)*n := by
  let b := miuraPhysicalSobolevL2SourceInclusion 0 a
  have h := D.toL2MassData.frequency_eq b.val b.property n hn
  change D.toL2MassData.frequency n (miuraRealL2ActionMeanMap b) = _ at h
  rw [← miuraNormalizedNativeActionMeanMap_zero_L2 a] at h
  change D.toL2MassData.frequency n (miuraNativeActionMeanEquiv 0 (miuraNativeActionMeanMap 0 a.val)) = _ at h
  rwa [D.toL2MassData_frequency n _ (D.contains a)] at h

/-- Positive physical action frequencies are independent of the global
normal form chosen, at every native order s>=0 and every physical profile. -/
theorem frequency_unique_allOrders {s : ℕ} (D E : MiuraNativeHamiltonianActionData s)
    (a : MiuraRealSobolevSource s) (n : ℤ) (hn : 0 < n) :
    D.frequency n (miuraNativeActionMeanMap s a.val) = E.frequency n (miuraNativeActionMeanMap s a.val) := by
  by_cases hs : 1 ≤ s
  · exact D.frequency_unique E hs a n hn
  · have he : s = 0 := by omega
    subst s
    exact (D.frequency_mass_eq a n hn).trans (E.frequency_mass_eq a n hn).symm

end NLS.MKdV.MiuraNativeHamiltonianActionData
