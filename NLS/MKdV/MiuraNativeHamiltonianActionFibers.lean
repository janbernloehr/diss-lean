import NLS.MKdV.MiuraNativeHamiltonianLocalActionFactor
import NLS.MKdV.MiuraSobolevActionFiberIdentification
import NLS.MKdV.MiuraFiniteEncodedActionRealization
import NLS.MKdV.MiuraJointFiberNLSCoordinates

/-! # Independent native Hill Hamiltonians are constant on physical action fibers

Native physical actions and signed mean determine the original NLS
actions. The verified isospectral sharp trace identifies the independent
Hill Hamiltonian on every representative of those data.
-/
noncomputable section
open Set Complex NLS.ZakharovShabat
open scoped ENNReal ComplexConjugate
namespace NLS.MKdV

theorem miuraNativeActionMean_eq_implies_L2_eq (s : ℕ) (a b : MiuraRealSobolevSource s)
    (hJ : miuraNativeActionMeanMap s a.val = miuraNativeActionMeanMap s b.val) :
    miuraRealL2ActionMeanMap (miuraPhysicalSobolevL2SourceInclusion s a) =
      miuraRealL2ActionMeanMap (miuraPhysicalSobolevL2SourceInclusion s b) := by
  apply Prod.ext
  · apply Subtype.ext
    funext n
    change (miuraL2ActionSequence (miuraPhysicalSobolevL2SourceInclusion s a).val).val n =
      (miuraL2ActionSequence (miuraPhysicalSobolevL2SourceInclusion s b).val).val n
    rw [← miuraSobolevActionSequence_L2_coefficients s a n,← miuraSobolevActionSequence_L2_coefficients s b n]
    exact congrArg (fun q : MiuraNativeActionMeanTarget s => q.1.val n) hJ
  · have h := congrArg Prod.snd hJ
    change a.val.val 0 = b.val.val 0 at h
    change (miuraPhysicalSobolevL2SourceInclusion s a).val 0 = (miuraPhysicalSobolevL2SourceInclusion s b).val 0
    simpa only [miuraPhysicalSobolevL2SourceInclusion_apply] using h

theorem miuraRealDiagonalL2Source_native (s : ℕ) (a : MiuraRealSobolevSource s) :
    miuraRealDiagonalL2Source (miuraPhysicalSobolevL2SourceInclusion s a) =
      miuraActionInitialSource s a.val a.property := by
  apply Subtype.ext
  change scalarL2Diagonal (hierarchySobolevJetL2 s 0 (Nat.zero_le s) a.val) = _
  exact (miuraActionInitialSource_L2_diagonal s a.val a.property).symm

theorem miuraNative_sources_isospectral_of_actionMean (s : ℕ) (hs : 1 ≤ s) (a b : MiuraRealSobolevSource s)
    (hJ : miuraNativeActionMeanMap s a.val = miuraNativeActionMeanMap s b.val) :
    miuraActionInitialSource s b.val b.property ∈ sourceIsospectralSet (by simp)
      (miuraActionInitialSource s a.val a.property) := by
  have hI := miuraOriginalNLSActions_eq_of_Sobolev_actionMean_eq s hs a b
    (miuraNativeActionMean_eq_implies_L2_eq s a b hJ)
  have h : miuraRealDiagonalL2Source (miuraPhysicalSobolevL2SourceInclusion s b) ∈ sourceIsospectralSet (by simp)
      (miuraRealDiagonalL2Source (miuraPhysicalSobolevL2SourceInclusion s a)) := by
    rw [sourceIsospectralSet_eq_actionLevelSet_all_exponents (by simp) (by norm_num)]
    exact fun k => (miuraNLS_action_re_eq_of_sequence_eq _ _ hI k).symm
  rwa [miuraRealDiagonalL2Source_native,miuraRealDiagonalL2Source_native] at h

theorem miuraSpectralHillHamiltonian_eq_of_native_actionMean (s : ℕ) (hs : 1 ≤ s) (a b : MiuraRealSobolevSource s)
    (hJ : miuraNativeActionMeanMap s a.val = miuraNativeActionMeanMap s b.val) :
    miuraSpectralHillHamiltonian s a.val = miuraSpectralHillHamiltonian s b.val := by
  have ha : ∀ j, a.val.val j = conj (a.val.val (-j)) := a.property
  have hb : ∀ j, b.val.val j = conj (b.val.val (-j)) := b.property
  have hi := miuraNative_sources_isospectral_of_actionMean s hs a b hJ
  change miuraActionInitialSource s b.val hb ∈ sourceIsospectralSet (by simp)
    (miuraActionInitialSource s a.val ha) at hi
  rw [← miuraRealHigherSobolevDiagonal_source s a.val ha,
    ← miuraRealHigherSobolevDiagonal_source s b.val hb] at hi
  have h := sobolevOddHamiltonian_eq_of_isospectral s hs
    (miuraRealHigherSobolevDiagonal s a.val ha) (miuraRealHigherSobolevDiagonal s b.val hb) hi
  change sobolevOddHamiltonian s hs (b.val,b.val) = sobolevOddHamiltonian s hs (a.val,a.val) at h
  rw [nativeMiuraHillHamiltonian_odd_restriction s hs,nativeMiuraHillHamiltonian_odd_restriction s hs] at h
  rw [miuraSpectralHillHamiltonian_eq_native]
  exact (mul_left_cancel₀ (by norm_num : (2 : ℂ) ≠ 0) h).symm

namespace MiuraNativeCartesianChart
variable {s : ℕ} {a : MiuraRealSobolevSource s}

theorem hamiltonian_eq_of_normalized_actionMean (C : MiuraNativeCartesianChart s a) (hs : 1 ≤ s)
    (b : MiuraRealSobolevSource s) (z : MiuraPositiveCartesianTarget)
    (hz : z ∈ Metric.ball (miuraSobolevNormalizedCartesianMap s a.val) C.radius)
    (hzr : z ∈ miuraCartesianRealSubmodule)
    (hJ : miuraPositiveCartesianActionMean z = miuraNormalizedNativeActionMeanMap s b.val) :
    C.hamiltonian z = miuraSpectralHillHamiltonian s b.val := by
  let p : MiuraRealSobolevSource s := ⟨C.inverse z,C.inverse_real z hz hzr⟩
  apply miuraSpectralHillHamiltonian_eq_of_native_actionMean s hs p b
  apply (miuraNativeActionMeanEquiv s).injective
  change miuraNormalizedNativeActionMeanMap s (C.inverse z) = miuraNormalizedNativeActionMeanMap s b.val
  rw [← miuraNormalizedCartesian_actionMean s (C.inverse z) p.property,(C.right_inverse z hz).2]
  exact hJ

end MiuraNativeCartesianChart
end NLS.MKdV
