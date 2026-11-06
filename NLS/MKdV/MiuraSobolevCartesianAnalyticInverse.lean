import NLS.MKdV.MiuraRealSobolevCartesianJacobian
import NLS.MKdV.MiuraCartesianSobolevInverse
import NLS.MKdV.SpectralMiuraHamiltonians
import NLS.ComplexAnalysis.AnalyticGlobalInverseCharts

/-! # Global analytic native Sobolev Cartesian inverses

The actual Cartesian bijection has a real analytic inverse on the entire
native target at every integer order s>=1. The independent physical Hill
Hamiltonian K_(s+1) is therefore analytic in those Cartesian coordinates.
This does not yet identify canonical mKdV angles or action frequencies.
-/
noncomputable section
open Set Complex NLS.ZakharovShabat
open scoped ENNReal ComplexConjugate
namespace NLS.MKdV

def miuraPhysicalSobolevCartesianEquiv (s : ℕ) (hs : 1 ≤ s) :
    MiuraRealSobolevSource s ≃ MiuraRealSobolevCartesianTarget s :=
  Equiv.ofBijective (miuraPhysicalSobolevCartesianMap s) (miuraPhysicalSobolevCartesianMap_bijective s hs)

@[simp] theorem miuraPhysicalSobolevCartesianEquiv_apply (s : ℕ) (hs : 1 ≤ s) (a : MiuraRealSobolevSource s) :
    miuraPhysicalSobolevCartesianEquiv s hs a = miuraPhysicalSobolevCartesianMap s a := rfl

def miuraPhysicalSobolevCartesianInverse (s : ℕ) (hs : 1 ≤ s) :
    MiuraRealSobolevCartesianTarget s → MiuraRealSobolevSource s :=
  (miuraPhysicalSobolevCartesianEquiv s hs).symm

@[simp] theorem miuraPhysicalSobolevCartesianInverse_map (s : ℕ) (hs : 1 ≤ s) (a : MiuraRealSobolevSource s) :
    miuraPhysicalSobolevCartesianInverse s hs (miuraPhysicalSobolevCartesianMap s a) = a :=
  (miuraPhysicalSobolevCartesianEquiv s hs).symm_apply_apply a

@[simp] theorem miuraPhysicalSobolevCartesianMap_inverse (s : ℕ) (hs : 1 ≤ s) (z : MiuraRealSobolevCartesianTarget s) :
    miuraPhysicalSobolevCartesianMap s (miuraPhysicalSobolevCartesianInverse s hs z) = z :=
  (miuraPhysicalSobolevCartesianEquiv s hs).apply_symm_apply z

/-- The global inverse is analytic everywhere in the full native
Sobolev norms, including arbitrary signed mean and closed actions. -/
theorem analyticOnNhd_miuraPhysicalSobolevCartesianInverse (s : ℕ) (hs : 1 ≤ s) :
    AnalyticOnNhd ℝ (miuraPhysicalSobolevCartesianInverse s hs) univ := by
  apply @NLS.ComplexAnalysis.analyticOnNhd_inverse_of_local_charts
    ℝ (MiuraRealSobolevSource s) (MiuraRealSobolevCartesianTarget s)
    inferInstance inferInstance inferInstance inferInstance inferInstance
    (miuraPhysicalSobolevCartesianMap s) (miuraPhysicalSobolevCartesianInverse s hs)
    (miuraPhysicalSobolevCartesianMap_injective s hs) (miuraPhysicalSobolevCartesianMap_inverse s hs)
  intro a
  obtain ⟨P,hP,ha,_,hG⟩ := exists_miuraPhysicalSobolevCartesian_analytic_chart s hs a
  exact ⟨P,hP,ha,hG⟩

def miuraPhysicalSobolevCartesianHomeomorph (s : ℕ) (hs : 1 ≤ s) :
    MiuraRealSobolevSource s ≃ₜ MiuraRealSobolevCartesianTarget s where
  toEquiv := miuraPhysicalSobolevCartesianEquiv s hs
  continuous_toFun := continuous_iff_continuousAt.mpr (fun a =>
    (analyticAt_miuraPhysicalSobolevCartesianMap s a).continuousAt)
  continuous_invFun := continuous_iff_continuousAt.mpr (fun z =>
    (analyticOnNhd_miuraPhysicalSobolevCartesianInverse s hs z (mem_univ z)).continuousAt)

/-- The independent physical Hill Hamiltonian expressed in the actual
native Cartesian coordinates, before action descent or canonicity. -/
def miuraSpectralCartesianHamiltonian (s : ℕ) (hs : 1 ≤ s) (z : MiuraRealSobolevCartesianTarget s) : ℂ :=
  miuraSpectralHillHamiltonian s (miuraPhysicalSobolevCartesianInverse s hs z).val

theorem analyticOnNhd_miuraSpectralCartesianHamiltonian (s : ℕ) (hs : 1 ≤ s) :
    AnalyticOnNhd ℝ (miuraSpectralCartesianHamiltonian s hs) univ := by
  intro z hz
  have hg := analyticOnNhd_miuraPhysicalSobolevCartesianInverse s hs z hz
  have hJ := (MiuraRealSobolevSource s).subtypeL.analyticAt (miuraPhysicalSobolevCartesianInverse s hs z)
  exact ((analyticAt_miuraSpectralHillHamiltonian s _).restrictScalars (𝕜 := ℝ)).comp (hJ.comp hg)

theorem miuraSpectralCartesianHamiltonian_map (s : ℕ) (hs : 1 ≤ s) (a : MiuraRealSobolevSource s) :
    miuraSpectralCartesianHamiltonian s hs (miuraPhysicalSobolevCartesianMap s a) =
      miuraSpectralHillHamiltonian s a.val := by
  rw [miuraSpectralCartesianHamiltonian,miuraPhysicalSobolevCartesianInverse_map]

end NLS.MKdV
