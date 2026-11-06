import NLS.Articles.KdVConvexity.PhysicalActionHamiltonian
import NLS.KdV.HillNativeH1Recovery
import NLS.KdV.NativeHamiltonianPhysicalIntegrals
import NLS.Articles.KdVKdV2Frequencies.NativeSourceFiniteActionVariation
import NLS.Articles.KdVKdV2Frequencies.OriginalRoughActionGerms

/-! # The same physical H1 source and energy in both action constructions

Both native H1 models retain the original unit Fourier coefficients.
Their continuous representatives and physical energies agree, and the
fixed signed Birkhoff map has exactly the article's positive raw actions.
-/
noncomputable section
set_option autoImplicit false
open Set Complex
open NLS.KdV NLS.Fourier NLS.ZakharovShabat NLS.Articles.KdVKdV2Frequencies
open scoped ComplexConjugate
namespace NLS.Articles.KdVConvexity

def nativeH1PhysicalRepresentative (q : physicalRealMeanZeroWeightedSubmodule (Weight.sobolev ((1:ℕ):ℝ))) :
    RealHillWeightedPotential hillH1SpectralWeight :=
  ⟨hillSobolevToNativeH1 (hierarchySobolevToScalarDomain 1 (by norm_num) q.val),by
    intro j
    simpa only [SpectralWeight.toCoeff_apply,hillSobolevToNativeH1_apply,hierarchySobolevToScalarDomain_apply] using q.property.1 j⟩

@[simp] theorem nativeH1PhysicalRepresentative_apply
    (q : physicalRealMeanZeroWeightedSubmodule (Weight.sobolev ((1:ℕ):ℝ))) (j : ℤ) :
    (nativeH1PhysicalRepresentative q).val.val j=q.val.val j :=
  (hillSobolevToNativeH1_apply _ j).trans (hierarchySobolevToScalarDomain_apply 1 (by norm_num) q.val j)

theorem nativeH1PhysicalRepresentative_mean_zero
    (q : physicalRealMeanZeroWeightedSubmodule (Weight.sobolev ((1:ℕ):ℝ))) :
    (nativeH1PhysicalRepresentative q).val.val 0=0 :=
  (nativeH1PhysicalRepresentative_apply q 0).trans q.property.2

/-- The independent physical Hamiltonians coincide on the full H1
space, without a finite-gap or smoothness assumption. -/
theorem nativeH1PhysicalRepresentative_energy
    (q : physicalRealMeanZeroWeightedSubmodule (Weight.sobolev ((1:ℕ):ℝ))) :
    hillNativeH1Hamiltonian (nativeH1PhysicalRepresentative q).val = nativeKdVHamiltonian q.val := by
  rw [hillNativeH1Hamiltonian_eq_physical_integral,nativeKdVHamiltonian_eq_classical]
  have he : hillNativeH1ToSobolev (nativeH1PhysicalRepresentative q).val =
      hierarchySobolevToScalarDomain 1 (by norm_num) q.val := by
    apply Subtype.ext
    funext j
    rw [hillNativeH1ToSobolev_apply,nativeH1PhysicalRepresentative_apply,
      hierarchySobolevToScalarDomain_apply]
  congr 1
  funext x
  change periodOneSobolevSynthesis (hillNativeH1ToSobolev (nativeH1PhysicalRepresentative q).val)
    (x:AddCircle (2:ℝ)) = periodOneSobolevSynthesis (hierarchySobolevToScalarDomain 1 (by norm_num) q.val)
      (x:AddCircle (2:ℝ))
  rw [he]

theorem nativeH1PhysicalRepresentative_rough_source
    (q : physicalRealMeanZeroWeightedSubmodule (Weight.sobolev ((1:ℕ):ℝ))) :
    hillWeightedNativeHminusSource hillH1SpectralWeight (nativeH1PhysicalRepresentative q).val =
      nativeHillSource 1 q.val := by
  apply Subtype.ext
  funext j
  rw [hillWeightedNativeHminusSource_apply,nativeH1PhysicalRepresentative_apply,
    nativeHillSource,WeightedCoeff.sobolevInclusion_apply]

/-- The two actual action constructions agree at every positive label,
including all closed gaps, for any fixed global physical Birkhoff data. -/
theorem nativeH1PhysicalRepresentative_actions (D : GlobalRoughAbelianForwardData)
    (q : physicalRealMeanZeroWeightedSubmodule (Weight.sobolev ((1:ℕ):ℝ))) (n : ℕ+) :
    (D.nativeSourceActionSequence 1 3 (by norm_num) q).val (n:ℤ) =
      physicalHilbertActions hillH1SpectralWeight (nativeH1PhysicalRepresentative q) n := by
  rw [D.nativeSourceActionSequence_apply,if_pos (show (0:ℤ)<(n:ℤ) by exact_mod_cast n.pos)]
  change D.roughActionCoordinate n (nativeHillSource 1 q.val) = _
  rw [←nativeH1PhysicalRepresentative_rough_source,
    hillWeightedNativeHminusSource_eq_original,physicalHilbertActions_apply]
  exact D.roughActionCoordinate_physical
    (hillWeightedPhysicalSource hillH1SpectralWeight (nativeH1PhysicalRepresentative q)) n

end NLS.Articles.KdVConvexity
