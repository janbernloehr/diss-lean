import NLS.Articles.KdVKdV2Frequencies.FiniteActionCoordinateRotations
import NLS.Articles.KdVKdV2Frequencies.NativeHamiltonianFourierCovectors

/-! # The actual finite-action Hamiltonian vectors are the printed PDE fields

At an actual finite-gap native source, agreement of first differentials on
all complex mean-zero directions determines every nonzero Fourier mode of
the Gardner vector. The zero mode is automatic. Smooth physical realization
then identifies the entire vector with the original KdV or KdV2 right side.
-/
noncomputable section
set_option autoImplicit false
open Set Complex NLS.KdV NLS.ZakharovShabat NLS.Fourier NLS.DifferentialPolynomial
open scoped ContDiff
namespace NLS.Articles.KdVKdV2Frequencies.GlobalRoughAbelianForwardData

/-- Every nonzero Fourier coefficient is determined by the independent
native physical Hamiltonian covector, not by an assumed rotation law. -/
theorem finiteGapActionCombination_vector_coefficient (D : GlobalRoughAbelianForwardData)
    (m : ℕ) (r : ℝ) (hrs : r=2*((m : ℝ)+1/2))
    (q : physicalRealMeanZeroWeightedSubmodule (Weight.sobolev (m : ℝ))) (S : Finset ℕ+)
    (hq : ∀ n : ℕ+, n ∉ S → hillRealGapHalfLength
      (nativeHillPhysicalSource m q.val q.property.1).val
      (nativeHillPhysicalSource m q.val q.property.1).property.1
      (nativeHillPhysicalSource m q.val q.property.1).property.2 n = 0)
    (k : ℤ) (hk : k≠0) :
    (NLS.Poisson.gardnerHamiltonianVector (D.finiteGapActionCombination m r hrs q S)
      (nativeHillSource m q.val)).val k = (2*Real.pi : ℂ)*I*k*
        (fderiv ℂ (nativeHillHierarchyHamiltonian m) q.val)
          (WeightedCoeff.ofFinsupp (Weight.sobolev (m : ℝ)) 2 (Finsupp.single (-k) 1)) := by
  let h : ScalarSobolev m := WeightedCoeff.ofFinsupp (Weight.sobolev (m : ℝ)) 2 (Finsupp.single (-k) 1)
  have hm : h.val 0=0 := by simp [h,WeightedCoeff.ofFinsupp_apply,hk]
  have hb : nativeHillSource m h =
      WeightedCoeff.ofFinsupp (Weight.sobolev (-1)) 2 (Finsupp.single (-k) 1) := by
    apply Subtype.ext
    funext n
    simp only [nativeHillSource_apply,h,WeightedCoeff.ofFinsupp_apply]
  have he := D.finiteGapActionCombination_fderiv_matches_native m r hrs q S hq h hm
  rw [hb] at he
  rw [NLS.Poisson.gardnerHamiltonianVector_apply,NLS.Poisson.hminusScalarGradient_apply,←he]

/-- ALL Fourier modes of the genuine action Hamiltonian vector are exactly
the printed third-order KdV field on every smooth physical finite-gap source. -/
theorem finiteGapActionCombination_kdv_vector (D : GlobalRoughAbelianForwardData)
    (q : physicalRealMeanZeroWeightedSubmodule (Weight.sobolev ((1 : ℕ) : ℝ))) (S : Finset ℕ+)
    (hq : ∀ n : ℕ+, n ∉ S → hillRealGapHalfLength
      (nativeHillPhysicalSource 1 q.val q.property.1).val
      (nativeHillPhysicalSource 1 q.val q.property.1).property.1
      (nativeHillPhysicalSource 1 q.val q.property.1).property.2 n = 0)
    (f : ℝ → ℂ) (hf : ContDiff ℝ ∞ f) (hp : Function.Periodic f 1)
    (hc : ∀ n : ℤ, q.val.val n=periodOneCoefficient f n) (k : ℤ) :
    (NLS.Poisson.gardnerHamiltonianVector (D.finiteGapActionCombination 1 3 (by norm_num) q S)
      (nativeHillSource 1 q.val)).val k = periodOneCoefficient (kdvRHS f) k := by
  have hd : deriv (evaluate f 0 kdvGradient) = kdvRHS f :=
    funext (fun x => (hasDerivAt_evaluate_kdvGradient f hf x).deriv)
  rw [←hd,periodOneCoefficient_deriv_of_smooth_periodic _
    (contDiff_evaluate f 0 hf contDiff_const _) (periodic_evaluate f 0 1 hp (fun _ => rfl) _) k]
  by_cases hk : k=0
  · subst k
    simp [NLS.Poisson.gardnerHamiltonianVector_apply]
  · rw [D.finiteGapActionCombination_vector_coefficient 1 3 (by norm_num) q S hq k hk]
    have he : nativeHillHierarchyHamiltonian 1 = nativeKdVHamiltonian :=
      funext nativeHillHierarchyHamiltonian_one
    rw [he,fderiv_nativeKdVHamiltonian_single q.val f hf hp hc k]
    ring

/-- The SAME complete coefficient identification for the printed fifth-order KdV2 field. -/
theorem finiteGapActionCombination_kdv2_vector (D : GlobalRoughAbelianForwardData)
    (q : physicalRealMeanZeroWeightedSubmodule (Weight.sobolev ((2 : ℕ) : ℝ))) (S : Finset ℕ+)
    (hq : ∀ n : ℕ+, n ∉ S → hillRealGapHalfLength
      (nativeHillPhysicalSource 2 q.val q.property.1).val
      (nativeHillPhysicalSource 2 q.val q.property.1).property.1
      (nativeHillPhysicalSource 2 q.val q.property.1).property.2 n = 0)
    (f : ℝ → ℂ) (hf : ContDiff ℝ ∞ f) (hp : Function.Periodic f 1)
    (hc : ∀ n : ℤ, q.val.val n=periodOneCoefficient f n) (k : ℤ) :
    (NLS.Poisson.gardnerHamiltonianVector (D.finiteGapActionCombination 2 5 (by norm_num) q S)
      (nativeHillSource 2 q.val)).val k = periodOneCoefficient (kdv2RHS f) k := by
  have hd : deriv (evaluate f 0 kdv2Gradient) = kdv2RHS f :=
    funext (fun x => (hasDerivAt_evaluate_kdv2Gradient f hf x).deriv)
  rw [←hd,periodOneCoefficient_deriv_of_smooth_periodic _
    (contDiff_evaluate f 0 hf contDiff_const _) (periodic_evaluate f 0 1 hp (fun _ => rfl) _) k]
  by_cases hk : k=0
  · subst k
    simp [NLS.Poisson.gardnerHamiltonianVector_apply]
  · rw [D.finiteGapActionCombination_vector_coefficient 2 5 (by norm_num) q S hq k hk]
    have he : nativeHillHierarchyHamiltonian 2 = nativeKdV2Hamiltonian :=
      funext nativeHillHierarchyHamiltonian_two
    rw [he,fderiv_nativeKdV2Hamiltonian_single q.val f hf hp hc k]
    ring

end NLS.Articles.KdVKdV2Frequencies.GlobalRoughAbelianForwardData
