import NLS.Articles.KdVKdV2Frequencies.GlobalNativeHamiltonians
import NLS.Articles.KdVKdV2Frequencies.GlobalRoughActionIsospectral
import NLS.KdV.NativeHamiltonianIsospectral

/-! # The actual global native physical Hamiltonians depend only on the actions

Equality of every complete original signed action determines the entire
rough Hill discriminant of the SAME native inverse source. The printed
physical H1 and H2 are spectral invariants on their full native domains.
Analytic factorization through actions is a further obligation.
-/
noncomputable section
set_option autoImplicit false
open Set Complex NLS.KdV NLS.ZakharovShabat
open scoped ComplexConjugate
namespace NLS.Articles.KdVKdV2Frequencies.GlobalRoughAbelianForwardData

/-- Complete original action equality determines the inverse discriminant,
even when comparing two different integer native target orders. -/
theorem rawIntegerInverseSource_discriminant_eq_of_actions_eq
    (D : GlobalRoughAbelianForwardData) (s t : ℕ)
    (z : physicalRealMeanZeroWeightedSubmodule (Weight.sobolev ((s : ℝ)+1/2)))
    (w : physicalRealMeanZeroWeightedSubmodule (Weight.sobolev ((t : ℝ)+1/2)))
    (h : ∀ n : ℕ+, z.val.val (n : ℤ)*z.val.val (-(n : ℤ)) =
      w.val.val (n : ℤ)*w.val.val (-(n : ℤ))) :
    hillHminusDiscriminant (nativeHillSource s (D.rawIntegerInverseSource s z)) =
      hillHminusDiscriminant (nativeHillSource t (D.rawIntegerInverseSource t w)) := by
  have hz (n : ℤ) : (D.signed (nativeHillSource s (D.rawIntegerInverseSource s z))).val n = z.val.val n := by
    have he := congrArg (fun a : WeightedCoeff (Weight.sobolev (-1/2)) 2 => a.val n)
      (D.rawIntegerInverseSource_signed s z)
    simpa only [nativeHillSource,WeightedCoeff.sobolevInclusion_apply] using he
  have hw (n : ℤ) : (D.signed (nativeHillSource t (D.rawIntegerInverseSource t w))).val n = w.val.val n := by
    have he := congrArg (fun a : WeightedCoeff (Weight.sobolev (-1/2)) 2 => a.val n)
      (D.rawIntegerInverseSource_signed t w)
    simpa only [nativeHillSource,WeightedCoeff.sobolevInclusion_apply] using he
  exact funext (D.discriminant_eq_of_signed_actions_eq _ _
    (nativeHillSource_real s _ (D.rawIntegerInverseSource_real s z))
    (nativeHillSource_real t _ (D.rawIntegerInverseSource_real t w))
    (by simpa only [nativeHillSource_apply] using D.rawIntegerInverseSource_zero s z)
    (by simpa only [nativeHillSource_apply] using D.rawIntegerInverseSource_zero t w)
    (fun n => by simpa only [hz,hw] using h n))

/-- On the ENTIRE actual raw real mean-zero h^(3/2) domain, the ORIGINAL
physical H1 composed with the SAME global inverse is constant on every
complete action fiber, including infinite support and all closed gaps. -/
theorem birkhoffKdVHamiltonian_eq_of_actions_eq (D : GlobalRoughAbelianForwardData)
    (z w : physicalRealMeanZeroWeightedSubmodule (Weight.sobolev (((1 : ℕ) : ℝ)+1/2)))
    (h : ∀ n : ℕ+, z.val.val (n : ℤ)*z.val.val (-(n : ℤ)) =
      w.val.val (n : ℤ)*w.val.val (-(n : ℤ))) :
    D.birkhoffKdVHamiltonian z = D.birkhoffKdVHamiltonian w := by
  apply congrArg Complex.re
  exact nativeKdVHamiltonian_eq_of_discriminant_eq _ _
    (D.rawIntegerInverseSource_real 1 z) (D.rawIntegerInverseSource_real 1 w)
    (D.rawIntegerInverseSource_zero 1 z) (D.rawIntegerInverseSource_zero 1 w)
    (D.rawIntegerInverseSource_discriminant_eq_of_actions_eq 1 1 z w h)

/-- On the ENTIRE actual raw real mean-zero h^(5/2) domain, the ORIGINAL
physical H2 composed with the SAME global inverse is constant on every
complete action fiber, without an extra regularity or gap hypothesis. -/
theorem birkhoffKdV2Hamiltonian_eq_of_actions_eq (D : GlobalRoughAbelianForwardData)
    (z w : physicalRealMeanZeroWeightedSubmodule (Weight.sobolev (((2 : ℕ) : ℝ)+1/2)))
    (h : ∀ n : ℕ+, z.val.val (n : ℤ)*z.val.val (-(n : ℤ)) =
      w.val.val (n : ℤ)*w.val.val (-(n : ℤ))) :
    D.birkhoffKdV2Hamiltonian z = D.birkhoffKdV2Hamiltonian w := by
  apply congrArg Complex.re
  exact nativeKdV2Hamiltonian_eq_of_discriminant_eq _ _
    (D.rawIntegerInverseSource_real 2 z) (D.rawIntegerInverseSource_real 2 w)
    (D.rawIntegerInverseSource_zero 2 z) (D.rawIntegerInverseSource_zero 2 w)
    (D.rawIntegerInverseSource_discriminant_eq_of_actions_eq 2 2 z w h)

end NLS.Articles.KdVKdV2Frequencies.GlobalRoughAbelianForwardData
