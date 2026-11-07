import NLS.Articles.KdVKdV2Frequencies.GlobalNativeRealDiffeomorphisms
import NLS.SequenceSpaces.SignedHilbertPairs

/-! Native complex inverse germs in real Hilbert pair coordinates, at
EVERY real target and every order. The real restriction is the SAME
global inverse; no surjectivity or stronger regularity is assumed. -/
noncomputable section
set_option autoImplicit false
open Set Complex Filter Topology
open scoped ENNReal
namespace NLS.KdV
open NLS.Articles.KdVKdV2Frequencies
open GlobalRoughAbelianForwardData

def nativeRealPairTarget (e : ℤ ≃ ℕ+) (z : Coeff 2 × Coeff 2)
    (hz : z∈Coeff.realPairLocus 2) : physicalRealDeletedSubmodule :=
  ⟨signedPairToDeleted e z,signedPairToDeleted_real e z hz⟩

def nativeRealPairInverse (D : GlobalRoughAbelianForwardData) (e : ℤ ≃ ℕ+)
    (t : ℝ) (ht : 0≤t) (z : Coeff 2 × Coeff 2) (hz : z∈Coeff.realPairLocus 2) :
    WeightedCoeff (Weight.sobolev (t-1)) 2 :=
  WeightedCoeff.meanZeroWeightedLiftCLM (Weight.sobolev (t-1))
    (D.realNativeInverse t ht (nativeRealPairTarget e z hz)).val

theorem nativeRealPairInverse_real (D : GlobalRoughAbelianForwardData) (e : ℤ ≃ ℕ+)
    (t : ℝ) (ht : 0≤t) (z : Coeff 2 × Coeff 2) (hz : z∈Coeff.realPairLocus 2) :
    IsRealPeriodOneHminusOne (periodOneSobolevImageInclusion t ht (nativeRealPairInverse D e t ht z hz)) :=
  realNativeSource_real t ht (D.realNativeInverse t ht (nativeRealPairTarget e z hz))

theorem nativeRealPairInverse_signed (D : GlobalRoughAbelianForwardData) (e : ℤ ≃ ℕ+)
    (t : ℝ) (ht : 0≤t) (z : Coeff 2 × Coeff 2) (hz : z∈Coeff.realPairLocus 2) :
    D.signed (periodOneSobolevImageInclusion t ht (nativeRealPairInverse D e t ht z hz))=
      WeightedCoeff.sobolevInclusion (by linarith : (-1/2 : ℝ)≤t-1/2)
        (WeightedCoeff.meanZeroWeightedLiftCLM (Weight.sobolev (t-1/2)) (signedPairToDeleted e z)) :=
  D.realNativeInverse_full_signed_recovery t ht (nativeRealPairTarget e z hz)

theorem nativeRealPairInverse_signed_apply (D : GlobalRoughAbelianForwardData) (e : ℤ ≃ ℕ+)
    (t : ℝ) (ht : 0≤t) (z : Coeff 2 × Coeff 2) (hz : z∈Coeff.realPairLocus 2) (j : ℤ) :
    (D.signed (periodOneSobolevImageInclusion t ht (nativeRealPairInverse D e t ht z hz))).val j=
      (signedPairToDeleted e z).val j/(Weight.sobolev (t-1/2) j : ℂ) := by
  rw [nativeRealPairInverse_signed,WeightedCoeff.sobolevInclusion_apply,
    WeightedCoeff.meanZeroWeightedLift_apply]

theorem nativeRealHalfPairInverse_signed_apply (D : GlobalRoughAbelianForwardData) (e : ℤ ≃ ℕ+)
    (z : Coeff 2 × Coeff 2) (hz : z∈Coeff.realPairLocus 2) (j : ℤ) :
    (D.signed (periodOneSobolevImageInclusion (1/2) (by norm_num)
      (nativeRealPairInverse D e (1/2) (by norm_num) z hz))).val j=
        (signedPairToDeleted e z).val j := by
  rw [nativeRealPairInverse_signed_apply]
  norm_num [Weight.sobolev_apply]

theorem exists_hillNative_pair_inverse (D : GlobalRoughAbelianForwardData) (e : ℤ ≃ ℕ+)
    (t : ℝ) (ht : 0≤t) (z0 : Coeff 2 × Coeff 2) (hz0 : z0∈Coeff.realPairLocus 2) :
    ∃ U : Set (Coeff 2 × Coeff 2), IsOpen U ∧ z0∈U ∧
      ∃ Q : (Coeff 2 × Coeff 2) → WeightedCoeff (Weight.sobolev (t-1)) 2,
        AnalyticOnNhd ℂ Q U ∧
        (∀ z∈U, (Q z).val 0=0) ∧
        ∀ z∈U, ∀ hz : z∈Coeff.realPairLocus 2, Q z=nativeRealPairInverse D e t ht z hz := by
  let b := nativeRealPairTarget e z0 hz0
  obtain ⟨T,hT,hbT,G,hG,hmatch⟩ := D.realNativeInverse_has_complex_germ t ht b
  let L := WeightedCoeff.meanZeroWeightedLiftCLM (Weight.sobolev (t-1))
  let U := signedPairToDeleted e ⁻¹' T
  let Q := fun z => L (G (signedPairToDeleted e z))
  refine ⟨U,hT.preimage (signedPairToDeleted e).continuous,hbT,Q,?_,?_,?_⟩
  · intro z hz
    exact (L.analyticAt _).comp ((hG _ hz).comp ((signedPairToDeleted e).analyticAt z))
  · intro z _hz
    exact WeightedCoeff.meanZeroWeightedLift_zero _ _
  · intro z hz hzr
    exact congrArg L (hmatch (nativeRealPairTarget e z hzr) hz)

end NLS.KdV
