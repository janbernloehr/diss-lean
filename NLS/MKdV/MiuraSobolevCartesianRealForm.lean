import NLS.MKdV.MiuraSobolevCartesianLocalInverse
import NLS.MKdV.MiuraRealCartesianLocalInverse
import NLS.SequenceSpaces.PhysicalRealWeightEquivalence
import NLS.SequenceSpaces.PositiveRealWeightTransport

/-! # The genuine physical real forms of all native Cartesian Sobolev spaces -/
noncomputable section
open Set Complex NLS.ZakharovShabat NLS.FunctionalAnalysis
open scoped ENNReal ComplexConjugate
namespace NLS.MKdV

abbrev MiuraRealSobolevSource (s : ℕ) := WeightedCoeff.physicalRealSubmodule (Weight.sobolev (s : ℝ)) 2

def miuraSobolevCartesianRealSubmodule (s : ℕ) : Submodule ℝ (MiuraPositiveSobolevTarget s) :=
  miuraCartesianRealSubmodule.comap ((miuraPositiveSobolevWeightEquiv s).toContinuousLinearMap.restrictScalars ℝ).toLinearMap

abbrev MiuraRealSobolevCartesianTarget (s : ℕ) := ↥(miuraSobolevCartesianRealSubmodule s)

theorem miuraPositiveSobolevWeightEquiv_mean (s : ℕ) (z : MiuraPositiveSobolevTarget s) :
    (miuraPositiveSobolevWeightEquiv s z).2 = z.2 :=
  NLS.FunctionalAnalysis.prodCongr_refl_snd
    ((WeightedCoeff.positiveWeightEquiv (miuraCartesianWeight s) (Weight.sobolev (1/2)) 2).prodCongr
      (WeightedCoeff.positiveWeightEquiv (miuraCartesianWeight s) (Weight.sobolev (1/2)) 2)) z

/-- The transported real form is exactly coefficientwise Cartesian reality
and a real signed mean, in the inherited full native target norm. -/
theorem mem_miuraSobolevCartesianRealSubmodule_iff (s : ℕ) (z : MiuraPositiveSobolevTarget s) :
    z ∈ miuraSobolevCartesianRealSubmodule s ↔
      (∀ n, (z.1.1.val.val n).im = 0 ∧ (z.1.2.val.val n).im = 0) ∧ z.2.im = 0 := by
  change ((∀ n, ((miuraPositiveSobolevWeightEquiv s z).1.1.val.val n).im = 0 ∧
    ((miuraPositiveSobolevWeightEquiv s z).1.2.val.val n).im = 0) ∧
      (miuraPositiveSobolevWeightEquiv s z).2.im = 0) ↔ _
  rw [miuraPositiveSobolevWeightEquiv_mean]
  have hx (n : ℤ) : ((miuraPositiveSobolevWeightEquiv s z).1.1.val.val n).im = 0 ↔
      (z.1.1.val.val n).im = 0 :=
    WeightedCoeff.positiveWeightEquiv_im_zero_iff _ _ 2 z.1.1 n
  have hy (n : ℤ) : ((miuraPositiveSobolevWeightEquiv s z).1.2.val.val n).im = 0 ↔
      (z.1.2.val.val n).im = 0 :=
    WeightedCoeff.positiveWeightEquiv_im_zero_iff _ _ 2 z.1.2 n
  simp only [hx,hy]

theorem isClosed_miuraSobolevCartesianRealSubmodule (s : ℕ) :
    IsClosed (miuraSobolevCartesianRealSubmodule s : Set (MiuraPositiveSobolevTarget s)) :=
  isClosed_miuraCartesianRealSubmodule.preimage (miuraPositiveSobolevWeightEquiv s).continuous

instance miuraRealSobolevCartesianTargetComplete (s : ℕ) : CompleteSpace (MiuraRealSobolevCartesianTarget s) :=
  (isClosed_miuraSobolevCartesianRealSubmodule s).completeSpace_coe

def miuraSobolevCartesianRealWeightEquiv (s : ℕ) : MiuraRealSobolevCartesianTarget s ≃L[ℝ] MiuraRealCartesianTarget :=
  (complexEquivReal (miuraPositiveSobolevWeightEquiv s)).ofSubmodule' miuraCartesianRealSubmodule

def miuraSobolevCartesianRealProjection (s : ℕ) :
    MiuraPositiveSobolevTarget s →L[ℝ] MiuraRealSobolevCartesianTarget s :=
  (miuraSobolevCartesianRealWeightEquiv s).symm.toContinuousLinearMap.comp
    (miuraCartesianRealProjection.comp ((miuraPositiveSobolevWeightEquiv s).toContinuousLinearMap.restrictScalars ℝ))

theorem miuraSobolevCartesianRealProjection_real (s : ℕ) (z : MiuraRealSobolevCartesianTarget s) :
    miuraSobolevCartesianRealProjection s z.val = z := by
  change (miuraSobolevCartesianRealWeightEquiv s).symm
    (miuraCartesianRealProjection (miuraPositiveSobolevWeightEquiv s z.val)) = z
  have he : miuraCartesianRealProjection (miuraPositiveSobolevWeightEquiv s z.val) =
      miuraSobolevCartesianRealWeightEquiv s z :=
    miuraCartesianRealProjection_real (miuraSobolevCartesianRealWeightEquiv s z)
  rw [he,ContinuousLinearEquiv.symm_apply_apply]

/-- The original physical source and genuine real native target are
boundedly equivalent under the actual free Fourier derivative. -/
def miuraSobolevCartesianRealFreeEquiv (s : ℕ) : MiuraRealSobolevSource s ≃L[ℝ] MiuraRealSobolevCartesianTarget s :=
  ((WeightedCoeff.physicalRealWeightEquiv (Weight.sobolev (s : ℝ)) 2
    (by intro n; simp [Weight.sobolev_apply])).trans miuraCartesianRealFreeEquiv).trans
      (miuraSobolevCartesianRealWeightEquiv s).symm

theorem miuraSobolevCartesianRealFreeEquiv_inclusion (s : ℕ) (a : MiuraRealSobolevSource s) :
    (miuraSobolevCartesianRealFreeEquiv s a).val = miuraSobolevCartesianFreeEquiv s a.val := rfl

end NLS.MKdV
