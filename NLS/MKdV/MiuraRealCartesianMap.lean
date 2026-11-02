import NLS.MKdV.MiuraCartesianRealForm
import NLS.ComplexAnalysis.RealAnalyticEquivalentDerivativeInverse

/-! # The actual full Cartesian map between its physical real Banach spaces -/
noncomputable section
open Set Complex NLS.ZakharovShabat
open scoped ENNReal ComplexConjugate
namespace NLS.MKdV

theorem miuraPositiveCartesianMap_physicalReal (a : Coeff.physicalRealSubmodule 2) :
    miuraPositiveCartesianMap a.val ∈ miuraCartesianRealSubmodule := by
  constructor
  · intro n
    by_cases hn : 0 < n
    · have hi : (n.toNat : ℤ) = n := Int.toNat_of_nonneg hn.le
      have hnat : 1 ≤ n.toNat := by omega
      have he := miuraL2CartesianSequence_positive a.val a.property n.toNat hnat
      rw [hi] at he
      have hr := miuraL2CartesianCoordinates_real a.val a.property n.toNat hnat
      have hx := congrArg Prod.fst he
      have hy := congrArg Prod.snd he
      change (miuraL2CartesianSequence a.val).1.val n = _ at hx
      change (miuraL2CartesianSequence a.val).2.val n = _ at hy
      change ((WeightedCoeff.positiveProjection (Weight.sobolev (1/2)) 2 (miuraL2CartesianSequence a.val).1).val.val n).im = 0 ∧
        ((WeightedCoeff.positiveProjection (Weight.sobolev (1/2)) 2 (miuraL2CartesianSequence a.val).2).val.val n).im = 0
      rw [WeightedCoeff.positiveProjection_apply,WeightedCoeff.positiveProjection_apply,if_pos hn,if_pos hn,hx,hy]
      exact hr
    · exact ⟨by rw [(miuraPositiveCartesianMap a.val).1.1.property n (by omega)]; rfl,
        by rw [(miuraPositiveCartesianMap a.val).1.2.property n (by omega)]; rfl⟩
  · change (a.val 0).im = 0
    have he := congrArg Complex.im (a.property 0)
    simp only [neg_zero,Complex.conj_im] at he
    linarith

/-- The full positive Cartesian pair and signed mean, in their genuine
closed real Hilbert target. -/
def miuraPhysicalCartesianMap (a : Coeff.physicalRealSubmodule 2) : MiuraRealCartesianTarget :=
  miuraCartesianRealProjection (miuraPositiveCartesianMap a.val)

theorem miuraPhysicalCartesianMap_inclusion (a : Coeff.physicalRealSubmodule 2) :
    (miuraPhysicalCartesianMap a).val = miuraPositiveCartesianMap a.val := by
  exact congrArg Subtype.val (miuraCartesianRealProjection_real
    ⟨miuraPositiveCartesianMap a.val,miuraPositiveCartesianMap_physicalReal a⟩)

theorem analyticAt_miuraPhysicalCartesianMap (a : Coeff.physicalRealSubmodule 2) :
    AnalyticAt ℝ miuraPhysicalCartesianMap a := by
  exact @NLS.ComplexAnalysis.analyticAt_real_linear_transport
    (Coeff.physicalRealSubmodule 2) (Coeff 2) MiuraPositiveCartesianTarget MiuraRealCartesianTarget
    inferInstance inferInstance inferInstance inferInstance inferInstance inferInstance inferInstance inferInstance
    (Coeff.physicalRealSubmodule 2).subtypeL miuraCartesianRealProjection miuraPositiveCartesianMap a
    (analyticAt_miuraPositiveCartesianMap a.val a.property)

def miuraCartesianRealFreeJacobian : Coeff.physicalRealSubmodule 2 →L[ℝ] MiuraRealCartesianTarget :=
  ((miuraCartesianFreeJacobian.restrictScalars ℝ).comp (Coeff.physicalRealSubmodule 2).subtypeL).codRestrict
    miuraCartesianRealSubmodule miuraCartesianFreeJacobian_physicalReal

def miuraCartesianRealFreeInverse : MiuraRealCartesianTarget →L[ℝ] Coeff.physicalRealSubmodule 2 :=
  ((miuraCartesianFreeInverse.restrictScalars ℝ).comp miuraCartesianRealSubmodule.subtypeL).codRestrict
    (Coeff.physicalRealSubmodule 2) miuraCartesianFreeInverse_physicalReal

def miuraCartesianRealFreeEquiv : Coeff.physicalRealSubmodule 2 ≃L[ℝ] MiuraRealCartesianTarget where
  toLinearEquiv :=
    { toLinearMap := miuraCartesianRealFreeJacobian.toLinearMap
      invFun := miuraCartesianRealFreeInverse
      left_inv := by intro a; apply Subtype.ext; exact miuraCartesianFreeInverse_jacobian a.val
      right_inv := by intro z; apply Subtype.ext; exact miuraCartesianFreeJacobian_inverse z.val }
  continuous_toFun := miuraCartesianRealFreeJacobian.continuous
  continuous_invFun := miuraCartesianRealFreeInverse.continuous

theorem fderiv_miuraPhysicalCartesianMap_zero :
    fderiv ℝ miuraPhysicalCartesianMap 0 = miuraCartesianRealFreeEquiv.toContinuousLinearMap := by
  have hzero : ∀ j : ℤ, (0 : Coeff 2) j = conj ((0 : Coeff 2) (-j)) := by intro j; simp
  have hq := @NLS.ComplexAnalysis.hasFDerivAt_real_linear_transport
    (Coeff.physicalRealSubmodule 2) (Coeff 2) MiuraPositiveCartesianTarget MiuraRealCartesianTarget
    inferInstance inferInstance inferInstance inferInstance inferInstance inferInstance inferInstance inferInstance
    (Coeff.physicalRealSubmodule 2).subtypeL miuraCartesianRealProjection miuraPositiveCartesianMap
    (0 : Coeff.physicalRealSubmodule 2) (analyticAt_miuraPositiveCartesianMap 0 hzero).differentiableAt
  have he : miuraCartesianRealProjection.comp
      (((fderiv ℂ miuraPositiveCartesianMap 0).restrictScalars ℝ).comp (Coeff.physicalRealSubmodule 2).subtypeL) =
      miuraCartesianRealFreeEquiv.toContinuousLinearMap := by
    apply ContinuousLinearMap.ext
    intro a
    exact miuraCartesianRealProjection_real (miuraCartesianRealFreeJacobian a)
  change HasFDerivAt miuraPhysicalCartesianMap (miuraCartesianRealProjection.comp
    (((fderiv ℂ miuraPositiveCartesianMap 0).restrictScalars ℝ).comp (Coeff.physicalRealSubmodule 2).subtypeL)) 0 at hq
  rw [he] at hq
  exact hq.fderiv

theorem miuraPhysicalCartesianMap_zero : miuraPhysicalCartesianMap 0 = 0 := by
  apply Subtype.ext
  rw [miuraPhysicalCartesianMap_inclusion]
  exact miuraPositiveCartesianMap_zero

end NLS.MKdV
