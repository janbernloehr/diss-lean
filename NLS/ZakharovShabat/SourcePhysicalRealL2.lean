import NLS.ZakharovShabat.SourcePhysicalL2Equiv
import NLS.ZakharovShabat.ClassicalAuxiliaryReality
import NLS.ZakharovShabat.SourceRealTypeBanachSpace

/-! # The physical real Hilbert source

The real subspace consists exactly of L2 pairs whose second component is
the conjugate of the first almost everywhere. The source Fourier map
restricts to a real linear isometry equivalence onto this complete space.
-/

noncomputable section
open Set MeasureTheory
open scoped ENNReal
namespace NLS.ZakharovShabat
open NLS.Fourier

/-- Physical a.e. conjugation is equivalent to the original coefficient real-type condition. -/
theorem sourcePhysicalL2_realType_iff (φ : CoeffPair 2) :
    IsClassicalRealType (intervalL2Representative (sourcePhysicalL2 φ)) ↔
      φ ∈ realTypeSourceSubmodule 2 := by
  constructor
  · intro h n
    change φ.snd n = (starRingEnd ℂ) (φ.fst (-n))
    rw [← (sourcePhysicalL2_coefficients φ n).2,← (sourcePhysicalL2_coefficients φ (-n)).1]
    calc
      _ = intervalFourierCoefficient 1 (fun x => (starRingEnd ℂ) ((sourcePhysicalL2 φ).ofLp.1 x)) n := by
        simp only [intervalFourierCoefficient_eq_fourierCoeffOn (by norm_num : (0:ℝ) < 1)]
        exact congrFun (fourierCoeffOn_congr_ae (by norm_num) h) n
      _ = _ := intervalFourierCoefficient_conj _ n
  · intro h
    have he : (sourcePhysicalL2 φ).ofLp.2 = star (sourcePhysicalL2 φ).ofLp.1 := by
      apply unitL2_ext_coefficients
      intro n
      rw [intervalFourierCoefficient_Lp_star,(sourcePhysicalL2_coefficients φ n).2,
        (sourcePhysicalL2_coefficients φ (-n)).1]
      exact h n
    change (fun x => (sourcePhysicalL2 φ).ofLp.2 x) =ᵐ[volume.restrict (Ioc 0 1)]
      (fun x => (starRingEnd ℂ) ((sourcePhysicalL2 φ).ofLp.1 x))
    rw [he]
    filter_upwards [Lp.coeFn_star (sourcePhysicalL2 φ).ofLp.1] with x hx
    exact hx

/-- The real physical L2 space, identified below by its a.e. conjugation relation. -/
def physicalRealSubmodule : Submodule ℝ IntervalPairL2 :=
  Submodule.comap (sourcePhysicalL2Equiv.symm.toLinearEquiv.restrictScalars ℝ).toLinearMap
    (realTypeSourceSubmodule 2)

/-- Membership is exactly physical real type and is independent of null-set representatives. -/
theorem mem_physicalRealSubmodule (u : IntervalPairL2) :
    u ∈ physicalRealSubmodule ↔ IsClassicalRealType (intervalL2Representative u) := by
  change sourcePhysicalL2Equiv.symm u ∈ realTypeSourceSubmodule 2 ↔ _
  rw [← sourcePhysicalL2_realType_iff,← sourcePhysicalL2Equiv_apply,
    LinearIsometryEquiv.apply_symm_apply]

/-- The physical real source equivalence preserves the exact Hilbert norm in both directions. -/
def realSourcePhysicalL2Equiv : realTypeSourceSubmodule 2 ≃ₗᵢ[ℝ] physicalRealSubmodule where
  toFun φ := ⟨sourcePhysicalL2Equiv φ.val,by
    change sourcePhysicalL2Equiv.symm (sourcePhysicalL2Equiv φ.val) ∈ realTypeSourceSubmodule 2
    simpa only [LinearIsometryEquiv.symm_apply_apply] using φ.property⟩
  invFun u := ⟨sourcePhysicalL2Equiv.symm u.val,u.property⟩
  left_inv φ := by apply Subtype.ext; exact sourcePhysicalL2Equiv.symm_apply_apply φ.val
  right_inv u := by apply Subtype.ext; exact sourcePhysicalL2Equiv.apply_symm_apply u.val
  map_add' φ ψ := by apply Subtype.ext; exact sourcePhysicalL2Equiv.map_add φ.val ψ.val
  map_smul' r φ := by
    apply Subtype.ext
    exact (sourcePhysicalL2Equiv.restrictScalars ℝ).map_smul r φ.val
  norm_map' φ := sourcePhysicalL2Equiv.norm_map φ.val

instance : CompleteSpace physicalRealSubmodule :=
  realSourcePhysicalL2Equiv.symm.toIsometryEquiv.completeSpace

end NLS.ZakharovShabat
