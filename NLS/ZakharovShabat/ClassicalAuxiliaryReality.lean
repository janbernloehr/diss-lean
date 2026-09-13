import NLS.ZakharovShabat.AuxiliaryReality
import NLS.ZakharovShabat.ClassicalAuxiliaryResolvent

/-!
# Real-type original physical potentials

The a.e. conjugation relation on the original interval passes through the
actual normalized Fourier integrals of the Neumann potential extension.
Consequently both physical auxiliary spectra are real.
-/

noncomputable section
open MeasureTheory Set NLS.Fourier
open scoped ComplexConjugate
namespace NLS.Fourier

/-- Complex conjugation reverses the index in the actual half-interval integral. -/
theorem halfCoefficient_conj (f : ℝ → ℂ) (n : ℤ) :
    halfCoefficient (fun x => (starRingEnd ℂ) (f x)) n =
      (starRingEnd ℂ) (halfCoefficient f (-n)) := by
  unfold halfCoefficient
  simp only [neg_neg, map_mul]
  have hhalf : (starRingEnd ℂ) (1/2 : ℂ) = 1/2 := by
    rw [map_div₀, map_one, show (starRingEnd ℂ) (2 : ℂ) = 2 from Complex.conj_ofReal 2]
  rw [hhalf, ← intervalIntegral.intervalIntegral_conj]
  congr 1
  apply intervalIntegral.integral_congr
  intro x _
  dsimp only
  rw [map_mul, wave_neg]

/-- The integral only depends on the a.e. function on the original interval. -/
theorem halfCoefficient_congr_ae {f g : ℝ → ℂ}
    (h : f =ᵐ[volume.restrict (Ioc 0 1)] g) (n : ℤ) : halfCoefficient f n = halfCoefficient g n := by
  unfold halfCoefficient
  congr 1
  apply intervalIntegral.integral_congr_ae_restrict
  rw [uIoc_of_le (show (0 : ℝ) ≤ 1 by norm_num)]
  filter_upwards [h] with x hx
  rw [hx]

end NLS.Fourier
namespace NLS.ZakharovShabat

/-- Physical real type on the original interval, with no constraints on representatives at null sets. -/
def IsClassicalRealType (φ : ℝ → ℂ × ℂ) : Prop :=
  (fun x => (φ x).2) =ᵐ[volume.restrict (Ioc 0 1)] (fun x => (starRingEnd ℂ) (φ x).1)

/-- Reversing the physical relation conjugates the second component back to the first. -/
theorem IsClassicalRealType.fst_eq (φ : ℝ → ℂ × ℂ) (hφ : IsClassicalRealType φ) :
    (fun x => (φ x).1) =ᵐ[volume.restrict (Ioc 0 1)] (fun x => (starRingEnd ℂ) (φ x).2) := by
  filter_upwards [hφ] with x hx
  rw [hx, starRingEnd_self_apply]

/-- Physical real type is independent of the chosen representative. -/
theorem IsClassicalRealType.congr {φ ψ : ℝ → ℂ × ℂ} (hφ : IsClassicalRealType φ)
    (h : φ =ᵐ[volume.restrict (Ioc 0 1)] ψ) : IsClassicalRealType ψ := by
  filter_upwards [hφ, h] with x hx he
  simpa only [he] using hx

/-- Passing to the actual L² class preserves physical real type. -/
theorem isClassicalRealType_intervalL2Representative_ofFunction (φ : ℝ → ℂ × ℂ)
    (hφ : MemLp φ 2 (volume.restrict (Ioc 0 1))) (hr : IsClassicalRealType φ) :
    IsClassicalRealType (intervalL2Representative (intervalL2OfFunction φ hφ)) :=
  hr.congr (intervalL2Representative_ofFunction φ hφ).symm

namespace BoundaryCondition

/-- The actual Neumann-extended Fourier coefficients of an original real-type L² potential are real type. -/
theorem isRealType_neumannPotentialCoefficients (φ : ℝ → ℂ × ℂ)
    (hφ : MemLp φ 2 (volume.restrict (Ioc 0 1))) (hr : IsClassicalRealType φ) :
    IsRealType (neumannPotentialCoefficients φ hφ) := by
  have h₁ : IntervalIntegrable (fun x => (φ x).1) volume 0 1 :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num)).mpr (hφ.fst.integrable (by norm_num))
  have h₂ : IntervalIntegrable (fun x => (φ x).2) volume 0 1 :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num)).mpr (hφ.snd.integrable (by norm_num))
  intro n
  change periodTwoCoefficient (folded (-1) (fun x => (φ x).2) (fun x => (φ x).1)) n =
    (starRingEnd ℂ) (periodTwoCoefficient (folded (-1) (fun x => (φ x).1) (fun x => (φ x).2)) (-n))
  rw [periodTwoCoefficient_folded_of_intervalIntegrable _ h₂ h₁,
    periodTwoCoefficient_folded_of_intervalIntegrable _ h₁ h₂]
  have he (k : ℤ) : halfCoefficient (fun x => (φ x).2) k =
      (starRingEnd ℂ) (halfCoefficient (fun x => (φ x).1) (-k)) :=
    (halfCoefficient_congr_ae hr k).trans (halfCoefficient_conj _ k)
  rw [he n, he (-(-n))]
  simp

/-- Proposition 5.2(iv) for eigenvalues defined by the original auxiliary endpoints and equation. -/
theorem classicalAuxiliaryEigenvalues_im_eq_zero_of_realType (b : BoundaryCondition)
    (φ : ℝ → ℂ × ℂ) (hφ : MemLp φ 2 (volume.restrict (Ioc 0 1))) (hr : IsClassicalRealType φ)
    (z : ℂ) (hz : z ∈ classicalAuxiliaryEigenvalues b φ) : z.im = 0 := by
  rw [classicalAuxiliaryEigenvalues_eq_auxiliarySpectrum b φ hφ] at hz
  exact auxiliarySpectrum_im_eq_zero_of_realType b (by simp) _ _
    (isRealType_neumannPotentialCoefficients φ hφ hr) z hz

/-- The actual closed physical auxiliary operator has real spectrum at a real-type L² potential. -/
theorem classicalAuxiliarySpectrum_im_eq_zero_of_realType (b : BoundaryCondition)
    (u : IntervalPairL2) (hr : IsClassicalRealType (intervalL2Representative u))
    (z : ℂ) (hz : z ∈ classicalAuxiliarySpectrum b u) : z.im = 0 := by
  rw [classicalAuxiliarySpectrum_eq_eigenvalues] at hz
  exact classicalAuxiliaryEigenvalues_im_eq_zero_of_realType b _ (memLp_intervalL2Representative u) hr z hz

/-- Every nonreal parameter is in the original physical auxiliary resolvent set. -/
theorem mem_classicalAuxiliaryResolventSet_of_realType_of_im_ne_zero (b : BoundaryCondition)
    (u : IntervalPairL2) (hr : IsClassicalRealType (intervalL2Representative u))
    (z : ℂ) (hz : z.im ≠ 0) : z ∈ classicalAuxiliaryResolventSet b u := by
  by_contra h
  exact hz (classicalAuxiliarySpectrum_im_eq_zero_of_realType b u hr z h)

end BoundaryCondition
end NLS.ZakharovShabat
