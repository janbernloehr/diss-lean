import NLS.ZakharovShabat.PhysicalBirkhoffFourier
import NLS.ZakharovShabat.PhysicalBirkhoffIntrinsicProperties

/-! # Full physical linearization of the intrinsic Birkhoff map

Every original complex extension has the physical Fourier transform as its
full bounded derivative at zero. At every real input, the native real
differential agrees with the restriction of the full complex differential.
The derivative of the intrinsic global inverse at zero is exactly the
inverse physical Fourier transform.
-/

noncomputable section
open Set Complex Filter Topology NLS.ComplexAnalysis NLS.Fourier
open scoped ENNReal Classical
namespace NLS.ZakharovShabat

namespace SourceSection14OriginalData
variable {W₀ W V : Set (CoeffPair 2)} {s : (n : ℤ) → CoeffPair 2 → DeletedCoeff 2 n}
  (D : SourceSection14OriginalData (by simp) (by norm_num) W₀ W V s)
include D

/-- Every complex physical extension has the exact physical Fourier transform as its derivative at zero. -/
theorem physicalBirkhoffMap_hasFDerivAt_zero :
    HasFDerivAt (physicalBirkhoffMap s) physicalBirkhoffFourier 0 := by
  let T := (WithLp.prodContinuousLinearEquiv 2 ℂ (Coeff 2) (Coeff 2)).symm
  have h0 : (0 : CoeffPair 2) ∈ V := D.complex.real_subset
    (show IsRealType (CoeffPair.toMax 2 (0 : CoeffPair 2)) from by simp)
  have hs : HasFDerivAt (sourceBirkhoffMap (by simp) (by norm_num) s) sourceBirkhoffFourier 0 := by
    rw [← D.complex.jacobian_zero]
    exact (D.complex.analytic 0 h0).differentiableAt.hasFDerivAt
  have hi : HasFDerivAt (sourceBirkhoffMap (by simp) (by norm_num) s) sourceBirkhoffFourier
      (sourcePhysicalL2Equiv.symm 0) := by simpa only [map_zero] using hs
  have hd := T.hasFDerivAt.comp 0
    (hi.comp 0 (sourcePhysicalL2Equiv.symm.toContinuousLinearEquiv.hasFDerivAt))
  exact hd

/-- Equality of the full bounded physical derivative, not just evaluations on Fourier modes. -/
theorem physicalBirkhoffMap_fderiv_zero : fderiv ℂ (physicalBirkhoffMap s) 0 = physicalBirkhoffFourier :=
  D.physicalBirkhoffMap_hasFDerivAt_zero.fderiv

/-- The full native real differential is the restriction of every physical complex extension. -/
theorem intrinsicPhysicalBirkhoffMap_fderiv_complex (u h : physicalRealSubmodule) :
    physicalRealTargetComplex (fderiv ℝ intrinsicPhysicalBirkhoffMap u h) =
      (fderiv ℂ (physicalBirkhoffMap s) u.val) h.val := by
  have hl := physicalRealTargetComplex.hasFDerivAt.comp u
    (intrinsicPhysicalBirkhoffMap_analytic u (mem_univ _)).differentiableAt.hasFDerivAt
  have hr := ((D.physicalBirkhoffMap_analytic u.val (D.physicalBirkhoffDomain_real u)).differentiableAt.hasFDerivAt.restrictScalars ℝ).comp u
    physicalRealSubmodule.subtypeL.hasFDerivAt
  have he : (fun v => physicalRealTargetComplex (intrinsicPhysicalBirkhoffMap v)) =
      (fun v : physicalRealSubmodule => physicalBirkhoffMap s v.val) :=
    funext D.intrinsicPhysicalBirkhoffMap_complex
  change HasFDerivAt (fun v => physicalRealTargetComplex (intrinsicPhysicalBirkhoffMap v)) _ u at hl
  rw [he] at hl
  exact congrArg (fun L => L h) (hl.unique hr)

end SourceSection14OriginalData

/-- The actual real derivative at zero is completely identified by the explicit physical Fourier operator. -/
theorem intrinsicPhysicalBirkhoffMap_fderiv_zero_complex (h : physicalRealSubmodule) :
    physicalRealTargetComplex (fderiv ℝ intrinsicPhysicalBirkhoffMap 0 h) = physicalBirkhoffFourier h.val := by
  obtain ⟨W₀,W,V,s,D⟩ := sourceSection14 (p := 2) (by simp) (by norm_num)
  let A := D.toSourceSection14OriginalData
  rw [A.intrinsicPhysicalBirkhoffMap_fderiv_complex]
  change (fderiv ℂ (physicalBirkhoffMap s) 0) h.val = _
  rw [A.physicalBirkhoffMap_fderiv_zero]

/-- Both coordinates of the native real derivative are literal Fourier-integral expressions. -/
theorem intrinsicPhysicalBirkhoffMap_fderiv_zero_coordinates (h : physicalRealSubmodule) (n : ℤ) :
    (fderiv ℝ intrinsicPhysicalBirkhoffMap 0 h).fst n =
      (-(intervalFourierCoefficient 1 h.val.ofLp.1 (-n)+intervalFourierCoefficient 1 h.val.ofLp.2 n)/(Real.sqrt 2:ℂ)).re ∧
    (fderiv ℝ intrinsicPhysicalBirkhoffMap 0 h).snd n =
      ((intervalFourierCoefficient 1 h.val.ofLp.1 (-n)-intervalFourierCoefficient 1 h.val.ofLp.2 n)/((Real.sqrt 2:ℂ)*I)).re := by
  have he := intrinsicPhysicalBirkhoffMap_fderiv_zero_complex h
  have hx := congrArg (fun z : CoeffPair 2 => (z.fst n).re) he
  have hy := congrArg (fun z : CoeffPair 2 => (z.snd n).re) he
  change (fderiv ℝ intrinsicPhysicalBirkhoffMap 0 h).fst n = ((physicalBirkhoffFourier h.val).fst n).re at hx
  change (fderiv ℝ intrinsicPhysicalBirkhoffMap 0 h).snd n = ((physicalBirkhoffFourier h.val).snd n).re at hy
  rw [physicalBirkhoffFourier_fst] at hx
  rw [physicalBirkhoffFourier_snd] at hy
  exact ⟨hx,hy⟩

/-- The inverse at zero has exactly the inverse physical Fourier transform as its full differential. -/
theorem intrinsicPhysicalBirkhoffHomeomorph_symm_fderiv_zero (z : PhysicalRealBirkhoffTarget) :
    (fderiv ℝ intrinsicPhysicalBirkhoffHomeomorph.symm 0 z).val =
      physicalBirkhoffFourierEquiv.symm (physicalRealTargetComplex z) := by
  have hz : intrinsicPhysicalBirkhoffHomeomorph.symm 0 = 0 := by
    simpa only [intrinsicPhysicalBirkhoffMap_zero] using intrinsicPhysicalBirkhoffHomeomorph_left_inv 0
  have hf : HasFDerivAt intrinsicPhysicalBirkhoffMap (fderiv ℝ intrinsicPhysicalBirkhoffMap 0)
      (intrinsicPhysicalBirkhoffHomeomorph.symm 0) := by
    rw [hz]
    exact (intrinsicPhysicalBirkhoffMap_analytic 0 (mem_univ _)).differentiableAt.hasFDerivAt
  have hd := hf.comp 0
    (intrinsicPhysicalBirkhoffHomeomorph_analytic.2 0 (mem_univ _)).differentiableAt.hasFDerivAt
  have he : (fun z => intrinsicPhysicalBirkhoffMap (intrinsicPhysicalBirkhoffHomeomorph.symm z)) =
      (fun z : PhysicalRealBirkhoffTarget => z) := funext intrinsicPhysicalBirkhoffHomeomorph_right_inv
  change HasFDerivAt (fun z => intrinsicPhysicalBirkhoffMap (intrinsicPhysicalBirkhoffHomeomorph.symm z)) _ 0 at hd
  rw [he] at hd
  have hv := congrArg (fun L => L z) (hd.unique (hasFDerivAt_id (𝕜 := ℝ) (0 : PhysicalRealBirkhoffTarget)))
  have hF := intrinsicPhysicalBirkhoffMap_fderiv_zero_complex (fderiv ℝ intrinsicPhysicalBirkhoffHomeomorph.symm 0 z)
  change fderiv ℝ intrinsicPhysicalBirkhoffMap 0 (fderiv ℝ intrinsicPhysicalBirkhoffHomeomorph.symm 0 z) = z at hv
  rw [hv] at hF
  apply physicalBirkhoffFourierEquiv.injective
  rw [ContinuousLinearEquiv.apply_symm_apply]
  exact hF.symm

end NLS.ZakharovShabat
