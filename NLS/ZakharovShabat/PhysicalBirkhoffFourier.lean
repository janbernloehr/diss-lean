import NLS.ZakharovShabat.SourceBirkhoffFourierEquivalence
import NLS.ZakharovShabat.SourcePhysicalL2Equiv

/-! # The physical Birkhoff Fourier isometry

The signed transform is expressed using the actual unit-interval Fourier
integrals. Its first component reverses frequency and both components retain
the original square-root-two and imaginary factors. The transform and its
inverse preserve the exact complex Hilbert pair norm.
-/

noncomputable section
open Set Complex Filter Topology NLS.ComplexAnalysis NLS.Fourier
open scoped ENNReal Classical
namespace NLS.ZakharovShabat

/-- The signed Fourier transform between the original physical and target Hilbert spaces. -/
def physicalBirkhoffFourierEquiv : IntervalPairL2 ≃L[ℂ] CoeffPair 2 :=
  (sourcePhysicalL2Equiv.symm.toContinuousLinearEquiv.trans sourceBirkhoffFourierEquiv).trans
    (WithLp.prodContinuousLinearEquiv 2 ℂ (Coeff 2) (Coeff 2)).symm

/-- The normalized physical Fourier transform as a bounded complex linear operator. -/
def physicalBirkhoffFourier : IntervalPairL2 →L[ℂ] CoeffPair 2 :=
  physicalBirkhoffFourierEquiv.toContinuousLinearMap

/-- The first coordinate uses the actual physical Fourier integral with a reflected first index. -/
theorem physicalBirkhoffFourier_fst (h : IntervalPairL2) (n : ℤ) :
    (physicalBirkhoffFourier h).fst n =
      -(intervalFourierCoefficient 1 h.ofLp.1 (-n)+intervalFourierCoefficient 1 h.ofLp.2 n)/(Real.sqrt 2:ℂ) := by
  change (sourceBirkhoffFourier (sourcePhysicalL2Equiv.symm h)).1 n = _
  rw [sourceBirkhoffFourier_fst,sourcePhysicalL2Equiv_symm_fst,sourcePhysicalL2Equiv_symm_snd]

/-- The second coordinate has the fixed positive-sine convention and its exact imaginary factor. -/
theorem physicalBirkhoffFourier_snd (h : IntervalPairL2) (n : ℤ) :
    (physicalBirkhoffFourier h).snd n =
      (intervalFourierCoefficient 1 h.ofLp.1 (-n)-intervalFourierCoefficient 1 h.ofLp.2 n)/((Real.sqrt 2:ℂ)*I) := by
  change (sourceBirkhoffFourier (sourcePhysicalL2Equiv.symm h)).2 n = _
  rw [sourceBirkhoffFourier_snd,sourcePhysicalL2Equiv_symm_fst,sourcePhysicalL2Equiv_symm_snd]

/-- The normalization preserves the full complex physical Hilbert norm. -/
theorem physicalBirkhoffFourier_norm (h : IntervalPairL2) : ‖physicalBirkhoffFourier h‖ = ‖h‖ := by
  let a := sourcePhysicalL2Equiv.symm h
  have hx : (physicalBirkhoffFourier h).fst =
      ((-1:ℂ)/(Real.sqrt 2:ℂ)) • (Coeff.reflection a.fst+a.snd) := rfl
  have hy : (physicalBirkhoffFourier h).snd =
      ((1:ℂ)/((Real.sqrt 2:ℂ)*I)) • (Coeff.reflection a.fst-a.snd) := rfl
  have hq : ‖(-1:ℂ)/(Real.sqrt 2:ℂ)‖ = 1/Real.sqrt 2 := by
    simp [Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (Real.sqrt_nonneg 2)]
  have hi : ‖(1:ℂ)/((Real.sqrt 2:ℂ)*I)‖ = 1/Real.sqrt 2 := by
    simp [Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (Real.sqrt_nonneg 2)]
  have hp := parallelogram_law_with_norm ℂ (Coeff.reflection a.fst) a.snd
  rw [Coeff.reflection.norm_map] at hp
  have ha : ‖h‖^2 = ‖a.fst‖^2+‖a.snd‖^2 := by
    rw [← sourcePhysicalL2Equiv.symm.norm_map h,WithLp.prod_norm_sq_eq_of_L2]
  have hs : (Real.sqrt 2)^2 = 2 := Real.sq_sqrt (by norm_num)
  have he : ‖physicalBirkhoffFourier h‖^2 = ‖h‖^2 := by
    rw [WithLp.prod_norm_sq_eq_of_L2,hx,hy,norm_smul,norm_smul,hq,hi,
      mul_pow,mul_pow,div_pow,one_pow,hs,ha]
    nlinarith [hp]
  nlinarith [norm_nonneg (physicalBirkhoffFourier h),norm_nonneg h]

/-- The physical Fourier transform is an isometry equivalence of the original complex Hilbert spaces. -/
def physicalBirkhoffFourierIsometryEquiv : IntervalPairL2 ≃ₗᵢ[ℂ] CoeffPair 2 :=
  { physicalBirkhoffFourierEquiv.toLinearEquiv with norm_map' := physicalBirkhoffFourier_norm }

/-- The inverse physical Fourier transform also preserves the exact Hilbert norm. -/
theorem physicalBirkhoffFourierEquiv_symm_norm (z : CoeffPair 2) :
    ‖physicalBirkhoffFourierEquiv.symm z‖ = ‖z‖ := by
  have h := physicalBirkhoffFourier_norm (physicalBirkhoffFourierEquiv.symm z)
  change ‖physicalBirkhoffFourierEquiv (physicalBirkhoffFourierEquiv.symm z)‖ = _ at h
  rw [ContinuousLinearEquiv.apply_symm_apply] at h
  exact h.symm

end NLS.ZakharovShabat
