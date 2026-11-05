import NLS.SequenceSpaces.PeriodOneMiuraSpatialTranslation
import NLS.KdV.HillDiscriminantGardnerGradient
import NLS.KdV.HillHminusOneMiuraOutsideShift
import NLS.ZakharovShabat.SourceSpatialTranslation
import NLS.ZakharovShabat.SourceIsospectralSet

/-! Spatial translation preserves the ENTIRE ACTUAL Hill discriminant on
the full complex Hminus-one space. Real Miura lifts give the physical
identity; verified physical-real analytic uniqueness extends it to every
complex source. No trace formula or Birkhoff covariance is assumed. -/
noncomputable section
open Set Complex NLS.ZakharovShabat NLS.ComplexAnalysis
namespace NLS.KdV

/-- The actual diagonal Miura source and actual spatial translation commute. -/
theorem hillMiuraDiagonal_spatialTranslation (t : ℝ) (u : Coeff 2) :
    sourceSpatialTranslation t (hillMiuraDiagonal u)=
      hillMiuraDiagonal (Coeff.spatialTranslation (2*Real.pi) t u) := by
  apply (CoeffPair.toMax 2).injective
  apply Prod.ext
  · change (sourceSpatialTranslation t (hillMiuraDiagonal u)).fst=
      (hillMiuraDiagonal (Coeff.spatialTranslation (2*Real.pi) t u)).fst
    rw [sourceSpatialTranslation_fst,hillMiuraDiagonal_fst,hillMiuraDiagonal_fst]
  · change (sourceSpatialTranslation t (hillMiuraDiagonal u)).snd=
      (hillMiuraDiagonal (Coeff.spatialTranslation (2*Real.pi) t u)).snd
    rw [sourceSpatialTranslation_snd,hillMiuraDiagonal_snd,hillMiuraDiagonal_snd]

/-- Literal spatial translation preserves the full original Hill trace
at EVERY energy and EVERY real Hminus-one potential. -/
theorem hillHminusDiscriminant_spatialTranslation_real
    (q : PeriodOneHminusOne) (hq : IsRealPeriodOneHminusOne q) (t : ℝ) (E : ℂ) :
    hillHminusDiscriminant (WeightedCoeff.spatialTranslation (Weight.sobolev (-1)) (2*Real.pi) t q) E=
      hillHminusDiscriminant q E := by
  let T : PeriodOneHminusOne ≃ₗᵢ[ℂ] PeriodOneHminusOne := WeightedCoeff.spatialTranslation (Weight.sobolev (-1)) (2*Real.pi) t
  obtain ⟨c,_,_,u,hu,_⟩ := exists_real_periodOneMiura_shift_outside_spectrum q hq 0
  have hv : periodOneMiura (Coeff.spatialTranslation (2*Real.pi) t u.val)=
      T q+periodOneL2Inclusion (lp.single 2 0 ((c:ℂ)^2)) := by
    rw [periodOneMiura_spatialTranslation,hu,map_add,periodOneL2Constant_spatialTranslation]
  let φ : realTypeSourceSubmodule 2 := hillMiuraRealSource u
  let ψ : realTypeSourceSubmodule 2 :=
    ⟨sourceSpatialTranslation t φ.val,sourceSpatialTranslation_realType t φ.val φ.property⟩
  have hi : ψ ∈ sourceIsospectralSet (by simp) φ :=
    ⟨sourcePeriodicSpectrum_spatialTranslation (by simp) t φ.val,
      sourcePeriodicAlgebraicMultiplicity_spatialTranslation (by simp) t φ.val⟩
  have hd := (mem_sourceIsospectralSet_iff_discriminant_eq (by simp) (by norm_num) φ ψ).mp hi
  let z := Complex.sqrt (E+(c:ℂ)^2)
  have hz : z^2-(c:ℂ)^2=E := by rw [complex_sqrt_sq]; ring
  have hleft := hillHminusDiscriminant_shifted_miura_square (T q)
    (Coeff.spatialTranslation (2*Real.pi) t u.val) ((c:ℂ)^2) z hv
  have hright := hillHminusDiscriminant_shifted_miura_square q u.val ((c:ℂ)^2) z hu
  rw [hz] at hleft hright
  rw [← hillMiuraDiagonal_spatialTranslation] at hleft
  exact hleft.trans ((congrFun hd z).trans hright.symm)

/-- The same entire-trace identity holds for ALL complex Hminus-one inputs.
The physical-real uniqueness theorem is applied on the full connected space. -/
theorem hillHminusDiscriminant_spatialTranslation
    (q : PeriodOneHminusOne) (t : ℝ) (E : ℂ) :
    hillHminusDiscriminant (WeightedCoeff.spatialTranslation (Weight.sobolev (-1)) (2*Real.pi) t q) E=
      hillHminusDiscriminant q E := by
  let T : PeriodOneHminusOne ≃ₗᵢ[ℂ] PeriodOneHminusOne := WeightedCoeff.spatialTranslation (Weight.sobolev (-1)) (2*Real.pi) t
  have hleft : AnalyticOnNhd ℂ (fun a => hillHminusDiscriminant (T a) E) univ := by
    intro a _
    exact (analyticOnNhd_hillHminusDiscriminant_source E (T a) (mem_univ _)).comp
      (T.toContinuousLinearEquiv.toContinuousLinearMap.analyticAt a)
  have he := analytic_eqOn_of_real_periodOneHminus univ isOpen_univ isPreconnected_univ
    ⟨0,mem_univ _,by intro k; simp⟩ (fun a => hillHminusDiscriminant (T a) E)
    (fun a => hillHminusDiscriminant a E) hleft (analyticOnNhd_hillHminusDiscriminant_source E)
    (fun a _ ha => hillHminusDiscriminant_spatialTranslation_real a ha t E)
  exact he (mem_univ q)

/-- The actual discriminant differential vanishes on the physical spatial
velocity of EVERY complex L2 input, viewed in the full Hminus-one norm. -/
theorem hillHminusDiscriminant_spatial_derivative_zero (u : Coeff 2) (E : ℂ) :
    (fderiv ℂ (fun q => hillHminusDiscriminant q E) (periodOneL2Inclusion u))
      (periodOneL2SpatialDerivative u)=0 := by
  have hF : HasFDerivAt (fun q => hillHminusDiscriminant q E)
      (fderiv ℂ (fun q => hillHminusDiscriminant q E) (periodOneL2Inclusion u))
      (WeightedCoeff.spatialTranslation (Weight.sobolev (-1)) (2*Real.pi) 0 (periodOneL2Inclusion u)) := by
    simpa only [WeightedCoeff.spatialTranslation_zero] using
      (analyticOnNhd_hillHminusDiscriminant_source E (periodOneL2Inclusion u)
        (mem_univ _)).differentiableAt.hasFDerivAt
  have hd := (hF.restrictScalars ℝ).comp_hasDerivAt (0:ℝ)
    (by simpa only [WeightedCoeff.spatialTranslation_zero] using
      hasDerivAt_periodOneL2Inclusion_spatialTranslation u 0)
  change HasDerivAt (fun t => hillHminusDiscriminant
    (WeightedCoeff.spatialTranslation (Weight.sobolev (-1)) (2*Real.pi) t (periodOneL2Inclusion u)) E)
    ((fderiv ℂ (fun q => hillHminusDiscriminant q E) (periodOneL2Inclusion u))
      (periodOneL2SpatialDerivative u)) 0 at hd
  simp_rw [hillHminusDiscriminant_spatialTranslation] at hd
  exact hd.unique (hasDerivAt_const 0 _)

end NLS.KdV
