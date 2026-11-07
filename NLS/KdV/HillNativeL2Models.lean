import NLS.KdV.HillNativeRealSignedMap
import NLS.SequenceSpaces.FourierRealZeroMultiplier
import NLS.SequenceSpaces.SpatialInverseSymbol
import NLS.SequenceSpaces.SignedSobolevSpatialGenerator
import NLS.SequenceSpaces.SobolevDerivative

/-! Genuine physical L2 and native positive-half Banach models, with
bounded inclusions, original spatial generators and bounded generator
recoveries. The source Sobolev1+abs(k) and signed max(1,abs(k)) brackets
remain distinct. All raw coefficients are retained. -/
noncomputable section
open Complex
namespace NLS.KdV

abbrev HillRealL2BanachSource := WeightedCoeff.fourierRealZeroSubmodule (Weight.signedSobolev 0) 2
abbrev HillRealSignedHalfTarget := WeightedCoeff.fourierRealZeroSubmodule (Weight.signedSobolev (1/2)) 2

private theorem generator_conj (k : ℤ) :
    I*((2*Real.pi*((-k:ℤ):ℝ):ℝ):ℂ)=(starRingEnd ℂ) (I*((2*Real.pi*k:ℝ):ℂ)) := by
  simp only [map_mul,Int.cast_neg,Complex.conj_I,Complex.conj_ofReal]
  push_cast
  ring

private theorem source_inclusion_bound (k : ℤ) :
    Weight.sobolev (-1) k*‖(1:ℂ)‖ ≤ 1*Weight.signedSobolev 0 k := by
  have h := Weight.sobolev_mono (by norm_num : (-1:ℝ) ≤ 0) k
  simpa only [norm_one,mul_one,one_mul,Weight.sobolev_apply,Weight.signedSobolev,
    Real.rpow_zero] using h

private theorem source_generator_bound (k : ℤ) :
    Weight.sobolev (-1) k*‖I*((2*Real.pi*k:ℝ):ℂ)‖ ≤ (2*Real.pi)*Weight.signedSobolev 0 k := by
  have h := Weight.signedSobolev_spatialGenerator_bound (-1) k
  rw [show (-1:ℝ)+1=0 by norm_num] at h
  have hc := (Weight.signedSobolev_negative_bounds 1 (by norm_num) k).1
  exact (mul_le_mul_of_nonneg_right hc (norm_nonneg _)).trans h

private theorem target_inclusion_bound (k : ℤ) :
    Weight.signedSobolev (-1/2) k*‖(1:ℂ)‖ ≤ 1*Weight.signedSobolev (1/2) k := by
  simp only [norm_one,mul_one,one_mul]
  exact Real.rpow_le_rpow_of_exponent_le (le_max_left (1:ℝ) |(k:ℝ)|) (by norm_num)

private theorem target_generator_bound (k : ℤ) :
    Weight.signedSobolev (-1/2) k*‖I*((2*Real.pi*k:ℝ):ℂ)‖ ≤ (2*Real.pi)*Weight.signedSobolev (1/2) k := by
  have h := Weight.signedSobolev_spatialGenerator_bound (-1/2) k
  rwa [show (-1/2:ℝ)+1=1/2 by norm_num] at h

private theorem target_recovery_bound (k : ℤ) :
    Weight.signedSobolev (1/2) k*‖spatialInverseSymbol k‖ ≤ (1/(2*Real.pi))*Weight.signedSobolev (-1/2) k := by
  have h := Weight.signedSobolev_spatialInverse_bound (-1/2) k
  rwa [show (-1/2:ℝ)+1=1/2 by norm_num] at h

def hillL2SourceInclusion : HillRealL2BanachSource →L[ℝ] HillRealMeanZeroSource :=
  WeightedCoeff.fourierRealZeroMultiplier _ _ (Weight.sobolev_neg (-1)) (fun _ => 1) 1 zero_le_one
    source_inclusion_bound (by intro k; simp)

def hillL2SourceSpatialGenerator : HillRealL2BanachSource →L[ℝ] HillRealMeanZeroSource :=
  WeightedCoeff.fourierRealZeroMultiplier _ _ (Weight.sobolev_neg (-1))
    (fun k => I*((2*Real.pi*k:ℝ):ℂ)) (2*Real.pi) (by positivity) source_generator_bound generator_conj

def hillL2SourceSpatialRecovery : HillRealMeanZeroSource →L[ℝ] HillRealL2BanachSource :=
  WeightedCoeff.fourierRealZeroMultiplier _ _ (Weight.signedSobolev_neg 0)
    spatialInverseSymbol (1/Real.pi) (by positivity) Weight.sobolev_spatialInverse_to_zero_bound spatialInverseSymbol_neg

def hillSignedHalfInclusion : HillRealSignedHalfTarget →L[ℝ] HillRealSignedTarget :=
  WeightedCoeff.fourierRealZeroMultiplier _ _ (Weight.signedSobolev_neg (-1/2)) (fun _ => 1) 1 zero_le_one
    target_inclusion_bound (by intro k; simp)

def hillSignedHalfSpatialGenerator : HillRealSignedHalfTarget →L[ℝ] HillRealSignedTarget :=
  WeightedCoeff.fourierRealZeroMultiplier _ _ (Weight.signedSobolev_neg (-1/2))
    (fun k => I*((2*Real.pi*k:ℝ):ℂ)) (2*Real.pi) (by positivity) target_generator_bound generator_conj

def hillSignedHalfSpatialRecovery : HillRealSignedTarget →L[ℝ] HillRealSignedHalfTarget :=
  WeightedCoeff.fourierRealZeroMultiplier _ _ (Weight.signedSobolev_neg (1/2))
    spatialInverseSymbol (1/(2*Real.pi)) (by positivity) target_recovery_bound spatialInverseSymbol_neg

theorem hillL2SourceInclusion_apply (u : HillRealL2BanachSource) (k : ℤ) :
    (hillL2SourceInclusion u).val.val.val k=u.val.val.val k := by
  rw [hillL2SourceInclusion,WeightedCoeff.fourierRealZeroMultiplier_apply,one_mul]

theorem hillL2SourceSpatialGenerator_apply (u : HillRealL2BanachSource) (k : ℤ) :
    (hillL2SourceSpatialGenerator u).val.val.val k=I*((2*Real.pi*k:ℝ):ℂ)*u.val.val.val k :=
  WeightedCoeff.fourierRealZeroMultiplier_apply _ _ _ _ _ _ _ _ u k

theorem hillL2SourceSpatialRecovery_apply (v : HillRealMeanZeroSource) (k : ℤ) :
    (hillL2SourceSpatialRecovery v).val.val.val k=spatialInverseSymbol k*v.val.val.val k :=
  WeightedCoeff.fourierRealZeroMultiplier_apply _ _ _ _ _ _ _ _ v k

theorem hillSignedHalfInclusion_apply (z : HillRealSignedHalfTarget) (k : ℤ) :
    (hillSignedHalfInclusion z).val.val.val k=z.val.val.val k := by
  rw [hillSignedHalfInclusion,WeightedCoeff.fourierRealZeroMultiplier_apply,one_mul]

theorem hillSignedHalfSpatialGenerator_apply (z : HillRealSignedHalfTarget) (k : ℤ) :
    (hillSignedHalfSpatialGenerator z).val.val.val k=I*((2*Real.pi*k:ℝ):ℂ)*z.val.val.val k :=
  WeightedCoeff.fourierRealZeroMultiplier_apply _ _ _ _ _ _ _ _ z k

theorem hillSignedHalfSpatialRecovery_apply (v : HillRealSignedTarget) (k : ℤ) :
    (hillSignedHalfSpatialRecovery v).val.val.val k=spatialInverseSymbol k*v.val.val.val k :=
  WeightedCoeff.fourierRealZeroMultiplier_apply _ _ _ _ _ _ _ _ v k

theorem norm_hillL2SourceInclusion_le (u : HillRealL2BanachSource) : ‖hillL2SourceInclusion u‖ ≤ ‖u‖ := by
  simpa only [hillL2SourceInclusion,one_mul] using WeightedCoeff.norm_fourierRealZeroMultiplier_le
    (Weight.signedSobolev 0) (Weight.sobolev (-1)) (Weight.sobolev_neg (-1))
    (fun _ => 1) 1 zero_le_one source_inclusion_bound (by intro k; simp) u

theorem norm_hillL2SourceSpatialGenerator_le (u : HillRealL2BanachSource) :
    ‖hillL2SourceSpatialGenerator u‖ ≤ (2*Real.pi)*‖u‖ :=
  WeightedCoeff.norm_fourierRealZeroMultiplier_le _ _ _ _ _ _ _ _ u

theorem norm_hillL2SourceSpatialRecovery_le (v : HillRealMeanZeroSource) :
    ‖hillL2SourceSpatialRecovery v‖ ≤ (1/Real.pi)*‖v‖ :=
  WeightedCoeff.norm_fourierRealZeroMultiplier_le _ _ _ _ _ _ _ _ v

theorem norm_hillSignedHalfInclusion_le (z : HillRealSignedHalfTarget) : ‖hillSignedHalfInclusion z‖ ≤ ‖z‖ := by
  simpa only [hillSignedHalfInclusion,one_mul] using WeightedCoeff.norm_fourierRealZeroMultiplier_le
    (Weight.signedSobolev (1/2)) (Weight.signedSobolev (-1/2)) (Weight.signedSobolev_neg (-1/2))
    (fun _ => 1) 1 zero_le_one target_inclusion_bound (by intro k; simp) z

theorem norm_hillSignedHalfSpatialGenerator_le (z : HillRealSignedHalfTarget) :
    ‖hillSignedHalfSpatialGenerator z‖ ≤ (2*Real.pi)*‖z‖ :=
  WeightedCoeff.norm_fourierRealZeroMultiplier_le _ _ _ _ _ _ _ _ z

theorem norm_hillSignedHalfSpatialRecovery_le (v : HillRealSignedTarget) :
    ‖hillSignedHalfSpatialRecovery v‖ ≤ (1/(2*Real.pi))*‖v‖ :=
  WeightedCoeff.norm_fourierRealZeroMultiplier_le _ _ _ _ _ _ _ _ v

theorem hillL2SourceInclusion_injective : Function.Injective hillL2SourceInclusion := by
  intro u v h
  apply Subtype.ext
  apply Subtype.ext
  apply Subtype.ext
  funext k
  have he := congrArg (fun a : HillRealMeanZeroSource => a.val.val.val k) h
  simpa only [hillL2SourceInclusion_apply] using he

theorem hillSignedHalfInclusion_injective : Function.Injective hillSignedHalfInclusion := by
  intro u v h
  apply Subtype.ext
  apply Subtype.ext
  apply Subtype.ext
  funext k
  have he := congrArg (fun a : HillRealSignedTarget => a.val.val.val k) h
  simpa only [hillSignedHalfInclusion_apply] using he

theorem hillL2SourceSpatialRecovery_generator_eq (u : HillRealL2BanachSource) :
    hillL2SourceSpatialRecovery (hillL2SourceSpatialGenerator u)=u := by
  apply Subtype.ext
  apply Subtype.ext
  apply Subtype.ext
  funext k
  rw [hillL2SourceSpatialRecovery_apply,hillL2SourceSpatialGenerator_apply,spatialInverseSymbol_generator]
  split_ifs with hk
  · subst k
    exact u.val.property.symm
  · rfl

theorem hillSignedHalfSpatialRecovery_generator_eq (z : HillRealSignedHalfTarget) :
    hillSignedHalfSpatialRecovery (hillSignedHalfSpatialGenerator z)=z := by
  apply Subtype.ext
  apply Subtype.ext
  apply Subtype.ext
  funext k
  rw [hillSignedHalfSpatialRecovery_apply,hillSignedHalfSpatialGenerator_apply,spatialInverseSymbol_generator]
  split_ifs with hk
  · subst k
    exact z.val.property.symm
  · rfl

theorem hillL2SourceInclusion_recovery_eq (q v : HillRealMeanZeroSource)
    (hv : ∀ k : ℤ, v.val.val.val k=I*((2*Real.pi*k:ℝ):ℂ)*q.val.val.val k) :
    hillL2SourceInclusion (hillL2SourceSpatialRecovery v)=q := by
  apply Subtype.ext
  apply Subtype.ext
  apply Subtype.ext
  funext k
  rw [hillL2SourceInclusion_apply,hillL2SourceSpatialRecovery_apply,hv,spatialInverseSymbol_generator]
  split_ifs with hk
  · subst k
    exact q.val.property.symm
  · rfl

theorem hillSignedHalfInclusion_recovery_eq (a v : HillRealSignedTarget)
    (hv : ∀ k : ℤ, v.val.val.val k=I*((2*Real.pi*k:ℝ):ℂ)*a.val.val.val k) :
    hillSignedHalfInclusion (hillSignedHalfSpatialRecovery v)=a := by
  apply Subtype.ext
  apply Subtype.ext
  apply Subtype.ext
  funext k
  rw [hillSignedHalfInclusion_apply,hillSignedHalfSpatialRecovery_apply,hv,spatialInverseSymbol_generator]
  split_ifs with hk
  · subst k
    exact a.val.property.symm
  · rfl

def hillL2SourceCoefficients : HillRealL2BanachSource →L[ℝ] Coeff 2 :=
  ((WeightedCoeff.weightIsometry (Weight.signedSobolev 0) 2).toContinuousLinearEquiv.toContinuousLinearMap.restrictScalars ℝ).comp
    (((WeightedCoeff.zeroModeSubmodule (Weight.signedSobolev 0) 2).subtypeL.restrictScalars ℝ).comp
      (WeightedCoeff.fourierRealZeroSubmodule (Weight.signedSobolev 0) 2).subtypeL)

theorem hillL2SourceCoefficients_apply (u : HillRealL2BanachSource) (k : ℤ) :
    hillL2SourceCoefficients u k=u.val.val.val k := by
  change (Weight.signedSobolev 0 k:ℂ)*u.val.val.val k= _
  simp [Weight.signedSobolev]

theorem norm_hillL2SourceCoefficients (u : HillRealL2BanachSource) : ‖hillL2SourceCoefficients u‖=‖u‖ := by
  change ‖WeightedCoeff.weightIsometry (Weight.signedSobolev 0) 2 u.val.val‖=‖u.val.val‖
  exact (WeightedCoeff.weightIsometry (Weight.signedSobolev 0) 2).norm_map _

end NLS.KdV
