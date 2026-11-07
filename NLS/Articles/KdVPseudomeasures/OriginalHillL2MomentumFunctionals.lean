import NLS.Articles.KdVPseudomeasures.OriginalHillL2NativeAnalytic
import NLS.SequenceSpaces.SignedHalfHilbertPairing
import NLS.FunctionalAnalysis.ComplexRealPullbackDerivative

/-! Original L2 momentum and actual native positive-half action energy as
FULL real Banach-analytic complex-valued quadratic forms. Their values
are real squared norms on the physical Fourier real forms. -/
noncomputable section
open Complex NLS.KdV
namespace NLS.Articles.KdVPseudomeasures

def hillL2Momentum (u : HillRealL2BanachSource) : ℂ :=
  (1/2:ℂ)*WeightedCoeff.fourierRealZeroHilbertPairing (Weight.signedSobolev 0) u u

def hillL2ActionEnergy (u : HillRealL2BanachSource) : ℂ :=
  (Real.pi:ℂ)*WeightedCoeff.fourierRealZeroHilbertPairing (Weight.signedSobolev (1/2)) (hillL2NativeMap u) (hillL2NativeMap u)

def hillL2CanonicalAction (n : ℕ+) (u : HillRealL2BanachSource) : ℂ :=
  hillHminusCanonicalAction n (hillRealMeanZeroInclusion (hillL2SourceInclusion u))

theorem hillL2Momentum_eq_half_norm_sq (u : HillRealL2BanachSource) :
    hillL2Momentum u=(((1/2:ℝ)*‖u‖^2:ℝ):ℂ) := by
  rw [hillL2Momentum,WeightedCoeff.fourierRealZeroHilbertPairing_self_eq_norm_sq _ (Weight.signedSobolev_neg 0)]
  push_cast
  ring

theorem hillL2ActionEnergy_eq_pi_norm_sq (u : HillRealL2BanachSource) :
    hillL2ActionEnergy u=((Real.pi*‖hillL2NativeMap u‖^2:ℝ):ℂ) := by
  rw [hillL2ActionEnergy,WeightedCoeff.fourierRealZeroHilbertPairing_self_eq_norm_sq _ (Weight.signedSobolev_neg (1/2))]
  push_cast
  rfl

theorem analyticAt_hillL2Momentum (u : HillRealL2BanachSource) : AnalyticAt ℝ hillL2Momentum u := by
  exact @NLS.FunctionalAnalysis.analyticAt_real_bilinear_quadratic_comp HillRealL2BanachSource HillRealL2BanachSource
    inferInstance inferInstance inferInstance inferInstance
    (WeightedCoeff.fourierRealZeroHilbertPairing (Weight.signedSobolev 0)) (1/2) (fun x => x) u analyticAt_id

theorem analyticAt_hillL2ActionEnergy (u : HillRealL2BanachSource) : AnalyticAt ℝ hillL2ActionEnergy u := by
  exact @NLS.FunctionalAnalysis.analyticAt_real_bilinear_quadratic_comp HillRealL2BanachSource HillRealSignedHalfTarget
    inferInstance inferInstance inferInstance inferInstance
    (WeightedCoeff.fourierRealZeroHilbertPairing (Weight.signedSobolev (1/2))) Real.pi hillL2NativeMap u
    (analyticAt_hillL2NativeMap u)

theorem fderiv_hillL2Momentum_apply (u h : HillRealL2BanachSource) :
    (fderiv ℝ hillL2Momentum u) h=WeightedCoeff.fourierRealZeroHilbertPairing (Weight.signedSobolev 0) u h := by
  have hd := @NLS.FunctionalAnalysis.fderiv_real_bilinear_quadratic_comp_apply HillRealL2BanachSource HillRealL2BanachSource
    inferInstance inferInstance inferInstance inferInstance
    (WeightedCoeff.fourierRealZeroHilbertPairing (Weight.signedSobolev 0)) (1/2) (fun x => x) u h differentiableAt_id
  calc
    (fderiv ℝ hillL2Momentum u) h=(1/2:ℂ)*
        (WeightedCoeff.fourierRealZeroHilbertPairing (Weight.signedSobolev 0) u h+
          WeightedCoeff.fourierRealZeroHilbertPairing (Weight.signedSobolev 0) h u) := by
      simpa only [fderiv_fun_id,ContinuousLinearMap.id_apply] using! hd
    _ = _ := by rw [WeightedCoeff.fourierRealZeroHilbertPairing_symm _ h u]; ring

theorem fderiv_hillL2ActionEnergy_apply (u h : HillRealL2BanachSource) :
    (fderiv ℝ hillL2ActionEnergy u) h=(2*Real.pi:ℂ)*
      WeightedCoeff.fourierRealZeroHilbertPairing (Weight.signedSobolev (1/2)) (hillL2NativeMap u)
        ((fderiv ℝ hillL2NativeMap u) h) := by
  have hd := @NLS.FunctionalAnalysis.fderiv_real_bilinear_quadratic_comp_apply HillRealL2BanachSource HillRealSignedHalfTarget
    inferInstance inferInstance inferInstance inferInstance
    (WeightedCoeff.fourierRealZeroHilbertPairing (Weight.signedSobolev (1/2))) Real.pi hillL2NativeMap u h
    (analyticAt_hillL2NativeMap u).differentiableAt
  calc
    (fderiv ℝ hillL2ActionEnergy u) h=(Real.pi:ℂ)*
        (WeightedCoeff.fourierRealZeroHilbertPairing (Weight.signedSobolev (1/2)) (hillL2NativeMap u) ((fderiv ℝ hillL2NativeMap u) h)+
          WeightedCoeff.fourierRealZeroHilbertPairing (Weight.signedSobolev (1/2)) ((fderiv ℝ hillL2NativeMap u) h) (hillL2NativeMap u)) := hd
    _ = _ := by
      rw [WeightedCoeff.fourierRealZeroHilbertPairing_symm _ ((fderiv ℝ hillL2NativeMap u) h) (hillL2NativeMap u)]
      ring

theorem hillL2CanonicalAction_eq_coordinates (n : ℕ+) (u : HillRealL2BanachSource) :
    hillL2CanonicalAction n u=(hillL2NativeMap u).val.val.val (n:ℤ)*(hillL2NativeMap u).val.val.val (-(n:ℤ)) := by
  rw [hillL2NativeMap_apply,hillL2NativeMap_apply,hillRealSignedMap_coordinate,hillRealSignedMap_coordinate]
  exact (hillHminusNativeComplexMap_action_identity _
    (real_mem_hillHminusActionAngleNativeDomain _ (hillL2SourceInclusion u).property) n).symm

theorem fderiv_hillL2CanonicalAction_complex_apply (n : ℕ+) (u h : HillRealL2BanachSource) :
    (fderiv ℝ (hillL2CanonicalAction n) u) h=
      (fderiv ℂ (hillHminusCanonicalAction n) (hillRealMeanZeroInclusion (hillL2SourceInclusion u)))
        (hillRealMeanZeroInclusion (hillL2SourceInclusion h)) := by
  exact @NLS.FunctionalAnalysis.fderiv_complex_real_pullback_apply PeriodOneHminusOne HillRealL2BanachSource
    inferInstance inferInstance inferInstance inferInstance inferInstance inferInstance
    (hillHminusCanonicalAction n) (hillRealMeanZeroInclusion.comp hillL2SourceInclusion) u h
    (analyticOnNhd_hillHminusCanonicalAction n _
      (real_mem_hillHminusCanonicalActionDomain _ (hillL2SourceInclusion u).property)).differentiableAt

theorem fderiv_hillL2CanonicalAction_coordinates (n : ℕ+) (u h : HillRealL2BanachSource) :
    (fderiv ℝ (hillL2CanonicalAction n) u) h=
      ((fderiv ℝ hillL2NativeMap u) h).val.val.val (n:ℤ)*(hillL2NativeMap u).val.val.val (-(n:ℤ))+
        (hillL2NativeMap u).val.val.val (n:ℤ)*((fderiv ℝ hillL2NativeMap u) h).val.val.val (-(n:ℤ)) := by
  let L := WeightedCoeff.fourierRealZeroEvalCLM (Weight.signedSobolev (1/2)) 2 (n:ℤ)
  let M := WeightedCoeff.fourierRealZeroEvalCLM (Weight.signedSobolev (1/2)) 2 (-(n:ℤ))
  have he : hillL2CanonicalAction n=(fun x => L (hillL2NativeMap x)*M (hillL2NativeMap x)) :=
    funext (hillL2CanonicalAction_eq_coordinates n)
  rw [he]
  exact @NLS.FunctionalAnalysis.fderiv_real_linear_product_comp_apply HillRealL2BanachSource HillRealSignedHalfTarget
    inferInstance inferInstance inferInstance inferInstance L M hillL2NativeMap u h
    (analyticAt_hillL2NativeMap u).differentiableAt

/-- The whole actual weighted action series equals the target quadratic
energy. Equality with the ORIGINAL momentum is proved separately. -/
theorem hasSum_hillL2CanonicalAction_energy (u : HillRealL2BanachSource) :
    HasSum (fun n : ℕ+ => ((2*Real.pi*(n:ℕ):ℝ):ℂ)*hillL2CanonicalAction n u) (hillL2ActionEnergy u) := by
  have hh := WeightedCoeff.hasSum_positive_signedHalf_energy (hillL2NativeMap u)
  have he : (fun n : ℕ+ => ((2*Real.pi*(n:ℕ):ℝ):ℂ)*hillL2CanonicalAction n u)=
      (fun n : ℕ+ => ((2*Real.pi*(n:ℕ):ℝ):ℂ)*(hillL2NativeMap u).val.val.val (n:ℤ)*(hillL2NativeMap u).val.val.val (-(n:ℤ))) := by
    funext n
    rw [hillL2CanonicalAction_eq_coordinates]
    ring
  rw [he]
  exact hh

end NLS.Articles.KdVPseudomeasures
