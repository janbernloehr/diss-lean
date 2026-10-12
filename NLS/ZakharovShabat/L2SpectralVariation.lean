import NLS.ZakharovShabat.L2KernelPairing
import NLS.ZakharovShabat.ClassicalSpectralVariation

/-! # Actual spectral derivatives and dual solution integrals in physical L2 -/
noncomputable section
open Set Complex MeasureTheory NLS.LinearVolterra
namespace NLS.ZakharovShabat

/-- Spectral differentiation of the entire uniform solution curve. -/
theorem hasDerivAt_l2SolutionCurve_spectral (u : IntervalPairL2) (z : ℂ) (v : ℂ × ℂ) :
    HasDerivAt (fun w : ℂ => l2SolutionCurve u w v) (l2VariationCurve (z,u) (1,0) v) z := by
  have hd := (analyticOnNhd_l2SolutionCurve_joint v (z,u) (mem_univ _)).differentiableAt.hasFDerivAt
  have hp : HasDerivAt (fun w : ℂ => (w,u)) ((1 : ℂ),(0 : IntervalPairL2)) z :=
    (hasDerivAt_id z).prodMk (hasDerivAt_const z u)
  have hc := hd.comp_hasDerivAt z hp
  rw [fderiv_l2SolutionCurve_joint_apply] at hc
  exact hc

theorem deriv_l2Endpoint_eq_variation (u : IntervalPairL2) (z : ℂ) (v : ℂ × ℂ)
    (ℓ : (ℂ × ℂ) →L[ℂ] ℂ) :
    deriv (fun w : ℂ => ℓ (l2SolutionCurve u w v ⟨1,by norm_num⟩)) z =
      ℓ (l2VariationCurve (z,u) (1,0) v ⟨1,by norm_num⟩) := by
  let ev : Curve (ℂ × ℂ) →L[ℂ] (ℂ × ℂ) := ContinuousMap.evalCLM ℂ ⟨1,by norm_num⟩
  exact (ℓ.hasFDerivAt.comp_hasDerivAt z
    (ev.hasFDerivAt.comp_hasDerivAt z (hasDerivAt_l2SolutionCurve_spectral u z v))).deriv

/-- The forward columns determine the endpoint-dual solution. -/
def l2EndpointDualCurve (u : IntervalPairL2) (z : ℂ) (ℓ : (ℂ × ℂ) →L[ℂ] ℂ) : Curve (ℂ × ℂ) :=
  ℓ (l2SolutionCurve u z (1,0) ⟨1,by norm_num⟩) • l2SolutionCurve u z (0,1)-
    ℓ (l2SolutionCurve u z (0,1) ⟨1,by norm_num⟩) • l2SolutionCurve u z (1,0)

theorem continuous_l2EndpointDualCurve (z : ℂ) (ℓ : (ℂ × ℂ) →L[ℂ] ℂ) :
    Continuous (fun u : IntervalPairL2 => l2EndpointDualCurve u z ℓ) := by
  have hc (v : ℂ × ℂ) : Continuous (fun u : IntervalPairL2 => l2SolutionCurve u z v) := by
    have hp : Continuous (fun u : IntervalPairL2 => (z,u)) := continuous_const.prodMk continuous_id
    have h := (continuous_l2SolutionCurve_joint v).comp hp
    exact h
  have he (v : ℂ × ℂ) : Continuous (fun u : IntervalPairL2 => ℓ (l2SolutionCurve u z v ⟨1,by norm_num⟩)) :=
    ℓ.continuous.comp ((continuous_eval_const _).comp (hc v))
  exact ((he (1,0)).smul (hc (0,1))).sub ((he (0,1)).smul (hc (1,0)))

private def firstCurve : Curve (ℂ × ℂ) →L[ℂ] Curve ℂ :=
  ContinuousLinearMap.compLeftContinuous ℂ _ (ContinuousLinearMap.fst ℂ ℂ ℂ)
private def secondCurve : Curve (ℂ × ℂ) →L[ℂ] Curve ℂ :=
  ContinuousLinearMap.compLeftContinuous ℂ _ (ContinuousLinearMap.snd ℂ ℂ ℂ)

/-- The signed bilinear integral of a dual and a forward curve. -/
def l2SpectralPairing (w y : Curve (ℂ × ℂ)) : ℂ :=
  primitive (-I • (secondCurve w*firstCurve y+firstCurve w*secondCurve y)) ⟨1,by norm_num⟩

theorem l2SpectralPairing_apply (w y : Curve (ℂ × ℂ)) :
    l2SpectralPairing w y = ∫ s in (0 : ℝ)..1,
      -I*((extend w s).2*(extend y s).1+(extend w s).1*(extend y s).2) := by
  rw [l2SpectralPairing,primitive_apply]
  rfl

theorem continuous_l2SpectralPairing :
    Continuous (fun p : Curve (ℂ × ℂ) × Curve (ℂ × ℂ) => l2SpectralPairing p.1 p.2) := by
  have h₁ : Continuous (fun p : Curve (ℂ × ℂ) × Curve (ℂ × ℂ) => secondCurve p.1*firstCurve p.2) :=
    (secondCurve.continuous.comp continuous_fst).mul (firstCurve.continuous.comp continuous_snd)
  have h₂ : Continuous (fun p : Curve (ℂ × ℂ) × Curve (ℂ × ℂ) => firstCurve p.1*secondCurve p.2) :=
    (firstCurve.continuous.comp continuous_fst).mul (secondCurve.continuous.comp continuous_snd)
  let L : Curve ℂ →L[ℂ] ℂ := (ContinuousMap.evalCLM ℂ ⟨1,by norm_num⟩).comp primitive
  exact L.continuous.comp ((h₁.add h₂).const_smul (-I))

theorem l2EndpointDualCurve_of_continuous (Φ : Curve (ℂ × ℂ)) (z : ℂ)
    (ℓ : (ℂ × ℂ) →L[ℂ] ℂ) (s : Icc (0 : ℝ) 1) :
    l2EndpointDualCurve (continuousPotentialL2Class Φ) z ℓ s =
      classicalSolution Φ z (classicalEndpointDualInitial Φ z ℓ) s := by
  rw [classicalEndpointDualSolution_eq_columns]
  simp only [l2EndpointDualCurve,l2SolutionCurve_of_continuous,ContinuousMap.sub_apply,
    ContinuousMap.smul_apply,classicalSolutionCurve_apply]

/-- The physical spectral-derivative integral holds before imposing any characteristic zero. -/
theorem deriv_l2Endpoint_eq_spectral_integral (u : IntervalPairL2) (z : ℂ) (v : ℂ × ℂ)
    (ℓ : (ℂ × ℂ) →L[ℂ] ℂ) :
    deriv (fun w : ℂ => ℓ (l2SolutionCurve u w v ⟨1,by norm_num⟩)) z =
      ∫ s in (0 : ℝ)..1, -I*((extend (l2EndpointDualCurve u z ℓ) s).2*
        (extend (l2SolutionCurve u z v) s).1+
        (extend (l2EndpointDualCurve u z ℓ) s).1*(extend (l2SolutionCurve u z v) s).2) := by
  have hc : Continuous (fun u : IntervalPairL2 => l2SolutionCurve u z v) := by
    have hp : Continuous (fun u : IntervalPairL2 => (z,u)) := continuous_const.prodMk continuous_id
    have h := (continuous_l2SolutionCurve_joint v).comp hp
    exact h
  have hl : Continuous (fun u : IntervalPairL2 => ℓ (l2VariationCurve (z,u) (1,0) v ⟨1,by norm_num⟩)) := by
    have hp : Continuous (fun u : IntervalPairL2 => ((z,u),((1 : ℂ),(0 : IntervalPairL2)))) :=
      (continuous_const.prodMk continuous_id).prodMk continuous_const
    have h := (continuous_l2VariationCurve v).comp hp
    exact ℓ.continuous.comp ((continuous_eval_const _).comp h)
  have hr : Continuous (fun u : IntervalPairL2 =>
      l2SpectralPairing (l2EndpointDualCurve u z ℓ) (l2SolutionCurve u z v)) := by
    have hp := (continuous_l2EndpointDualCurve z ℓ).prodMk hc
    have h := continuous_l2SpectralPairing.comp hp
    exact h
  have he := denseRange_continuousPotentialL2Class.equalizer hl hr (by
    funext Φ
    dsimp only [Function.comp_def]
    rw [← deriv_l2Endpoint_eq_variation]
    have hf : (fun w : ℂ => ℓ (l2SolutionCurve (continuousPotentialL2Class Φ) w v ⟨1,by norm_num⟩)) =
        (fun w : ℂ => ℓ (classicalSolution Φ w v 1)) := by
      funext w
      rw [l2SolutionCurve_of_continuous,classicalSolutionCurve_apply]
    rw [hf,deriv_classicalEndpoint_eq_spectral_integral,l2SpectralPairing_apply]
    apply intervalIntegral.integral_congr
    intro s hs
    have hs' : s ∈ Icc (0 : ℝ) 1 := by simpa only [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] using hs
    simp only [NLS.LinearVolterra.extend,projIcc_of_mem _ hs',l2EndpointDualCurve_of_continuous,
      l2SolutionCurve_of_continuous,classicalSolutionCurve_apply])
  rw [deriv_l2Endpoint_eq_variation]
  simpa only [l2SpectralPairing_apply] using congrFun he u

end NLS.ZakharovShabat
