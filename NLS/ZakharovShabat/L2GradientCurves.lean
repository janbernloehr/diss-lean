import NLS.ZakharovShabat.L2CharacteristicGradients

/-! # Physical gradient curves and continuous L2 pairings

Uniform continuity in the spectral parameter allows contour integration in
the space of continuous physical gradients. Pairing with a rough L2 direction
is a continuous linear map on that space.
-/
noncomputable section
open Set Complex MeasureTheory NLS.LinearVolterra
namespace NLS.ZakharovShabat

def l2EndpointGradientCurve (u : IntervalPairL2) (z : ℂ) (v : ℂ × ℂ)
    (ℓ : (ℂ × ℂ) →L[ℂ] ℂ) (t : Icc (0 : ℝ) 1) : Curve (ℂ × ℂ) :=
  ⟨fun s => l2EndpointGradient u z v ℓ t s,
    (continuous_l2EndpointGradient u z v ℓ t).comp continuous_subtype_val⟩

theorem continuous_l2EndpointGradientCurve_spectral (u : IntervalPairL2) (v : ℂ × ℂ)
    (ℓ : (ℂ × ℂ) →L[ℂ] ℂ) (t : Icc (0 : ℝ) 1) :
    Continuous (fun z : ℂ => l2EndpointGradientCurve u z v ℓ t) := by
  have hc (x : ℂ × ℂ) : Continuous (fun z : ℂ => l2SolutionCurve u z x) := by
    have hp : Continuous (fun z : ℂ => (z,u)) := continuous_id.prodMk continuous_const
    have h := (continuous_l2SolutionCurve_joint x).comp hp
    exact h
  apply ContinuousMap.continuous_of_continuous_uncurry
  have he (x : ℂ × ℂ) : Continuous (fun p : ℂ × Icc (0 : ℝ) 1 => l2SolutionCurve u p.1 x p.2) :=
    continuous_eval.comp (((hc x).comp continuous_fst).prodMk continuous_snd)
  have ht (x : ℂ × ℂ) : Continuous (fun p : ℂ × Icc (0 : ℝ) 1 => ℓ (l2SolutionCurve u p.1 x t)) :=
    ℓ.continuous.comp (((continuous_eval_const t).comp (hc x)).comp continuous_fst)
  change Continuous (fun p : ℂ × Icc (0 : ℝ) 1 => l2EndpointGradient u p.1 v ℓ t p.2)
  simp only [l2EndpointGradient,extend_coe]
  have h₁ := ((continuous_const (y := I)).mul (((ht (1,0)).mul (he (0,1)).snd).sub
    ((ht (0,1)).mul (he (1,0)).snd))).mul (he v).snd
  have h₂ := ((continuous_const (y := I)).mul (((ht (1,0)).mul (he (0,1)).fst).sub
    ((ht (0,1)).mul (he (1,0)).fst))).mul (he v).fst
  exact h₁.prodMk h₂

def l2DiscriminantGradientCurve (u : IntervalPairL2) (z : ℂ) : Curve (ℂ × ℂ) :=
  l2EndpointGradientCurve u z (1,0) (ContinuousLinearMap.fst ℂ ℂ ℂ) ⟨1,by norm_num⟩+
  l2EndpointGradientCurve u z (0,1) (ContinuousLinearMap.snd ℂ ℂ ℂ) ⟨1,by norm_num⟩

@[simp] theorem l2DiscriminantGradientCurve_apply (u : IntervalPairL2) (z : ℂ) (s : Icc (0 : ℝ) 1) :
    l2DiscriminantGradientCurve u z s = l2DiscriminantGradient u z s := rfl

theorem extend_l2DiscriminantGradientCurve (u : IntervalPairL2) (z : ℂ) (s : ℝ) :
    extend (l2DiscriminantGradientCurve u z) s = l2DiscriminantGradient u z s := by
  simp [NLS.LinearVolterra.extend,l2DiscriminantGradientCurve,l2EndpointGradientCurve,
    l2DiscriminantGradient,l2EndpointGradient]

theorem continuous_l2DiscriminantGradientCurve_spectral (u : IntervalPairL2) :
    Continuous (l2DiscriminantGradientCurve u) :=
  (continuous_l2EndpointGradientCurve_spectral _ _ _ _).add
    (continuous_l2EndpointGradientCurve_spectral _ _ _ _)

private def firstCurve : Curve (ℂ × ℂ) →L[ℂ] Curve ℂ :=
  ContinuousLinearMap.compLeftContinuous ℂ _ (ContinuousLinearMap.fst ℂ ℂ ℂ)
private def secondCurve : Curve (ℂ × ℂ) →L[ℂ] Curve ℂ :=
  ContinuousLinearMap.compLeftContinuous ℂ _ (ContinuousLinearMap.snd ℂ ℂ ℂ)

/-- The unconjugated integral against a fixed rough physical direction. -/
def l2GradientPairing (h : IntervalPairL2) : Curve (ℂ × ℂ) →L[ℂ] ℂ :=
  (ContinuousMap.evalCLM ℂ ⟨1,by norm_num⟩).comp
    (((l2ScalarVolterraCLM h.fst).comp firstCurve)+((l2ScalarVolterraCLM h.snd).comp secondCurve))

theorem l2GradientPairing_apply (h : IntervalPairL2) (g : Curve (ℂ × ℂ)) :
    l2GradientPairing h g = ∫ s in (0 : ℝ)..1,
      (extend g s).1*h.ofLp.1 s+(extend g s).2*h.ofLp.2 s := by
  have h₁ := intervalIntegrable_intervalL2_mul h.fst (curveBoundedExtension ℂ (firstCurve g)) ⟨1,by norm_num⟩
  have h₂ := intervalIntegrable_intervalL2_mul h.snd (curveBoundedExtension ℂ (secondCurve g)) ⟨1,by norm_num⟩
  change IntervalIntegrable (fun s => h.ofLp.1 s*(extend g s).1) volume 0 1 at h₁
  change IntervalIntegrable (fun s => h.ofLp.2 s*(extend g s).2) volume 0 1 at h₂
  change (∫ s in (0 : ℝ)..1, h.ofLp.1 s*(extend g s).1)+
    (∫ s in (0 : ℝ)..1, h.ofLp.2 s*(extend g s).2) = _
  rw [← intervalIntegral.integral_add h₁ h₂]
  apply intervalIntegral.integral_congr
  intro s _
  dsimp only
  ring

/-- This curve represents the actual physical discriminant differential. -/
theorem l2GradientPairing_discriminant (u h : IntervalPairL2) (z : ℂ) :
    l2GradientPairing h (l2DiscriminantGradientCurve u z) =
      (fderiv ℂ (fun w : IntervalPairL2 => l2Discriminant w z) u) h := by
  rw [l2GradientPairing_apply,fderiv_l2Discriminant_eq_gradient_integral]
  simp only [extend_l2DiscriminantGradientCurve]

end NLS.ZakharovShabat
