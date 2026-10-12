import NLS.ZakharovShabat.L2EndpointGradient

/-! # Integrability and addition of physical L2 endpoint gradients -/
noncomputable section
open Set Complex MeasureTheory NLS.LinearVolterra
open scoped BoundedContinuousFunction
namespace NLS.ZakharovShabat

theorem intervalIntegrable_l2EndpointGradient_pairing (u h : IntervalPairL2) (z : ℂ) (v : ℂ × ℂ)
    (ℓ : (ℂ × ℂ) →L[ℂ] ℂ) (t : Icc (0 : ℝ) 1) :
    IntervalIntegrable (fun s => (l2EndpointGradient u z v ℓ t s).1*h.ofLp.1 s+
      (l2EndpointGradient u z v ℓ t s).2*h.ofLp.2 s) volume 0 t.val := by
  let a := l2SolutionCurve u z (1,0)
  let b := l2SolutionCurve u z (0,1)
  let y := l2SolutionCurve u z v
  let α := ℓ (a t)
  let β := ℓ (b t)
  let g₁ : ℝ →ᵇ ℂ := I • ((α • l2BoundedSecond b-β • l2BoundedSecond a)*l2BoundedSecond y)
  let g₂ : ℝ →ᵇ ℂ := I • ((α • l2BoundedFirst b-β • l2BoundedFirst a)*l2BoundedFirst y)
  have hi := (intervalIntegrable_intervalL2_mul h.fst g₁ t).add
    (intervalIntegrable_intervalL2_mul h.snd g₂ t)
  convert hi using 1
  funext s
  change _ = h.ofLp.1 s*(I*((α*(extend b s).2-β*(extend a s).2)*(extend y s).2))+
    h.ofLp.2 s*(I*((α*(extend b s).1-β*(extend a s).1)*(extend y s).1))
  dsimp [l2EndpointGradient,a,b,y,α,β]
  ring

theorem differentiableAt_l2Endpoint (u : IntervalPairL2) (z : ℂ) (v : ℂ × ℂ)
    (ℓ : (ℂ × ℂ) →L[ℂ] ℂ) (t : Icc (0 : ℝ) 1) :
    DifferentiableAt ℂ (fun w : IntervalPairL2 => ℓ (l2SolutionCurve w z v t)) u := by
  have hd := (analyticOnNhd_l2SolutionCurve_potential z v u (mem_univ _)).differentiableAt.hasFDerivAt
  let ev : Curve (ℂ × ℂ) →L[ℂ] (ℂ × ℂ) := ContinuousMap.evalCLM ℂ t
  exact (ℓ.hasFDerivAt.comp u (ev.hasFDerivAt.comp u hd)).differentiableAt

/-- Two endpoint gradients can be added inside their actual integrable pairing. -/
theorem fderiv_l2Endpoint_add_eq_gradient_integral (u h : IntervalPairL2) (z : ℂ)
    (v₁ v₂ : ℂ × ℂ) (ℓ₁ ℓ₂ : (ℂ × ℂ) →L[ℂ] ℂ) (t : Icc (0 : ℝ) 1) :
    (fderiv ℂ (fun w : IntervalPairL2 => ℓ₁ (l2SolutionCurve w z v₁ t)+
      ℓ₂ (l2SolutionCurve w z v₂ t)) u) h =
      ∫ s in (0 : ℝ)..t.val,
        (l2EndpointGradient u z v₁ ℓ₁ t s+l2EndpointGradient u z v₂ ℓ₂ t s).1*h.ofLp.1 s+
        (l2EndpointGradient u z v₁ ℓ₁ t s+l2EndpointGradient u z v₂ ℓ₂ t s).2*h.ofLp.2 s := by
  rw [fderiv_fun_add (differentiableAt_l2Endpoint u z v₁ ℓ₁ t)
    (differentiableAt_l2Endpoint u z v₂ ℓ₂ t),add_apply,
    fderiv_l2Endpoint_eq_gradient_integral,fderiv_l2Endpoint_eq_gradient_integral,
    ← intervalIntegral.integral_add (intervalIntegrable_l2EndpointGradient_pairing u h z v₁ ℓ₁ t)
      (intervalIntegrable_l2EndpointGradient_pairing u h z v₂ ℓ₂ t)]
  apply intervalIntegral.integral_congr
  intro s _
  simp only [Prod.fst_add,Prod.snd_add]
  ring

end NLS.ZakharovShabat
