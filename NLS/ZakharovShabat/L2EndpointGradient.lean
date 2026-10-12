import NLS.ZakharovShabat.L2VariationKernel

/-! # Physical endpoint gradients at arbitrary L2 potentials

The fundamental-matrix kernel gives the unconjugated gradient integral
for every linear endpoint functional, at every time in the unit interval.
-/
noncomputable section
open Set Complex MeasureTheory
open NLS.LinearVolterra
namespace NLS.ZakharovShabat

/-- The adjugate formula for the physical endpoint gradient. -/
def l2EndpointGradient (u : IntervalPairL2) (z : ℂ) (v : ℂ × ℂ)
    (ℓ : (ℂ × ℂ) →L[ℂ] ℂ) (t : Icc (0 : ℝ) 1) (s : ℝ) : ℂ × ℂ :=
  let a := extend (l2SolutionCurve u z (1,0)) s
  let b := extend (l2SolutionCurve u z (0,1)) s
  let y := extend (l2SolutionCurve u z v) s
  let α := ℓ (l2SolutionCurve u z (1,0) t)
  let β := ℓ (l2SolutionCurve u z (0,1) t)
  (I*(α*b.2-β*a.2)*y.2,I*(α*b.1-β*a.1)*y.1)

theorem continuous_l2EndpointGradient (u : IntervalPairL2) (z : ℂ) (v : ℂ × ℂ)
    (ℓ : (ℂ × ℂ) →L[ℂ] ℂ) (t : Icc (0 : ℝ) 1) :
    Continuous (l2EndpointGradient u z v ℓ t) := by
  have ha := continuous_extend (l2SolutionCurve u z (1,0))
  have hb := continuous_extend (l2SolutionCurve u z (0,1))
  have hy := continuous_extend (l2SolutionCurve u z v)
  unfold l2EndpointGradient
  fun_prop

/-- The actual Fréchet derivative is the ordinary integral of the physical gradient. -/
theorem fderiv_l2Endpoint_eq_gradient_integral (u h : IntervalPairL2) (z : ℂ) (v : ℂ × ℂ)
    (ℓ : (ℂ × ℂ) →L[ℂ] ℂ) (t : Icc (0 : ℝ) 1) :
    (fderiv ℂ (fun w : IntervalPairL2 => ℓ (l2SolutionCurve w z v t)) u) h =
      ∫ s in (0 : ℝ)..t.val, (l2EndpointGradient u z v ℓ t s).1*h.ofLp.1 s+
        (l2EndpointGradient u z v ℓ t s).2*h.ofLp.2 s := by
  let a := l2SolutionCurve u z (1,0)
  let b := l2SolutionCurve u z (0,1)
  let y := l2SolutionCurve u z v
  let α := ℓ (a t)
  let β := ℓ (b t)
  let w := α • b-β • a
  have hd := (analyticOnNhd_l2SolutionCurve_potential z v u (mem_univ _)).differentiableAt.hasFDerivAt
  let ev : Curve (ℂ × ℂ) →L[ℂ] (ℂ × ℂ) := ContinuousMap.evalCLM ℂ t
  have hc := ℓ.hasFDerivAt.comp u (ev.hasFDerivAt.comp u hd)
  have he := hc.fderiv
  change fderiv ℂ (fun w : IntervalPairL2 => ℓ (l2SolutionCurve w z v t)) u = _ at he
  rw [he,ContinuousLinearMap.comp_apply,ContinuousLinearMap.comp_apply,
    fderiv_l2SolutionCurve_potential_eq_kernel]
  change ℓ (l2KernelPairing h b y t • a t-l2KernelPairing h a y t • b t) = _
  rw [map_sub,map_smul,map_smul]
  have hk : l2KernelPairing h b y t • α-l2KernelPairing h a y t • β =
      l2KernelPairing h w y t := by
    dsimp only [w]
    rw [l2KernelPairing_sub,l2KernelPairing_smul,l2KernelPairing_smul]
    change _ * α-_ * β = α*_ - β*_
    ring
  change l2KernelPairing h b y t • α-l2KernelPairing h a y t • β = _
  rw [hk,l2KernelPairing_apply]
  apply intervalIntegral.integral_congr
  intro s _
  simp only [w,l2EndpointGradient,a,b,y,α,β,NLS.LinearVolterra.extend,
    ContinuousMap.sub_apply,ContinuousMap.smul_apply,Prod.fst_sub,Prod.snd_sub,
    Prod.smul_fst,Prod.smul_snd,smul_eq_mul]
  ring

end NLS.ZakharovShabat
