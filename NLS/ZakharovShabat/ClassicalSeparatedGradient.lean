import NLS.ZakharovShabat.ClassicalDiscriminantBoundaryFlow

/-! # Actual physical gradients of the separated characteristics

The variation-of-constants kernel gives the potential gradient of every
linear endpoint functional. Specializing the initial vector and endpoint
functional recovers the original Dirichlet and Neumann characteristics.
This is the physical gradient needed to identify their source Poisson
brackets with the proved discriminant Hamiltonian variations.
-/

noncomputable section
set_option maxHeartbeats 800000
open Set Complex MeasureTheory intervalIntegral NLS.LinearVolterra
namespace NLS.ZakharovShabat
open BoundaryCondition

/-- The physical potential gradient of a linear endpoint functional. -/
def classicalEndpointGradient (Φ : Curve (ℂ × ℂ)) (z : ℂ) (v : ℂ × ℂ)
    (ℓ : (ℂ × ℂ) →L[ℂ] ℂ) (s : ℝ) : ℂ × ℂ :=
  let a := classicalSolution Φ z (1,0) s
  let b := classicalSolution Φ z (0,1) s
  let u := classicalSolution Φ z v s
  let α := ℓ (classicalSolution Φ z (1,0) 1)
  let β := ℓ (classicalSolution Φ z (0,1) 1)
  (I*(α*b.2-β*a.2)*u.2,I*(α*b.1-β*a.1)*u.1)

theorem continuous_classicalEndpointGradient (Φ : Curve (ℂ × ℂ)) (z : ℂ) (v : ℂ × ℂ)
    (ℓ : (ℂ × ℂ) →L[ℂ] ℂ) : Continuous (classicalEndpointGradient Φ z v ℓ) := by
  have ha := continuous_classicalSolution Φ z (1,0)
  have hb := continuous_classicalSolution Φ z (0,1)
  have hu := continuous_classicalSolution Φ z v
  unfold classicalEndpointGradient
  fun_prop

/-- The actual Frechet derivative of an endpoint functional is the
unconjugated integral of its constructed physical gradient. -/
theorem fderiv_classicalEndpoint_eq_gradient_integral
    (Φ H : Curve (ℂ × ℂ)) (z : ℂ) (v : ℂ × ℂ) (ℓ : (ℂ × ℂ) →L[ℂ] ℂ) :
    (fderiv ℂ (fun Ψ : Curve (ℂ × ℂ) => ℓ (classicalSolution Ψ z v 1)) Φ) H =
      ∫ s in (0 : ℝ)..1, (classicalEndpointGradient Φ z v ℓ s).1*(extend H s).1+
        (classicalEndpointGradient Φ z v ℓ s).2*(extend H s).2 := by
  let t : Icc (0 : ℝ) 1 := ⟨1,by constructor <;> norm_num⟩
  have hf : HasFDerivAt (fun Ψ : Curve (ℂ × ℂ) => classicalSolution Ψ z v t)
      (fderiv ℂ (fun Ψ : Curve (ℂ × ℂ) => classicalSolution Ψ z v t) Φ) Φ :=
    ((analyticOnNhd_classicalSolution_joint v t (z,Φ) (mem_univ _)).comp
      (f := fun Ψ : Curve (ℂ × ℂ) => (z,Ψ)) (analyticAt_const.prod analyticAt_id)).differentiableAt.hasFDerivAt
  have hl : HasFDerivAt ℓ ℓ (classicalSolution Φ z v t) := ℓ.hasFDerivAt
  have hd := (HasFDerivAt.comp (𝕜 := ℂ) (E := Curve (ℂ × ℂ)) (F := ℂ × ℂ) (G := ℂ) Φ hl hf).fderiv
  change fderiv ℂ (fun Ψ : Curve (ℂ × ℂ) => ℓ (classicalSolution Ψ z v t)) Φ = _ at hd
  rw [hd,ContinuousLinearMap.comp_apply,fderiv_classicalSolution_potential Φ H z v t]
  let g := classicalPotentialVariationSource Φ H z v
  let L : (ℂ × ℂ) →L[ℂ] ℂ :=
    ℓ (classicalSolution Φ z (1,0) 1) • ContinuousLinearMap.fst ℂ ℂ ℂ+
      ℓ (classicalSolution Φ z (0,1) 1) • ContinuousLinearMap.snd ℂ ℂ ℂ
  have hv : ℓ (classicalPotentialVariation Φ H z v 1) =
      L (∫ s in (0 : ℝ)..1, classicalForcedKernelIntegrand Φ g z s) := by
    rw [show classicalPotentialVariation Φ H z v 1 = classicalForcedKernelSolution Φ g z 1 from
      (classicalForcedKernelSolution_eq_forcedSolution Φ g z t).symm]
    simp only [classicalForcedKernelSolution,classicalForcedKernelPrimitive,map_add,map_smul,L,g,
      smul_eq_mul,smul_apply,add_apply,ContinuousLinearMap.coe_fst',ContinuousLinearMap.coe_snd']
    ring
  have hc := continuous_classicalForcedKernelIntegrand Φ g z
  rw [hv,← L.intervalIntegral_comp_comm (hc.intervalIntegrable 0 1)]
  apply intervalIntegral.integral_congr
  intro s hs
  have hs' : s ∈ Icc (0 : ℝ) 1 := by
    simpa only [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] using hs
  simp only [L,classicalForcedKernelIntegrand,g,classicalEndpointGradient,
    smul_apply,add_apply,smul_eq_mul,ContinuousLinearMap.coe_fst',ContinuousLinearMap.coe_snd',
    NLS.LinearVolterra.extend,projIcc_of_mem _ hs',classicalPotentialVariationSource_apply]
  ring

/-- The original normalized separated endpoint functional. -/
def classicalSeparatedEndpointCLM (b : BoundaryCondition) : (ℂ × ℂ) →L[ℂ] ℂ :=
  (2*I)⁻¹ • (extensionSign b • ContinuousLinearMap.snd ℂ ℂ ℂ-ContinuousLinearMap.fst ℂ ℂ ℂ)

@[simp] theorem classicalSeparatedEndpointCLM_apply (b : BoundaryCondition) (v : ℂ × ℂ) :
    classicalSeparatedEndpointCLM b v = (extensionSign b*v.2-v.1)/(2*I) := by
  simp only [classicalSeparatedEndpointCLM,smul_apply,sub_apply,smul_eq_mul,
    ContinuousLinearMap.coe_fst',ContinuousLinearMap.coe_snd',div_eq_mul_inv]
  ring

/-- The signed initial vector and endpoint functional reproduce the exact
classical characteristic, rather than a proportional normalization. -/
theorem classicalSeparatedCharacteristic_eq_endpoint (b : BoundaryCondition)
    (Φ : Curve (ℂ × ℂ)) (z : ℂ) :
    classicalSeparatedCharacteristic b Φ z =
      classicalSeparatedEndpointCLM b (classicalSolution Φ z (1,extensionSign b) 1) := by
  let t : Icc (0 : ℝ) 1 := ⟨1,by constructor <;> norm_num⟩
  rw [classicalSolution_eq_columns Φ z (1,extensionSign b) t,classicalSeparatedEndpointCLM_apply]
  simp only [classicalSeparatedCharacteristic,classicalMonodromy,classicalFundamentalMatrix,
    Prod.fst_add,Prod.snd_add,Prod.smul_fst,Prod.smul_snd,smul_eq_mul]
  dsimp
  cases b <;> simp only [extensionSign] <;> ring

/-- The actual physical separated characteristic gradient. -/
def classicalSeparatedGradient (b : BoundaryCondition) (Φ : Curve (ℂ × ℂ)) (z : ℂ) : ℝ → ℂ × ℂ :=
  classicalEndpointGradient Φ z (1,extensionSign b) (classicalSeparatedEndpointCLM b)

theorem continuous_classicalSeparatedGradient (b : BoundaryCondition)
    (Φ : Curve (ℂ × ℂ)) (z : ℂ) : Continuous (classicalSeparatedGradient b Φ z) :=
  continuous_classicalEndpointGradient _ _ _ _

/-- Both separated characteristics have their actual unconjugated physical
potential-gradient integral, with no gradient assumption. -/
theorem fderiv_classicalSeparatedCharacteristic_eq_gradient_integral
    (b : BoundaryCondition) (Φ H : Curve (ℂ × ℂ)) (z : ℂ) :
    (fderiv ℂ (fun Ψ : Curve (ℂ × ℂ) => classicalSeparatedCharacteristic b Ψ z) Φ) H =
      ∫ s in (0 : ℝ)..1, (classicalSeparatedGradient b Φ z s).1*(extend H s).1+
        (classicalSeparatedGradient b Φ z s).2*(extend H s).2 := by
  simp_rw [classicalSeparatedCharacteristic_eq_endpoint]
  exact fderiv_classicalEndpoint_eq_gradient_integral Φ H z (1,extensionSign b) (classicalSeparatedEndpointCLM b)

end NLS.ZakharovShabat
