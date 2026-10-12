import NLS.ZakharovShabat.L2EndpointGradientCalculus
import NLS.ZakharovShabat.L2CharacteristicCotangents
import NLS.ZakharovShabat.ClassicalSeparatedGradient

/-! # Physical L2 gradients of the spectral characteristics

The trace, off-diagonal sum, and both source-normalized separated
characteristics have their actual unconjugated gradient integrals at
arbitrary physical L2 potentials and in arbitrary L2 directions.
-/
noncomputable section
open Set Complex MeasureTheory NLS.LinearVolterra
namespace NLS.ZakharovShabat
open BoundaryCondition

/-- The physical gradient of the monodromy trace. -/
def l2DiscriminantGradient (u : IntervalPairL2) (z : ℂ) (s : ℝ) : ℂ × ℂ :=
  l2EndpointGradient u z (1,0) (ContinuousLinearMap.fst ℂ ℂ ℂ) ⟨1,by norm_num⟩ s+
  l2EndpointGradient u z (0,1) (ContinuousLinearMap.snd ℂ ℂ ℂ) ⟨1,by norm_num⟩ s

/-- The physical gradient of the established off-diagonal sum. -/
def l2AntiDiscriminantGradient (u : IntervalPairL2) (z : ℂ) (s : ℝ) : ℂ × ℂ :=
  l2EndpointGradient u z (0,1) (ContinuousLinearMap.fst ℂ ℂ ℂ) ⟨1,by norm_num⟩ s+
  l2EndpointGradient u z (1,0) (ContinuousLinearMap.snd ℂ ℂ ℂ) ⟨1,by norm_num⟩ s

/-- The separated gradient retains both original endpoint signs and the sine normalization. -/
def l2SeparatedGradient (b : BoundaryCondition) (u : IntervalPairL2) (z : ℂ) : ℝ → ℂ × ℂ :=
  l2EndpointGradient u z (1,extensionSign b) (classicalSeparatedEndpointCLM b) ⟨1,by norm_num⟩

theorem l2SeparatedCharacteristic_eq_endpoint (b : BoundaryCondition) (u : IntervalPairL2) (z : ℂ) :
    l2SeparatedCharacteristic b u z =
      classicalSeparatedEndpointCLM b
        (l2SolutionCurve u z (1,extensionSign b) ⟨1,by norm_num⟩) := by
  rw [classicalSeparatedEndpointCLM_apply,l2SolutionCurve_linearCombination]
  simp only [l2SeparatedCharacteristic,l2Monodromy,l2FundamentalMatrix,
    ContinuousMap.add_apply,ContinuousMap.smul_apply,
    Prod.fst_add,Prod.snd_add,Prod.smul_fst,Prod.smul_snd,smul_eq_mul,one_mul,Matrix.of_apply,
    Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_fin_one]
  cases b <;> simp only [extensionSign] <;> ring

theorem fderiv_l2Discriminant_eq_gradient_integral (u h : IntervalPairL2) (z : ℂ) :
    (fderiv ℂ (fun w : IntervalPairL2 => l2Discriminant w z) u) h =
      ∫ s in (0 : ℝ)..1, (l2DiscriminantGradient u z s).1*h.ofLp.1 s+
        (l2DiscriminantGradient u z s).2*h.ofLp.2 s := by
  have he : (fun w : IntervalPairL2 => l2Discriminant w z) =
      (fun w : IntervalPairL2 => (l2SolutionCurve w z (1,0) ⟨1,by norm_num⟩).1+
        (l2SolutionCurve w z (0,1) ⟨1,by norm_num⟩).2) := by
    funext w
    simp only [l2Discriminant,Matrix.trace_fin_two,l2Monodromy,l2FundamentalMatrix]
    rfl
  rw [he]
  exact fderiv_l2Endpoint_add_eq_gradient_integral u h z (1,0) (0,1)
    (ContinuousLinearMap.fst ℂ ℂ ℂ) (ContinuousLinearMap.snd ℂ ℂ ℂ) _

theorem fderiv_l2AntiDiscriminant_eq_gradient_integral (u h : IntervalPairL2) (z : ℂ) :
    (fderiv ℂ (fun w : IntervalPairL2 => l2AntiDiscriminant w z) u) h =
      ∫ s in (0 : ℝ)..1, (l2AntiDiscriminantGradient u z s).1*h.ofLp.1 s+
        (l2AntiDiscriminantGradient u z s).2*h.ofLp.2 s :=
  fderiv_l2Endpoint_add_eq_gradient_integral u h z (0,1) (1,0)
    (ContinuousLinearMap.fst ℂ ℂ ℂ) (ContinuousLinearMap.snd ℂ ℂ ℂ) _

theorem fderiv_l2SeparatedCharacteristic_eq_gradient_integral (b : BoundaryCondition)
    (u h : IntervalPairL2) (z : ℂ) :
    (fderiv ℂ (fun w : IntervalPairL2 => l2SeparatedCharacteristic b w z) u) h =
      ∫ s in (0 : ℝ)..1, (l2SeparatedGradient b u z s).1*h.ofLp.1 s+
        (l2SeparatedGradient b u z s).2*h.ofLp.2 s := by
  simp_rw [l2SeparatedCharacteristic_eq_endpoint]
  exact fderiv_l2Endpoint_eq_gradient_integral u h z (1,extensionSign b) (classicalSeparatedEndpointCLM b) _

theorem continuous_l2DiscriminantGradient (u : IntervalPairL2) (z : ℂ) :
    Continuous (l2DiscriminantGradient u z) :=
  (continuous_l2EndpointGradient _ _ _ _ _).add (continuous_l2EndpointGradient _ _ _ _ _)

theorem continuous_l2AntiDiscriminantGradient (u : IntervalPairL2) (z : ℂ) :
    Continuous (l2AntiDiscriminantGradient u z) :=
  (continuous_l2EndpointGradient _ _ _ _ _).add (continuous_l2EndpointGradient _ _ _ _ _)

theorem continuous_l2SeparatedGradient (b : BoundaryCondition) (u : IntervalPairL2) (z : ℂ) :
    Continuous (l2SeparatedGradient b u z) := continuous_l2EndpointGradient _ _ _ _ _

end NLS.ZakharovShabat
