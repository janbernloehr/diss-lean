import NLS.FunctionalAnalysis.ForcedVolterraSolution
import NLS.ZakharovShabat.ClassicalMonodromyAnalytic

/-!
# Classical inhomogeneous spectral equations

The source for the original pencil `z-L` is `diag(i,-i) g`. The constructed
forced solution satisfies this equation on the entire closed unit interval.
Initial data enter through the same homogeneous fundamental solution.
-/

noncomputable section
open Set Complex MeasureTheory NLS.LinearVolterra
namespace NLS.ZakharovShabat

/-- The signed source map for the original pencil `z-L`. -/
def classicalSource : (ℂ × ℂ) →L[ℂ] (ℂ × ℂ) :=
  (I • ContinuousLinearMap.id ℂ ℂ).prodMap (-I • ContinuousLinearMap.id ℂ ℂ)

@[simp] theorem classicalSource_apply (g : ℂ × ℂ) : classicalSource g = (I*g.1,-I*g.2) := rfl

/-- Apply the signed spectral source map to a continuous forcing curve. -/
def classicalSourceCurve (g : Curve (ℂ × ℂ)) : Curve (ℂ × ℂ) :=
  ⟨fun t => classicalSource (g t),classicalSource.continuous.comp g.continuous⟩

/-- The initial-value solution of the actual inhomogeneous pencil equation. -/
def classicalForcedSolution (Φ : Curve (ℂ × ℂ)) (z : ℂ) (g : Curve (ℂ × ℂ)) (v : ℂ × ℂ) :
    ℝ → ℂ × ℂ := forcedSolution (classicalCoefficientCurveCLM (z,Φ)) (classicalSourceCurve g) v

@[simp] theorem classicalForcedSolution_zero (Φ : Curve (ℂ × ℂ)) (z : ℂ)
    (g : Curve (ℂ × ℂ)) (v : ℂ × ℂ) : classicalForcedSolution Φ z g v 0 = v := forcedSolution_zero _ _ _

/-- The forced solution has physical C¹ regularity, even when only the source is continuous. -/
theorem contDiff_classicalForcedSolution (Φ : Curve (ℂ × ℂ)) (z : ℂ)
    (g : Curve (ℂ × ℂ)) (v : ℂ × ℂ) : ContDiff ℝ 1 (classicalForcedSolution Φ z g v) :=
  contDiff_forcedSolution _ _ _

/-- The forced derivative has the sign dictated by the original pencil. -/
theorem hasDerivAt_classicalForcedSolution (Φ : Curve (ℂ × ℂ)) (z : ℂ)
    (g : Curve (ℂ × ℂ)) (v : ℂ × ℂ) (t : Icc (0 : ℝ) 1) :
    HasDerivAt (classicalForcedSolution Φ z g v)
      (classicalODECoefficient (Φ t) z (classicalForcedSolution Φ z g v t)+classicalSource (g t)) t :=
  hasDerivAt_forcedSolution_coe _ _ _ t

/-- The constructed forced solution satisfies `z u-Lu=g` at every point of the closed interval. -/
theorem physicalPencil_classicalForcedSolution (Φ : Curve (ℂ × ℂ)) (z : ℂ)
    (g : Curve (ℂ × ℂ)) (v : ℂ × ℂ) (t : Icc (0 : ℝ) 1) :
    z • classicalForcedSolution Φ z g v t-
      physicalOperator (extend Φ) (classicalForcedSolution Φ z g v) t = g t := by
  have h := hasDerivAt_classicalForcedSolution Φ z g v t
  simp only [physicalOperator,extend_coe,(HasFDerivAt.hasDerivAt h.fst).deriv,
    (HasFDerivAt.hasDerivAt h.snd).deriv,classicalODECoefficient_apply,classicalSource_apply,
    ContinuousLinearMap.comp_apply,ContinuousLinearMap.toSpanSingleton_apply,one_smul]
  apply Prod.ext <;> dsimp <;> ring_nf <;> simp [I_sq]

/-- The inhomogeneous physical equation determines the derivative of a differentiable vector. -/
theorem hasDerivAt_of_physicalPencil_eq {u φ : ℝ → ℂ × ℂ} {g : ℂ × ℂ} {z : ℂ} {t : ℝ}
    (h₁ : DifferentiableAt ℝ (fun s => (u s).1) t)
    (h₂ : DifferentiableAt ℝ (fun s => (u s).2) t)
    (he : z • u t-physicalOperator φ u t = g) :
    HasDerivAt u (classicalODECoefficient (φ t) z (u t)+classicalSource g) t := by
  have he₁ := congrArg Prod.fst he
  have he₂ := congrArg Prod.snd he
  change z*(u t).1-(I*deriv (fun s => (u s).1) t+(φ t).1*(u t).2) = g.1 at he₁
  change z*(u t).2-(-I*deriv (fun s => (u s).2) t+(φ t).2*(u t).1) = g.2 at he₂
  have hd := h₁.hasDerivAt.prodMk h₂.hasDerivAt
  convert! hd.congr_deriv (show (deriv (fun s => (u s).1) t,deriv (fun s => (u s).2) t) =
      classicalODECoefficient (φ t) z (u t)+classicalSource g by
    apply Prod.ext
    · dsimp [classicalODECoefficient_apply,classicalSource_apply]
      linear_combination (norm := (ring_nf; simp [I_sq])) I*he₁
    · dsimp [classicalODECoefficient_apply,classicalSource_apply]
      linear_combination (norm := (ring_nf; simp [I_sq])) -I*he₂) using 1

/-- Initial-value uniqueness also holds for absolutely continuous physical forced solutions. -/
theorem classicalForcedSolution_unique (Φ : Curve (ℂ × ℂ)) (z : ℂ)
    (g : Curve (ℂ × ℂ)) (v : ℂ × ℂ) (u : ℝ → ℂ × ℂ)
    (hu : AbsolutelyContinuousOnInterval u 0 1) (h0 : u 0 = v)
    (hd : ∀ t : Icc (0 : ℝ) 1, HasDerivAt u
      (classicalODECoefficient (Φ t) z (u t)+classicalSource (g t)) t) :
    EqOn u (classicalForcedSolution Φ z g v) (Icc 0 1) := by
  have h := forcedSolution_unique_of_ac (classicalCoefficientCurveCLM (z,Φ))
    (classicalSourceCurve g) u hu (Filter.Eventually.of_forall (fun t ht => by
      simpa only [LinearVolterra.extend,projIcc_of_mem _ ht,classicalCoefficientCurveCLM_apply,
        classicalSourceCurve,ContinuousMap.coe_mk] using hd ⟨t,ht⟩))
  simpa only [h0,classicalForcedSolution] using! h

/-- Changing the initial vector adds exactly the corresponding homogeneous solution. -/
theorem classicalForcedSolution_eq_homogeneous_add (Φ : Curve (ℂ × ℂ)) (z : ℂ)
    (g : Curve (ℂ × ℂ)) (v : ℂ × ℂ) (t : Icc (0 : ℝ) 1) :
    classicalForcedSolution Φ z g v t = classicalSolution Φ z v t+classicalForcedSolution Φ z g 0 t := by
  unfold classicalForcedSolution classicalSolution
  rw [forcedSolution_coe,forcedSolution_coe,solution_coe,
    ← realCoefficient_classicalCoefficientCurve (z,Φ),solutionCurve_eq_solutionOperator]
  simp only [forcedSolutionCurve,map_add,ContinuousMap.add_apply,
    show ContinuousMap.const (Icc (0 : ℝ) 1) (0 : ℂ × ℂ) = 0 from rfl,zero_add]

/-- The endpoint multiplier condition is a two-coordinate linear equation in the initial value. -/
theorem classicalForcedSolution_endpoint_iff (Φ : Curve (ℂ × ℂ)) (z : ℂ)
    (g : Curve (ℂ × ℂ)) (v : ℂ × ℂ) (σ : ℂ) :
    classicalForcedSolution Φ z g v 1 = σ • v ↔
      classicalSolution Φ z v 1-σ • v = -classicalForcedSolution Φ z g 0 1 := by
  rw [classicalForcedSolution_eq_homogeneous_add Φ z g v ⟨1,by constructor <;> norm_num⟩]
  constructor
  · intro h
    rw [← h]
    abel
  · intro h
    rw [sub_eq_iff_eq_add] at h
    rw [h]
    abel

end NLS.ZakharovShabat
