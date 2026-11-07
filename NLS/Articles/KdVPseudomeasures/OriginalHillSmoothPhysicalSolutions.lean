import NLS.Articles.KdVPseudomeasures.OriginalHillSmoothPDEUniqueness
import NLS.Articles.KdVPseudomeasures.OriginalHillRoughCanonicalTrajectories

/-! Literal pointwise physical KdV solutions in the genuine H4/H1
strong source models. Their physical Fourier equation is DERIVED from
the pointwise PDE, and they have global existence and uniqueness.
Every rough-convergent family of their initial data gives uniform
compact-time convergence of the actual physical solution trajectories. -/
noncomputable section
open Set Complex Filter Topology NLS.KdV NLS.WeightedCoeff NLS.ZakharovShabat NLS.Fourier
open scoped ContDiff
namespace NLS.Articles.KdVPseudomeasures

def hillPhysicalH4Synthesis (q : RealSignedHilbert (signedStepOrder 0 4)) (x : ℝ) : ℂ :=
  periodOneSobolevSynthesis (signedOneRealToScalarDomain (hillIntegerSourceOrderInclusion 1 4 (by decide) q))
    (x : AddCircle (2:ℝ))

def HillSmoothStrongKdVSolution (γ : ℝ → RealSignedHilbert (signedStepOrder 0 4)) : Prop :=
  (∀ t, ContDiff ℝ ∞ (hillPhysicalH4Synthesis (γ t))) ∧
  (∀ t, ∃ v : RealSignedHilbert (signedStepOrder 0 1),
    HasDerivAt (fun r : ℝ => hillIntegerSourceOrderInclusion 1 4 (by decide) (γ r)) v t) ∧
  ∀ t x, HasDerivAt (fun r : ℝ => hillPhysicalH4Synthesis (γ r) x)
    (classicalKdVVectorField (hillPhysicalH4Synthesis (γ t)) x) t

theorem hillSmoothPhysicalDerivative_coefficients
    (γ : ℝ → RealSignedHilbert (signedStepOrder 0 4))
    (v : ℝ → RealSignedHilbert (signedStepOrder 0 1))
    (hd : ∀ t, HasDerivAt (fun r : ℝ => hillIntegerSourceOrderInclusion 1 4 (by decide) (γ r)) (v t) t)
    (hPDE : ∀ t x, HasDerivAt (fun r : ℝ => hillPhysicalH4Synthesis (γ r) x)
      (classicalKdVVectorField (hillPhysicalH4Synthesis (γ t)) x) t) (t : ℝ) (k : ℤ) :
    (v t).val.val.val k=periodOneCoefficient (classicalKdVVectorField (hillPhysicalH4Synthesis (γ t))) k := by
  have he : (fun x : ℝ => periodOneSobolevSynthesis (signedOneRealToScalarDomain (v t)) (x : AddCircle (2:ℝ)))=
      classicalKdVVectorField (hillPhysicalH4Synthesis (γ t)) := by
    funext x
    let L : RealSignedHilbert (signedStepOrder 0 1) →L[ℝ] ℂ :=
      (((ContinuousMap.evalCLM ℂ (x : AddCircle (2:ℝ))).comp periodOneSobolevSynthesis).restrictScalars ℝ).comp
        signedOneRealToScalarDomain
    have hx := @NLS.FunctionalAnalysis.hasDerivAt_clm_comp
      (RealSignedHilbert (signedStepOrder 0 1)) ℂ inferInstance inferInstance inferInstance inferInstance
      L _ _ t (hd t)
    change HasDerivAt (fun r : ℝ => hillPhysicalH4Synthesis (γ r) x)
      (periodOneSobolevSynthesis (signedOneRealToScalarDomain (v t)) (x : AddCircle (2:ℝ))) t at hx
    exact hx.unique (hPDE t x)
  have hc := congrArg (fun f : ℝ → ℂ => periodOneCoefficient f k) he
  rw [periodOneCoefficient_periodOneSobolevSynthesis,signedOneRealToScalarDomain_apply] at hc
  exact hc

theorem hillCanonicalFlow_is_smoothStrongKdVSolution
    (q : RealSignedHilbert (signedStepOrder 0 4)) (hq : ContDiff ℝ ∞ (hillPhysicalH4Synthesis q)) :
    HillSmoothStrongKdVSolution (hillIntegerCanonicalKdVFlow 4 q) := by
  exact ⟨fun t => hillIntegerCanonicalKdVFlow_smooth_physical_synthesis q hq t,
    fun t => ⟨hillIntegerCanonicalKdVVector 1 (hillIntegerCanonicalKdVFlow 4 q t),
      hasDerivAt_hillIntegerCanonicalKdVFlow 1 q t⟩,
    fun t x => hasDerivAt_hillIntegerCanonicalKdVFlow_physical_PDE q hq t x⟩

theorem hillSmoothStrongKdVSolution_eq_canonicalFlow
    (γ : ℝ → RealSignedHilbert (signedStepOrder 0 4)) (hγ : HillSmoothStrongKdVSolution γ) (t : ℝ) :
    γ t=hillIntegerCanonicalKdVFlow 4 (γ 0) t := by
  let v := fun t : ℝ => Classical.choose (hγ.2.1 t)
  have hd (t : ℝ) : HasDerivAt (fun r : ℝ => hillIntegerSourceOrderInclusion 1 4 (by decide) (γ r)) (v t) t :=
    Classical.choose_spec (hγ.2.1 t)
  exact hillSmoothPDECurve_eq_canonicalFlow γ v hγ.1 hd
    (fun s k => hillSmoothPhysicalDerivative_coefficients γ v hd hγ.2.2 s k) t

theorem existsUnique_hillSmoothStrongKdVSolution
    (q : RealSignedHilbert (signedStepOrder 0 4)) (hq : ContDiff ℝ ∞ (hillPhysicalH4Synthesis q)) :
    ∃! γ : ℝ → RealSignedHilbert (signedStepOrder 0 4), HillSmoothStrongKdVSolution γ ∧ γ 0=q := by
  refine ⟨hillIntegerCanonicalKdVFlow 4 q,
    ⟨hillCanonicalFlow_is_smoothStrongKdVSolution q hq,hillIntegerCanonicalKdVFlow_zero 4 q⟩,?_⟩
  intro γ hγ
  funext t
  rw [hillSmoothStrongKdVSolution_eq_canonicalFlow γ hγ.1 t,hγ.2]

theorem tendstoUniformlyOn_hillSmoothStrongKdVSolution_of_rough_initial_convergence
    {ι : Type*} {l : Filter ι} (T : ℝ)
    (Γ : ι → ℝ → RealSignedHilbert (signedStepOrder 0 4))
    (hΓ : ∀ j, HillSmoothStrongKdVSolution (Γ j)) (q : HillRealMeanZeroSource)
    (hinit : Tendsto (fun j => hillIntegerSourceInclusion 4 (Γ j 0)) l (𝓝 q)) :
    TendstoUniformlyOn (fun j t => hillIntegerSourceInclusion 4 (Γ j t))
      (hillRoughCanonicalKdVFlow q) l (Icc (-T) T) := by
  have he : (fun j t => hillIntegerSourceInclusion 4 (Γ j t))=
      (fun j t => hillRoughCanonicalKdVFlow (hillIntegerSourceInclusion 4 (Γ j 0)) t) := by
    funext j t
    rw [hillSmoothStrongKdVSolution_eq_canonicalFlow (Γ j) (hΓ j) t,hillIntegerCanonicalKdVFlow_inclusion]
  rw [he]
  exact tendstoUniformlyOn_hillRoughCanonicalKdVFlow T _ q hinit

end NLS.Articles.KdVPseudomeasures
