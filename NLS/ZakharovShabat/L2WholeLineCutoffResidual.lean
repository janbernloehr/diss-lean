import NLS.ZakharovShabat.L2WholeLineCutoff
import NLS.ZakharovShabat.L2WholeLineFloquetMass
import NLS.ZakharovShabat.L2WholeLineNonrealResolvent

/-! # Exact Hermitian L2 residual identities for physical cutoffs -/
noncomputable section
set_option autoImplicit false
open Set MeasureTheory Complex
namespace NLS.ZakharovShabat

/-- The opposite unit imaginary signs preserve the fibre norm. -/
theorem norm_physicalCutoffResidual (ψ : ℝ → ℂ) (F : ℝ → ℂ × ℂ) (t : ℝ) :
    ‖(WithLp.toLp 2 (physicalCutoffResidual ψ F t) : WholeLineVector)‖ =
      ‖deriv ψ t‖ * ‖(WithLp.toLp 2 (F t) : WholeLineVector)‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (mul_nonneg (norm_nonneg _) (norm_nonneg _))).mp
  rw [mul_pow]
  simp only [physicalCutoffResidual,WithLp.prod_norm_sq_eq_of_L2,WithLp.toLp_fst,WithLp.toLp_snd,norm_mul,norm_neg,
    Complex.norm_I,one_mul]
  ring

/-- The actual physical pencil on the cutoff equals the L2 class of its
signed derivative residual. -/
theorem wholeLinePencil_cutoff_eq (u : IntervalPairL2)
    (hu : IsClassicalRealType (intervalL2Representative u)) (z : ℂ) (v : Fin 2 → ℂ)
    (ψ : ℝ → ℂ) (hψ : ContDiff ℝ 1 ψ) (hc : HasCompactSupport ψ) :
    wholeLinePencil u z
      ⟨wholeLineCutoff u z v ψ hψ.continuous hc,wholeLineCutoff_mem_closure_domain u hu z v ψ hψ hc⟩ =
      wholeLineOfPair (physicalCutoffResidual ψ (l2WholeLineSolution u z v))
        (memLp_physicalCutoffResidual ψ hψ hc _ (continuous_l2WholeLineSolution u z v)) := by
  let F := fun t => ψ t • l2WholeLineSolution u z v t
  let G := fun t => z • F t-physicalCutoffResidual ψ (l2WholeLineSolution u z v) t
  let f := wholeLineCutoff u z v ψ hψ.continuous hc
  let g := wholeLineOfPair G (memLp_wholeLineCutoffImage u z v ψ hψ hc)
  change z • f-(wholeLineMinimalOperator u).closure _ = _
  rw [wholeLineCutoff_closure_apply u hu z v ψ hψ hc]
  change z • f-g = _
  apply Lp.ext
  filter_upwards [Lp.coeFn_sub (z • f) g,Lp.coeFn_smul z f,
    wholeLineOfPair_ae F (memLp_wholeLineCutoffPair u z v ψ hψ.continuous hc),
    wholeLineOfPair_ae G (memLp_wholeLineCutoffImage u z v ψ hψ hc),
    wholeLineOfPair_ae (physicalCutoffResidual ψ (l2WholeLineSolution u z v))
      (memLp_physicalCutoffResidual ψ hψ hc _ (continuous_l2WholeLineSolution u z v))]
    with t hsub hsm hf hg hr
  simp only [Pi.sub_apply,Pi.smul_apply] at hsub hsm
  change f t = WithLp.toLp 2 (F t) at hf
  change g t = WithLp.toLp 2 (G t) at hg
  rw [hsub,hsm,hf,hg,hr]
  apply (WithLp.linearEquiv 2 ℂ (ℂ × ℂ)).injective
  change z • F t-(z • F t-physicalCutoffResidual ψ (l2WholeLineSolution u z v) t) =
    physicalCutoffResidual ψ (l2WholeLineSolution u z v) t
  exact sub_sub_cancel _ _

/-- The actual cutoff norm is the cutoff-weighted physical mass integral. -/
theorem norm_wholeLineCutoff_sq (u : IntervalPairL2) (z : ℂ) (v : Fin 2 → ℂ)
    (ψ : ℝ → ℂ) (hψ : Continuous ψ) (hc : HasCompactSupport ψ) :
    ‖wholeLineCutoff u z v ψ hψ hc‖ ^ 2 =
      ∫ t : ℝ, ‖ψ t‖ ^ 2 * wholeLineSolutionMass u z v t := by
  rw [wholeLineCutoff,norm_wholeLineOfPair_sq]
  apply integral_congr_ae
  filter_upwards with t
  change ‖ψ t • (WithLp.toLp 2 (l2WholeLineSolution u z v t) : WholeLineVector)‖ ^ 2 = _
  rw [norm_smul,mul_pow]
  rfl

/-- The actual pencil residual norm is precisely the derivative-weighted mass integral. -/
theorem norm_wholeLinePencil_cutoff_sq (u : IntervalPairL2)
    (hu : IsClassicalRealType (intervalL2Representative u)) (z : ℂ) (v : Fin 2 → ℂ)
    (ψ : ℝ → ℂ) (hψ : ContDiff ℝ 1 ψ) (hc : HasCompactSupport ψ) :
    ‖wholeLinePencil u z
      ⟨wholeLineCutoff u z v ψ hψ.continuous hc,wholeLineCutoff_mem_closure_domain u hu z v ψ hψ hc⟩‖ ^ 2 =
      ∫ t : ℝ, ‖deriv ψ t‖ ^ 2 * wholeLineSolutionMass u z v t := by
  rw [wholeLinePencil_cutoff_eq u hu z v ψ hψ hc,norm_wholeLineOfPair_sq]
  apply integral_congr_ae
  filter_upwards with t
  rw [norm_physicalCutoffResidual,mul_pow]
  rfl

end NLS.ZakharovShabat
