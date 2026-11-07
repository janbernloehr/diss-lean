import NLS.KdV.HillOnIndexAbelianFilledRemainder
import NLS.ComplexAnalysis.QuadraticCosinePrimitive
import NLS.ComplexAnalysis.ConvexHolomorphicPrimitive

/-! The diagonal Abelian phase on a cosine cover of the ACTUAL local
spectral curve. Its derivative is the exact regular pullback of the
Hill differential, INCLUDING both branch points. The phase is zero
at tau-delta (angle pi); the actual half-gap gives the ORIGINAL left
endpoint. Reversing the half-gap changes the phase only modulo pi. -/
noncomputable section
open Set Metric Complex Filter Topology NLS.ComplexAnalysis NLS.ZakharovShabat
open scoped ENNReal Classical unitInterval
namespace NLS.KdV.HillProductEquationPatch

def onIndexAbelianCosinePhase (P : HillProductEquationPatch) (n : ℕ+) (q : PeriodOneHminusOne)
    (δ θ : ℂ) : ℂ :=
  θ-(Real.pi:ℂ)+quadraticCosinePrimitive
    (sourceStandardRootMidpoint (by norm_num) (by norm_num) (P.sourcePsi q) ((n:ℕ):ℤ)) δ
    (fun z => P.onIndexAbelianFilledRemainder n (z,q)) θ

theorem onIndexAbelianCosinePhase_at_pi (P : HillProductEquationPatch) (n : ℕ+)
    (q : PeriodOneHminusOne) (δ : ℂ) : P.onIndexAbelianCosinePhase n q δ (Real.pi:ℂ) = 0 := by
  simp [onIndexAbelianCosinePhase,quadraticCosinePrimitive]

theorem onIndexAbelianCosinePhase_at_zero (P : HillProductEquationPatch) (n : ℕ+)
    (q : PeriodOneHminusOne) (δ : ℂ) : P.onIndexAbelianCosinePhase n q δ 0 = -(Real.pi:ℂ) := by
  simp [onIndexAbelianCosinePhase,quadraticCosinePrimitive]

theorem onIndexCosineCover_actual_endpoint_frequencies (P : HillProductEquationPatch) (n : ℕ+)
    (q : PeriodOneHminusOne) :
    cosineGapPoint (sourceStandardRootMidpoint (by norm_num) (by norm_num) (P.sourcePsi q) ((n:ℕ):ℤ))
      (sourceStandardRootHalfGap (by norm_num) (by norm_num) (P.sourcePsi q) ((n:ℕ):ℤ)) (Real.pi:ℂ) =
        canonicalPeriodicLeft (by norm_num) (by norm_num) (periodOnePotential (P.sourcePsi q)) (periodOnePotential_mem _) ((n:ℕ):ℤ) ∧
    cosineGapPoint (sourceStandardRootMidpoint (by norm_num) (by norm_num) (P.sourcePsi q) ((n:ℕ):ℤ))
      (sourceStandardRootHalfGap (by norm_num) (by norm_num) (P.sourcePsi q) ((n:ℕ):ℤ)) 0 =
        canonicalPeriodicRight (by norm_num) (by norm_num) (periodOnePotential (P.sourcePsi q)) (periodOnePotential_mem _) ((n:ℕ):ℤ) := by
  constructor <;> simp only [cosineGapPoint,Complex.cos_pi,Complex.cos_zero,mul_neg_one,mul_one] <;>
    unfold sourceStandardRootMidpoint sourceStandardRootHalfGap canonicalPeriodicMidpoint canonicalPeriodicGap <;> ring

theorem hasDerivAt_onIndexAbelianCosinePhase (P : HillProductEquationPatch) (n : ℕ+)
    (q : PeriodOneHminusOne) (hq : q ∈ P.source) (δ θ : ℂ)
    (hδ : δ^2 = (canonicalPeriodicGap (by norm_num) (by norm_num) (periodOnePotential (P.sourcePsi q)) (periodOnePotential_mem _) ((n:ℕ):ℤ))^2/4)
    (hθ : cosineGapPoint (sourceStandardRootMidpoint (by norm_num) (by norm_num) (P.sourcePsi q) ((n:ℕ):ℤ)) δ θ ∈
      ball (P.centers ((n:ℕ):ℤ):ℂ) (P.radii ((n:ℕ):ℤ))) :
    HasDerivAt (P.onIndexAbelianCosinePhase n q δ)
      (-Complex.I*P.abelianGapNumerator n n (cosineGapPoint (sourceStandardRootMidpoint (by norm_num) (by norm_num) (P.sourcePsi q) ((n:ℕ):ℤ)) δ θ,q)) θ := by
  let τ := sourceStandardRootMidpoint (by norm_num) (by norm_num) (P.sourcePsi q) ((n:ℕ):ℤ)
  let z := cosineGapPoint τ δ θ
  let H : ℂ → ℂ := fun w => P.onIndexAbelianFilledRemainder n (w,q)
  have hH : AnalyticAt ℂ H z := (P.analytic_onIndexAbelianFilledRemainder n (z,q) ⟨hθ,hq⟩).comp
    (f := fun w : ℂ => (w,q)) (analyticAt_id.prod analyticAt_const)
  have heq : quadraticRootPolynomial τ (δ^2) z*deriv H z+(z-τ)*H z = P.abelianGapNumerator n n (z,q)-Complex.I := by
    rw [hδ]
    exact P.onIndexAbelianFilledRemainder_equation n q hq z hθ
  have hd := (((hasDerivAt_id θ).sub_const (Real.pi:ℂ)).add
    (hasDerivAt_quadraticCosinePrimitive τ δ θ (P.abelianGapNumerator n n (z,q)-Complex.I) H hH.differentiableAt heq))
  convert! hd using 1
  linear_combination -I_sq

theorem onIndexAbelianCosinePhase_curveIntegral (P : HillProductEquationPatch) (n : ℕ+)
    (q : PeriodOneHminusOne) (hq : q ∈ P.source) (δ : ℂ)
    (hδ : δ^2 = (canonicalPeriodicGap (by norm_num) (by norm_num) (periodOnePotential (P.sourcePsi q)) (periodOnePotential_mem _) ((n:ℕ):ℤ))^2/4)
    {a b : ℂ} (γ : Path a b) (hγ : ContDiffOn ℝ 1 γ.extend (Icc 0 1))
    (hinside : ∀ t ∈ Icc (0:ℝ) 1,
      cosineGapPoint (sourceStandardRootMidpoint (by norm_num) (by norm_num) (P.sourcePsi q) ((n:ℕ):ℤ)) δ (γ.extend t) ∈
        ball (P.centers ((n:ℕ):ℤ):ℂ) (P.radii ((n:ℕ):ℤ))) :
    (∫ᶜ θ in γ, holomorphicOneForm (fun θ => -Complex.I*P.abelianGapNumerator n n
      (cosineGapPoint (sourceStandardRootMidpoint (by norm_num) (by norm_num) (P.sourcePsi q) ((n:ℕ):ℤ)) δ θ,q)) θ) =
      P.onIndexAbelianCosinePhase n q δ b-P.onIndexAbelianCosinePhase n q δ a := by
  let τ := sourceStandardRootMidpoint (by norm_num) (by norm_num) (P.sourcePsi q) ((n:ℕ):ℤ)
  let U := {θ : ℂ | cosineGapPoint τ δ θ ∈ ball (P.centers ((n:ℕ):ℤ):ℂ) (P.radii ((n:ℕ):ℤ))}
  let f : ℂ → ℂ := fun θ => -Complex.I*P.abelianGapNumerator n n (cosineGapPoint τ δ θ,q)
  have hf : AnalyticOnNhd ℂ f U := by
    intro θ hθ
    have hz : cosineGapPoint τ δ θ ∈ ball (P.centers ((n:ℕ):ℤ):ℂ) (P.radii ((n:ℕ):ℤ)) := hθ
    have hc : AnalyticAt ℂ (fun θ => (cosineGapPoint τ δ θ,q)) θ := by
      exact (analyticAt_const.add (analyticAt_const.mul (Complex.analyticAt_cos))).prod analyticAt_const
    exact analyticAt_const.mul ((P.analytic_abelianGapNumerator_on_patch n n _ ⟨ball_subset_closedBall hz,hq⟩).comp hc)
  have hω : ContinuousOn (holomorphicOneForm f) U := hf.continuousOn.smul continuousOn_const
  apply curveIntegral_eq_sub_of_primitive f (P.onIndexAbelianCosinePhase n q δ) U
    (fun θ hθ => P.hasDerivAt_onIndexAbelianCosinePhase n q hq δ θ hδ hθ) γ hγ hinside
  apply hω.curveIntegrable_of_contDiffOn hγ
  intro t
  change cosineGapPoint τ δ (γ t) ∈ ball (P.centers ((n:ℕ):ℤ):ℂ) (P.radii ((n:ℕ):ℤ))
  simpa only [Path.extend_apply _ t.property] using hinside t t.property

end NLS.KdV.HillProductEquationPatch
