import NLS.KdV.HillOwnPhysicalPullback
import NLS.KdV.HillOwnSeriesAssembly
import NLS.KdV.HillSpectralCartesianTerminal

noncomputable section
set_option autoImplicit false
open Set Complex MeasureTheory NLS.ComplexAnalysis NLS.ZakharovShabat
open scoped ComplexConjugate
namespace NLS.KdV.HillHminusPsiChart
variable (P : HillHminusPsiChart) (q : RealPeriodOneHillPotential)
  (hq : hillOriginalHminusSource q.val∈P.source)
  (hreal : ∀ a∈P.miura.domain, IsRealPeriodOneHminusOne a → ∀ k : ℤ,
    P.miura.lift a (-k)=conj (P.miura.lift a k))
  (houtside : hillHminusRadicand (hillOriginalHminusSource q.val) (-P.miura.energyShift)≠0)
  (c : ℝ) (hshift : P.miura.energyShift=(c:ℂ)^2)

/-- The COMPLETE ORIGINAL physical Cartesian coordinate has its exact
actual own-source integral and full signed beta correction, with ONLY
the central beta removed. The negative-selected beta cancels, and the
NONZERO negative-anchor period disappears only in this exponential.
No original scalar off-index or own-index term is omitted. -/
theorem originalSpectralCartesian_eq_source_own_integral
    (H : SourceLemma12_12Data (by norm_num) (by norm_num)
      P.family.originalDomain P.family.domain P.family.roots)
    (n : ℕ+)
    (hgap : hillRealGapHalfLength q.val q.property.1 q.property.2 n≠0)
    (hw : hillDirichletSheetRoot (SpectralWeight.one.toCoeff q.val)
      (hillDirichletEnergy q.val q.property.1 q.property.2 n n.pos)≠0) :
    let w := hillDirichletSheetRoot (SpectralWeight.one.toCoeff q.val)
      (hillDirichletEnergy q.val q.property.1 q.property.2 n n.pos)
    let ψ := P.dirichletSource (hillOriginalHminusSource q.val)
    let γ := P.originalCosineFrequencyPath q hq hreal houtside c hshift n hgap
    hillSpectralCartesian q.val q.property.1 q.property.2 n n.pos=
      (Real.sqrt (2*hillRealGapIntegral q.val q.property.1 q.property.2 n 0):ℂ)*
        Complex.exp (I*(sourceAngularPathIntegral ((n:ℕ):ℤ) P.family.roots
          (sourceAngularRootSheet (by simp) w) ψ γ+
          P.sourceBetaCorrection (n:ℕ) (hillOriginalHminusSource q.val)-
          sourceAngularBeta (by norm_num) (by norm_num) ((n:ℕ):ℤ) 0 P.family.roots ψ)) := by
  dsimp only
  let θ := hillDirichletSelectedRealAngle q.val q.property.1 q.property.2 n n.pos hgap
  let B := P.sourceBetaCorrection (n:ℕ) (hillOriginalHminusSource q.val)
  let C := sourceAngularBeta (by norm_num) (by norm_num) ((n:ℕ):ℤ) 0 P.family.roots
    (P.dirichletSource (hillOriginalHminusSource q.val))
  let w := hillDirichletSheetRoot (SpectralWeight.one.toCoeff q.val)
    (hillDirichletEnergy q.val q.property.1 q.property.2 n n.pos)
  let γ := P.originalCosineFrequencyPath q hq hreal houtside c hshift n hgap
  let J := sourceAngularPathIntegral ((n:ℕ):ℤ) P.family.roots (sourceAngularRootSheet (by simp) w)
    (P.dirichletSource (hillOriginalHminusSource q.val)) γ
  have hfull := P.originalFullCorrection_eq_signed_source_finite_terms q hq hreal houtside c hshift H n
  have hown : hillRegularAbelianCorrection q.val q.property.1 q.property.2 n n.pos n n.pos=
      hillAbelianCosinePrimitive q.val q.property.1 q.property.2 n n.pos n (θ:ℂ)-((θ:ℂ)-(Real.pi:ℂ)) := by
    rw [hillRegularAbelianCorrection,dif_neg hgap,hillRegularAbelianPrimitive,if_pos rfl,one_mul]
  have hpull := P.originalOwnCosinePrimitive_source_decomposition q hq hreal houtside c hshift H n hgap hw
  have hphase : (θ:ℂ)-(Real.pi:ℂ)+hillSummedRegularAbelianCorrection q.val q.property.1 q.property.2 n n.pos=
      (J+B-C)-(if θ<0 then 2*(Real.pi:ℂ) else 0) := by
    linear_combination hfull+hown+hpull
  have hperiod : Complex.exp (I*(if θ<0 then 2*(Real.pi:ℂ) else 0))=1 := by
    by_cases hneg : θ<0
    · rw [if_pos hneg,show I*(2*(Real.pi:ℂ))=2*(Real.pi:ℂ)*I by ring,Complex.exp_two_pi_mul_I]
    · rw [if_neg hneg,mul_zero,Complex.exp_zero]
  have hspec := hillDirichletSelectedRealAngle_spec q.val q.property.1 q.property.2 n n.pos hgap
  rw [hillSpectralCartesian_eq_abelian_terminal q.val q.property.1 q.property.2 n n.pos hgap θ
    hspec.2.1 hspec.2.2,hphase,mul_sub,Complex.exp_sub,hperiod,div_one]

end NLS.KdV.HillHminusPsiChart
