import NLS.KdV.HillHminusNormalizedCartesianBrackets
import NLS.KdV.HillHminusEndpointCartesianMatrix

noncomputable section
set_option autoImplicit false
open Set Complex Filter Topology
namespace NLS.KdV

/-- The exact endpoint matrix has zero action weight in every nonzero
entry, with the ACTUAL original positive-2i convention retained. -/
theorem hillCartesianActionWeight_mul_matrixEntry_zero
    (n m k : ℕ+) (σ τ : Bool) :
    (hillCartesianActionRotationWeight σ n k + hillCartesianActionRotationWeight τ m k) *
      hillOriginalComplexGardnerMatrixEntry σ τ n m = 0 := by
  by_cases hnm : (n:ℕ)=(m:ℕ)
  · have he : n=m := Subtype.ext hnm
    subst m
    by_cases hkn : k=n
    · subst k
      cases σ <;> cases τ <;>
        simp [hillCartesianActionRotationWeight,hillOriginalComplexGardnerMatrixEntry]
    · have hkn' : (k:ℕ)≠(n:ℕ) := fun h => hkn (Subtype.ext h)
      cases σ <;> cases τ <;>
        simp [hillCartesianActionRotationWeight,hillOriginalComplexGardnerMatrixEntry,hkn']
  · simp [hillCartesianActionRotationWeight,hillOriginalComplexGardnerMatrixEntry,hnm]

/-- The defect from the FULL original Cartesian matrix satisfies its
exact homogeneous evolution under every actual physical action source.
This proves the transport equation rather than assuming invariance. -/
theorem hillSignedCartesian_matrix_defect_action_evolution
    (q : RealPeriodOneHillPotential) (n m k : ℕ+) (σ τ : Bool)
    (hgapn : hillRealGapHalfLength q.val q.property.1 q.property.2 n ≠ 0)
    (hgapm : hillRealGapHalfLength q.val q.property.1 q.property.2 m ≠ 0)
    (F G J : PeriodOneHminusOne → ℂ)
    (hF : AnalyticAt ℂ F (hillOriginalHminusSource q.val))
    (hG : AnalyticAt ℂ G (hillOriginalHminusSource q.val))
    (hJ : AnalyticAt ℂ J (hillOriginalHminusSource q.val))
    (hFM : ∀ᶠ p : RealPeriodOneHillPotential in 𝓝 q,
      F (hillOriginalHminusSource p.val) = hillSignedSpectralCartesian σ n p)
    (hGM : ∀ᶠ p : RealPeriodOneHillPotential in 𝓝 q,
      G (hillOriginalHminusSource p.val) = hillSignedSpectralCartesian τ m p)
    (hJM : ∀ᶠ p : RealPeriodOneHillPotential in 𝓝 q,
      J (hillOriginalHminusSource p.val) = (hillRealGapIntegral p.val p.property.1 p.property.2 k 0 : ℂ)) :
    (fderiv ℂ (fun a => NLS.Poisson.hminusGardnerBracket F G a -
        hillOriginalComplexGardnerMatrixEntry σ τ n m) (hillOriginalHminusSource q.val))
      (hillOriginalHminusSource (hillPhysicalMomentHamiltonianSource
        q.val q.property.1 q.property.2 k k.pos 0)) =
      -(hillCartesianActionRotationWeight σ n k + hillCartesianActionRotationWeight τ m k) *
        (NLS.Poisson.hminusGardnerBracket F G (hillOriginalHminusSource q.val) -
          hillOriginalComplexGardnerMatrixEntry σ τ n m) := by
  have hB : AnalyticAt ℂ (NLS.Poisson.hminusGardnerBracket F G) (hillOriginalHminusSource q.val) :=
    (NLS.Poisson.gardnerBivector.analyticAt_bilinear _).comp₂
      ((NLS.Poisson.hminusCotangentCLM.analyticAt _).comp hF.fderiv)
      ((NLS.Poisson.hminusCotangentCLM.analyticAt _).comp hG.fderiv)
  rw [(hB.differentiableAt.hasFDerivAt.sub_const
    (hillOriginalComplexGardnerMatrixEntry σ τ n m)).fderiv]
  have he := hillSignedCartesian_bracket_action_hminus_evolution
    q n m k σ τ hgapn hgapm F G J hF hG hJ hFM hGM hJM
  rw [hillOriginalAction_hminus_HamiltonianVector_eq_neg_source q k J hJ hJM,map_neg] at he
  have hw := hillCartesianActionWeight_mul_matrixEntry_zero n m k σ τ
  linear_combination -he - hw

end NLS.KdV
