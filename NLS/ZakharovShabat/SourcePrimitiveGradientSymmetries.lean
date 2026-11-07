import NLS.ZakharovShabat.SourceMidpointSpectralData
import NLS.ZakharovShabat.L2FullAbelianGradient
import NLS.ZakharovShabat.L2DiscriminantPointwiseSymmetries

/-! # Exact normalized physical primitive-gradient covariance -/
noncomputable section
open Set Complex
namespace NLS.ZakharovShabat

theorem sourceFullAbelianPhysicalGradient_componentSwap (φ : CoeffPair 2) (z : ℂ) (x : ℝ) :
    sourceFullAbelianPhysicalGradient (sourceComponentSwap φ) (-z) x =
      (-(sourceFullAbelianPhysicalGradient φ z x).2,-(sourceFullAbelianPhysicalGradient φ z x).1) := by
  simp only [sourceFullAbelianPhysicalGradient,l2NormalizedDiscriminantGradient,
    l2WholeLineDiscriminantGradient_sourceComponentSwap,sourceCanonicalRoot_componentSwap,
    inv_neg,Prod.smul_fst,Prod.smul_snd,smul_eq_mul]
  apply Prod.ext <;> dsimp <;> ring

theorem sourceFullAbelianPhysicalGradient_midpointReflection (φ : CoeffPair 2) (z : ℂ) (x : ℝ) :
    sourceFullAbelianPhysicalGradient (sourceMidpointReflection φ) (-z) x =
      -sourceFullAbelianPhysicalGradient φ z (1-x) := by
  simp only [sourceFullAbelianPhysicalGradient,l2NormalizedDiscriminantGradient,
    l2WholeLineDiscriminantGradient_sourceMidpointReflection,sourceCanonicalRoot_midpointReflection,
    inv_neg,neg_smul]

theorem sourceFullAbelianPhysicalGradient_reciprocalScaling (c : ℂ) (hc : c ≠ 0)
    (φ : CoeffPair 2) (z : ℂ) (x : ℝ) :
    sourceFullAbelianPhysicalGradient (sourceReciprocalScaling c φ) z x =
      (c⁻¹*(sourceFullAbelianPhysicalGradient φ z x).1,c*(sourceFullAbelianPhysicalGradient φ z x).2) := by
  simp only [sourceFullAbelianPhysicalGradient,l2NormalizedDiscriminantGradient,
    l2WholeLineDiscriminantGradient_sourceReciprocalScaling c hc,
    sourceCanonicalRoot_reciprocalScaling _ _ c hc,
    Prod.smul_fst,Prod.smul_snd,smul_eq_mul]
  apply Prod.ext <;> dsimp <;> ring

end NLS.ZakharovShabat
