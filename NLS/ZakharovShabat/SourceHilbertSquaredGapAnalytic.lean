import NLS.ZakharovShabat.SourceSymmetricContour
import NLS.ZakharovShabat.SourcePeriodicGapTails
import NLS.SequenceSpaces.HolderEmbedding
import NLS.SequenceSpaces.BoundedCoordinateAnalytic

/-! # The actual squared periodic gaps as a native analytic ell1 map

The gap itself need not be analytic at a collision. Its square has analytic
coordinates, and the locally uniform ell2 gap bound controls its ell1 norm.
-/
noncomputable section
set_option autoImplicit false
open Set Complex
namespace NLS.ZakharovShabat

def sourceHilbertSquaredGap (ψ : CoeffPair 2) : Coeff 1 :=
  Coeff.holderProduct (sourcePeriodicGapDisplacement (by simp) (by norm_num) ψ)
    (sourcePeriodicGapDisplacement (by simp) (by norm_num) ψ)

@[simp] theorem sourceHilbertSquaredGap_apply (ψ : CoeffPair 2) (n : ℤ) :
    sourceHilbertSquaredGap ψ n =
      (canonicalPeriodicGap (by simp) (by norm_num)
        (periodOnePotential ψ) (periodOnePotential_mem _) n)^2 := by
  simp only [sourceHilbertSquaredGap,Coeff.holderProduct_apply,
    sourcePeriodicGapDisplacement_apply,pow_two]

theorem exists_sourceHilbertSquaredGap_analytic_common_domain :
    ∃ W : Set (CoeffPair 2), IsOpen W ∧ realTypeSourceLocus 2 ⊆ W ∧
      AnalyticOnNhd ℂ sourceHilbertSquaredGap W := by
  obtain ⟨W,hW,_,hreal,hcoord⟩ :=
    exists_global_source_analytic_midpoint_squaredGap (by simp : (2 : ENNReal) ≠ ⊤) (by norm_num)
  refine ⟨W,hW,hreal,?_⟩
  intro ψ hψ
  obtain ⟨_,_,U,hU,hψU,R,hR,hbound⟩ :=
    exists_uniform_small_sourcePeriodicGapDisplacement
      (by simp : (2 : ENNReal) ≠ ⊤) (by norm_num) ψ (ε := 1) (by norm_num)
  apply (Coeff.analyticOnNhd_of_bounded_coordinatewise sourceHilbertSquaredGap
    (hW.inter hU) ?_ (R^2) ?_) ψ ⟨hψ,hψU⟩
  · intro n χ hχ
    simpa only [sourceHilbertSquaredGap_apply] using (hcoord χ hχ.1 n).2
  · intro χ hχ
    apply (Coeff.norm_holderProduct_le _ _).trans
    simpa only [pow_two] using
      mul_self_le_mul_self (norm_nonneg _) (hbound χ hχ.2).1

end NLS.ZakharovShabat
