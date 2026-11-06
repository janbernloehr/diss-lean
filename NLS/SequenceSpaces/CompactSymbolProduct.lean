import NLS.SequenceSpaces.AnalyticPhaseTrajectory
import NLS.SequenceSpaces.CompactRowMajorant

/-! # Compact multiplication of bounded symbols by a fixed sequence

Multiplication by a fixed finite-exponent sequence is compact from the
bounded-symbol space into that sequence space. This controls derivatives
of analytic scaling factors without requiring derivative asymptotics.
-/
noncomputable section
open scoped ENNReal
namespace NLS.Coeff
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

theorem isCompactOperator_multiplierBilinear_flip (hp : p ≠ ⊤) (a : Coeff p) :
    IsCompactOperator ((multiplierBilinear (p := p)).flip a) := by
  apply isCompactOperator_of_rowMajorant hp _ a
  intro n m
  change ‖m n*a n‖ ≤ ‖a n‖*‖m‖
  rw [norm_mul,mul_comm]
  exact mul_le_mul_of_nonneg_left
    (lp.norm_apply_le_norm (by simp : (⊤ : ℝ≥0∞) ≠ 0) m n) (norm_nonneg _)

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

theorem fderiv_multiplier_sequence (σ : E → Coeff ⊤) (F : E → Coeff p) (a : E)
    (hσ : DifferentiableAt ℂ σ a) (hF : DifferentiableAt ℂ F a) :
    fderiv ℂ (fun b => multiplier (σ b) (F b)) a =
      (multiplierCLM (σ a)).comp (fderiv ℂ F a)+
        ((multiplierBilinear (p := p)).flip (F a)).comp (fderiv ℂ σ a) := by
  have hd := ((multiplierBilinear (p := p)).hasFDerivAt.comp a hσ.hasFDerivAt).clm_apply hF.hasFDerivAt
  change HasFDerivAt (fun b => multiplier (σ b) (F b)) _ a at hd
  rw [hd.fderiv]
  ext h n
  rfl

/-- The derivative of a varying bounded scaling has compact remainder
relative to the free scaling, provided the unscaled derivative does. -/
theorem isCompactOperator_fderiv_multiplier_sub_free (hp : p ≠ ⊤)
    (σ : E → Coeff ⊤) (F : E → Coeff p) (a : E)
    (hσ : DifferentiableAt ℂ σ a) (hF : DifferentiableAt ℂ F a)
    (hDF : IsCompactOperator (fderiv ℂ F a-fderiv ℂ F 0))
    (hσtail : IsCompactOperator (multiplierCLM (p := p) (σ a-σ 0))) :
    IsCompactOperator (fderiv ℂ (fun b => multiplier (σ b) (F b)) a-
      (multiplierCLM (σ 0)).comp (fderiv ℂ F 0)) := by
  have he : fderiv ℂ (fun b => multiplier (σ b) (F b)) a-
      (multiplierCLM (σ 0)).comp (fderiv ℂ F 0) =
      (multiplierCLM (σ a)).comp (fderiv ℂ F a-fderiv ℂ F 0)+
        (multiplierCLM (σ a-σ 0)).comp (fderiv ℂ F 0)+
          ((multiplierBilinear (p := p)).flip (F a)).comp (fderiv ℂ σ a) := by
    rw [fderiv_multiplier_sequence σ F a hσ hF]
    ext h n
    change σ a n*(fderiv ℂ F a h) n+(fderiv ℂ σ a h) n*F a n-
      σ 0 n*(fderiv ℂ F 0 h) n =
        σ a n*((fderiv ℂ F a h) n-(fderiv ℂ F 0 h) n)+
          (σ a n-σ 0 n)*(fderiv ℂ F 0 h) n+(fderiv ℂ σ a h) n*F a n
    ring
  rw [he]
  exact ((hDF.clm_comp (multiplierCLM (σ a))).add
    (hσtail.comp_clm (fderiv ℂ F 0))).add
      ((isCompactOperator_multiplierBilinear_flip hp (F a)).comp_clm (fderiv ℂ σ a))

theorem isCompactOperator_fderiv_multiplier_sub_zero (hp : p ≠ ⊤)
    (σ : E → Coeff ⊤) (F : E → Coeff p) (a : E)
    (hσ : DifferentiableAt ℂ σ a) (hF : DifferentiableAt ℂ F a)
    (hσ₀ : DifferentiableAt ℂ σ 0) (hF₀ : DifferentiableAt ℂ F 0) (hzero : F 0 = 0)
    (hDF : IsCompactOperator (fderiv ℂ F a-fderiv ℂ F 0))
    (hσtail : IsCompactOperator (multiplierCLM (p := p) (σ a-σ 0))) :
    IsCompactOperator (fderiv ℂ (fun b => multiplier (σ b) (F b)) a-
      fderiv ℂ (fun b => multiplier (σ b) (F b)) 0) := by
  have h0 : fderiv ℂ (fun b => multiplier (σ b) (F b)) 0 =
      (multiplierCLM (σ 0)).comp (fderiv ℂ F 0) := by
    rw [fderiv_multiplier_sequence σ F 0 hσ₀ hF₀]
    ext h n
    change σ 0 n*(fderiv ℂ F 0 h) n+(fderiv ℂ σ 0 h) n*F 0 n = _
    rw [hzero]
    simp only [lp.coeFn_zero,Pi.zero_apply,mul_zero,add_zero]
    rfl
  rw [h0]
  exact isCompactOperator_fderiv_multiplier_sub_free hp σ F a hσ hF hDF hσtail

theorem isCompactOperator_prodCLM
    {F G : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]
    [NormedAddCommGroup G] [NormedSpace ℂ G]
    (T : E →L[ℂ] F) (S : E →L[ℂ] G)
    (hT : IsCompactOperator T) (hS : IsCompactOperator S) :
    IsCompactOperator (T.prod S) := by
  have hc := (hT.clm_comp (ContinuousLinearMap.inl ℂ F G)).add
    (hS.clm_comp (ContinuousLinearMap.inr ℂ F G))
  have he : T.prod S = (ContinuousLinearMap.inl ℂ F G).comp T+
      (ContinuousLinearMap.inr ℂ F G).comp S := by
    apply ContinuousLinearMap.ext
    intro h
    change (T h,S h) = (T h,0)+(0,S h)
    simp
  rw [he]
  exact hc

end NLS.Coeff
