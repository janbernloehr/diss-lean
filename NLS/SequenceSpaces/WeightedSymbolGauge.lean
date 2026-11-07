import NLS.SequenceSpaces.WeightedMultiplier
import NLS.SequenceSpaces.AnalyticPhaseTrajectory
import NLS.SequenceSpaces.CompactRowMajorant

/-! Bounded symbols act bilinearly on the actual weighted sequence space.
For finite exponent, fixing the sequence gives a compact map from bounded
symbols. Exponential symbols give bounded invertible diagonal maps. -/
noncomputable section
open Complex
open scoped ENNReal
namespace NLS.WeightedCoeff
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

def boundedSymbol (w : Weight) (m : Coeff ⊤) (a : WeightedCoeff w p) :
    WeightedCoeff w p :=
  weightedMultiplier w w m ‖m‖ (fun k => by
    simpa only [mul_comm (w k)] using
      mul_le_mul_of_nonneg_left (lp.norm_apply_le_norm (by simp) m k) (w.positive k).le) a

omit [Fact (1 ≤ p)] in
@[simp] theorem boundedSymbol_apply (w : Weight) (m : Coeff ⊤)
    (a : WeightedCoeff w p) (k : ℤ) :
    (boundedSymbol w m a).val k = m k*a.val k := rfl

theorem norm_boundedSymbol_le (w : Weight) (m : Coeff ⊤) (a : WeightedCoeff w p) :
    ‖boundedSymbol w m a‖ ≤ ‖m‖*‖a‖ :=
  norm_weightedMultiplier_le w w m ‖m‖ (norm_nonneg _) _ a

def boundedSymbolBilinear (w : Weight) :
    Coeff ⊤ →L[ℂ] WeightedCoeff w p →L[ℂ] WeightedCoeff w p :=
  (LinearMap.mk₂ ℂ (boundedSymbol w)
    (by intro m n a; apply Subtype.ext; funext k; exact add_mul _ _ _)
    (by intro c m a; apply Subtype.ext; funext k; exact mul_assoc _ _ _)
    (by intro m a b; apply Subtype.ext; funext k; exact mul_add _ _ _)
    (by intro c m a; apply Subtype.ext; funext k; exact mul_left_comm _ _ _)).mkContinuous₂ 1
      (fun m a => by
        change ‖boundedSymbol w m a‖ ≤ 1*‖m‖*‖a‖
        rw [one_mul]
        exact norm_boundedSymbol_le w m a)

@[simp] theorem boundedSymbolBilinear_apply (w : Weight) (m : Coeff ⊤)
    (a : WeightedCoeff w p) (k : ℤ) :
    (boundedSymbolBilinear w m a).val k = m k*a.val k := rfl

theorem isCompactOperator_boundedSymbol_fixed (w : Weight) (hp : p ≠ ⊤)
    (a : WeightedCoeff w p) : IsCompactOperator ((boundedSymbolBilinear w).flip a) := by
  let W := (weightIsometry w p).toContinuousLinearEquiv
  let T := W.toContinuousLinearMap.comp ((boundedSymbolBilinear w).flip a)
  have hc : IsCompactOperator T := Coeff.isCompactOperator_of_rowMajorant hp T (W a) (by
    intro k m
    change ‖(w k:ℂ)*(m k*a.val k)‖ ≤ ‖(w k:ℂ)*a.val k‖*‖m‖
    simp only [norm_mul]
    calc
      _ = (‖(w k:ℂ)‖*‖a.val k‖)*‖m k‖ := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left
        (lp.norm_apply_le_norm (by simp) m k) (by positivity))
  have he : (boundedSymbolBilinear w).flip a = W.symm.toContinuousLinearMap.comp T := by
    ext m
    exact (W.symm_apply_apply _).symm
  rw [he]
  exact hc.clm_comp W.symm.toContinuousLinearMap

def exponentialSymbolEquiv (w : Weight) (b : Coeff ⊤) :
    WeightedCoeff w p ≃L[ℂ] WeightedCoeff w p where
  toFun := boundedSymbolBilinear w (NormedSpace.exp b)
  invFun := boundedSymbolBilinear w (NormedSpace.exp (-b))
  map_add' := map_add _
  map_smul' := map_smul _
  left_inv a := by
    apply Subtype.ext
    funext k
    simp only [boundedSymbolBilinear_apply,Coeff.infty_exp_apply,lp.coeFn_neg,Pi.neg_apply]
    rw [← mul_assoc,← Complex.exp_add,neg_add_cancel,Complex.exp_zero,one_mul]
  right_inv a := by
    apply Subtype.ext
    funext k
    simp only [boundedSymbolBilinear_apply,Coeff.infty_exp_apply,lp.coeFn_neg,Pi.neg_apply]
    rw [← mul_assoc,← Complex.exp_add,add_neg_cancel,Complex.exp_zero,one_mul]
  continuous_toFun := (boundedSymbolBilinear w (NormedSpace.exp b)).continuous
  continuous_invFun := (boundedSymbolBilinear w (NormedSpace.exp (-b))).continuous

@[simp] theorem exponentialSymbolEquiv_apply (w : Weight) (b : Coeff ⊤)
    (a : WeightedCoeff w p) (k : ℤ) :
    (exponentialSymbolEquiv w b a).val k = Complex.exp (b k)*a.val k :=
  congrArg (fun z => z*a.val k) (Coeff.infty_exp_apply b k)

@[simp] theorem exponentialSymbolEquiv_symm_apply (w : Weight) (b : Coeff ⊤)
    (a : WeightedCoeff w p) (k : ℤ) :
    ((exponentialSymbolEquiv w b).symm a).val k = Complex.exp (-b k)*a.val k := by
  change NormedSpace.exp (-b) k*a.val k = _
  rw [Coeff.infty_exp_apply]
  rfl

end NLS.WeightedCoeff
