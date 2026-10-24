import NLS.ZakharovShabat.L2WholeLineAdjointRegularity
import NLS.ZakharovShabat.L2WholeLineGreenIdentity
import NLS.FunctionalAnalysis.ACIntegralAtInfinity

/-! # Vanishing boundary terms and symmetry on the actual adjoint domain

The maximal representatives and their boundary form are locally absolutely
continuous. L2 estimates make the boundary form and its derivative globally
integrable, so the whole-line boundary contribution vanishes.
-/
noncomputable section
set_option autoImplicit false
open Set MeasureTheory Complex
open NLS.FunctionalAnalysis
namespace NLS.ZakharovShabat

/-- Local absolute continuity of both factors gives local absolute
continuity of the original Hermitian boundary form. -/
theorem absolutelyContinuousOnInterval_boundaryForm_of_AC
    {F G : ℝ → ℂ × ℂ} {a b : ℝ}
    (hf : AbsolutelyContinuousOnInterval F a b)
    (hg : AbsolutelyContinuousOnInterval G a b) :
    AbsolutelyContinuousOnInterval (fun t => wholeLineBoundaryForm (F t) (G t)) a b := by
  have hf1 := absolutelyContinuousOnInterval_clm hf (ContinuousLinearMap.fst ℝ ℂ ℂ)
  have hf2 := absolutelyContinuousOnInterval_clm hf (ContinuousLinearMap.snd ℝ ℂ ℂ)
  have hg1 := absolutelyContinuousOnInterval_clm hg (ContinuousLinearMap.fst ℝ ℂ ℂ)
  have hg2 := absolutelyContinuousOnInterval_clm hg (ContinuousLinearMap.snd ℝ ℂ ℂ)
  have h1 := ((absolutelyContinuousOnInterval_clm hf1 Complex.conjCLE.toContinuousLinearMap).const_smul (-I)).smul hg1
  have h2 := ((absolutelyContinuousOnInterval_clm hf2 Complex.conjCLE.toContinuousLinearMap).const_smul I).smul hg2
  simpa [wholeLineBoundaryForm,Pi.add_def,Pi.smul_def,smul_eq_mul] using! h1.add h2

/-- The boundary form of two whole-line L2 functions is globally L1. -/
theorem integrable_wholeLineBoundaryForm {F G : ℝ → ℂ × ℂ}
    (hf : MemLp F 2 volume) (hg : MemLp G 2 volume) :
    Integrable (fun t => wholeLineBoundaryForm (F t) (G t)) volume := by
  have h1 := (hf.fst.star.integrable_mul hg.fst).const_mul (-I)
  have h2 := (hf.snd.star.integrable_mul hg.snd).const_mul I
  simpa only [wholeLineBoundaryForm,Pi.add_apply,Pi.mul_apply,Pi.star_apply,mul_assoc] using! h1.add h2

/-- The actual adjoint of the real minimal operator is itself symmetric.
The boundary argument uses global L2 integrability and local absolute
continuity; no unproved pointwise decay of the vector is assumed. -/
theorem wholeLineMinimalOperator_adjoint_isFormalAdjoint
    (u : IntervalPairL2) (hu : IsClassicalRealType (intervalL2Representative u)) :
    (wholeLineMinimalOperator u).adjoint.IsFormalAdjoint (wholeLineMinimalOperator u).adjoint := by
  intro f g
  obtain ⟨F,hF,hFac,hFd⟩ :=
    (wholeLineMinimalOperator_adjoint_weakEquation u f).exists_AC_representative hu
  obtain ⟨G,hG,hGac,hGd⟩ :=
    (wholeLineMinimalOperator_adjoint_weakEquation u g).exists_AC_representative hu
  let B : ℝ → ℂ := fun t => wholeLineBoundaryForm (F t) (G t)
  let R : ℝ → ℂ := fun t =>
    inner ℂ ((wholeLineMinimalOperator u).adjoint f t) (g.val t) -
      inner ℂ (f.val t) ((wholeLineMinimalOperator u).adjoint g t)
  have hBac (a b : ℝ) : AbsolutelyContinuousOnInterval B a b :=
    absolutelyContinuousOnInterval_boundaryForm_of_AC (hFac a b) (hGac a b)
  have hB : Integrable B volume := integrable_wholeLineBoundaryForm
    ((memLp_congr_ae hF).mp (memLp_wholeLineL2Pair f))
    ((memLp_congr_ae hG).mp (memLp_wholeLineL2Pair g))
  have hR : Integrable R volume := by
    simpa only [R] using!
      (L2.integrable_inner ((wholeLineMinimalOperator u).adjoint f) g.val).sub
        (L2.integrable_inner f.val ((wholeLineMinimalOperator u).adjoint g))
  have hd : ∀ᵐ t : ℝ, HasDerivAt B (R t) t := by
    filter_upwards [hF,hG,hFd,hGd,ae_l2WholeLinePotential_real u hu]
      with t hFt hGt hFdt hGdt hr
    have h := (((HasFDerivAt.hasDerivAt hFdt.fst).star.const_mul (-I)).mul
      (HasFDerivAt.hasDerivAt hGdt.fst)).add
      (((HasFDerivAt.hasDerivAt hFdt.snd).star.const_mul I).mul
        (HasFDerivAt.hasDerivAt hGdt.snd))
    convert! h using 1
    rw [← hFt,← hGt]
    simp only [R,wholeLineWeakDerivative,wholeLineL2Pair,WithLp.prod_inner_apply,
      RCLike.inner_apply',ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.toSpanSingleton_apply,one_smul]
    rw [hr]
    simp
    ring_nf
    simp [I_sq,sub_eq_add_neg]
  have hz := integral_eq_zero_of_locally_AC hBac hB hR hd
  rw [L2.inner_def,L2.inner_def]
  apply sub_eq_zero.mp
  rw [← integral_sub (L2.integrable_inner ((wholeLineMinimalOperator u).adjoint f) g)
    (L2.integrable_inner f ((wholeLineMinimalOperator u).adjoint g))]
  exact hz

end NLS.ZakharovShabat
