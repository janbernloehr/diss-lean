import NLS.ZakharovShabat.L2WholeLineIntegralEquation
import NLS.ZakharovShabat.L2WholeLineReality

/-! # The Hermitian Green identity for actual whole-line solutions

Absolute continuity makes the original boundary identity valid across
integer seams. This is a finite-interval identity, without any assumption
that a Floquet solution belongs to the whole-line Hilbert space.
-/
noncomputable section
set_option autoImplicit false
open Set MeasureTheory Complex
open NLS.FunctionalAnalysis
namespace NLS.ZakharovShabat

/-- The boundary form for the original signed differential expression. -/
def wholeLineBoundaryForm (f g : ℂ × ℂ) : ℂ :=
  -I * star f.1 * g.1 + I * star f.2 * g.2

/-- The boundary pairing of the actual physical solutions is absolutely
continuous on every finite real interval. -/
theorem absolutelyContinuousOnInterval_wholeLineBoundaryForm
    (u : IntervalPairL2) (z w : ℂ) (v q : Fin 2 → ℂ) (a b : ℝ) :
    AbsolutelyContinuousOnInterval (fun t => wholeLineBoundaryForm
      (l2WholeLineSolution u z v t) (l2WholeLineSolution u w q t)) a b := by
  have hf := absolutelyContinuousOnInterval_l2WholeLineSolution u z v a b
  have hg := absolutelyContinuousOnInterval_l2WholeLineSolution u w q a b
  have hf1 := absolutelyContinuousOnInterval_clm hf (ContinuousLinearMap.fst ℝ ℂ ℂ)
  have hf2 := absolutelyContinuousOnInterval_clm hf (ContinuousLinearMap.snd ℝ ℂ ℂ)
  have hg1 := absolutelyContinuousOnInterval_clm hg (ContinuousLinearMap.fst ℝ ℂ ℂ)
  have hg2 := absolutelyContinuousOnInterval_clm hg (ContinuousLinearMap.snd ℝ ℂ ℂ)
  have h1 := ((absolutelyContinuousOnInterval_clm hf1 Complex.conjCLE.toContinuousLinearMap).const_smul (-I)).smul hg1
  have h2 := ((absolutelyContinuousOnInterval_clm hf2 Complex.conjCLE.toContinuousLinearMap).const_smul I).smul hg2
  simpa [wholeLineBoundaryForm,Pi.add_def,Pi.smul_def,smul_eq_mul] using! h1.add h2

/-- The original physical equation differentiates the Hermitian boundary
form almost everywhere on the full real line. -/
theorem ae_hasDerivAt_wholeLineBoundaryForm (u : IntervalPairL2)
    (hu : IsClassicalRealType (intervalL2Representative u))
    (z w : ℂ) (v q : Fin 2 → ℂ) :
    ∀ᵐ t : ℝ, HasDerivAt (fun s => wholeLineBoundaryForm
      (l2WholeLineSolution u z v s) (l2WholeLineSolution u w q s))
      ((star z-w) * (star (l2WholeLineSolution u z v t).1 * (l2WholeLineSolution u w q t).1 +
        star (l2WholeLineSolution u z v t).2 * (l2WholeLineSolution u w q t).2)) t := by
  filter_upwards [ae_hasDerivAt_l2WholeLineSolution u z v,
    ae_hasDerivAt_l2WholeLineSolution u w q,ae_l2WholeLinePotential_real u hu] with t hf hg hr
  have h := (((HasFDerivAt.hasDerivAt hf.fst).star.const_mul (-I)).mul
    (HasFDerivAt.hasDerivAt hg.fst)).add
    (((HasFDerivAt.hasDerivAt hf.snd).star.const_mul I).mul
      (HasFDerivAt.hasDerivAt hg.snd))
  convert! h using 1
  simp only [ContinuousLinearMap.comp_apply,ContinuousLinearMap.toSpanSingleton_apply,one_smul,
    classicalODECoefficient_apply]
  rw [hr]
  simp
  ring_nf
  simp [I_sq,sub_eq_add_neg]

/-- The Hermitian Green identity holds between any two real times, with
the actual potential and the actual continued physical solutions. -/
theorem l2WholeLineSolution_green_identity (u : IntervalPairL2)
    (hu : IsClassicalRealType (intervalL2Representative u))
    (z w : ℂ) (v q : Fin 2 → ℂ) (a b : ℝ) :
    (star z-w) * (∫ t in a..b,
      star (l2WholeLineSolution u z v t).1 * (l2WholeLineSolution u w q t).1 +
        star (l2WholeLineSolution u z v t).2 * (l2WholeLineSolution u w q t).2) =
      wholeLineBoundaryForm (l2WholeLineSolution u z v b) (l2WholeLineSolution u w q b) -
        wholeLineBoundaryForm (l2WholeLineSolution u z v a) (l2WholeLineSolution u w q a) := by
  have hf := continuous_l2WholeLineSolution u z v
  have hg := continuous_l2WholeLineSolution u w q
  have hi := (((hf.fst.star.mul hg.fst).add (hf.snd.star.mul hg.snd)).const_smul (star z-w)).intervalIntegrable (μ := volume) a b
  have hd : ∀ᵐ t : ℝ, t ∈ uIcc a b → HasDerivAt (fun s => wholeLineBoundaryForm
      (l2WholeLineSolution u z v s) (l2WholeLineSolution u w q s))
      ((star z-w) * (star (l2WholeLineSolution u z v t).1 * (l2WholeLineSolution u w q t).1 +
        star (l2WholeLineSolution u z v t).2 * (l2WholeLineSolution u w q t).2)) t :=
    (ae_hasDerivAt_wholeLineBoundaryForm u hu z w v q).mono (fun _ ht _ => ht)
  have h := integral_eq_sub_of_ac_of_ae_hasDerivAt
    (absolutelyContinuousOnInterval_wholeLineBoundaryForm u z w v q a b) hi hd
  simpa only [Pi.smul_apply,Pi.mul_apply,Pi.add_apply,smul_eq_mul,
    intervalIntegral.integral_const_mul] using! h

/-- At a real spectral parameter the boundary current is conserved
between any two real times, including across integer seams. -/
theorem l2WholeLineSolution_boundaryForm_const (u : IntervalPairL2)
    (hu : IsClassicalRealType (intervalL2Representative u))
    (z : ℝ) (v q : Fin 2 → ℂ) (a b : ℝ) :
    wholeLineBoundaryForm (l2WholeLineSolution u z v b) (l2WholeLineSolution u z q b) =
      wholeLineBoundaryForm (l2WholeLineSolution u z v a) (l2WholeLineSolution u z q a) := by
  have h := l2WholeLineSolution_green_identity u hu z z v q a b
  apply sub_eq_zero.mp
  simpa only [star_def,conj_ofReal,sub_self,zero_mul] using h.symm

end NLS.ZakharovShabat
