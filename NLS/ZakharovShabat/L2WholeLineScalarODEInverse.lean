import NLS.ZakharovShabat.L2WholeLineScalarMaps
import NLS.ZakharovShabat.L2WholeLineFreePotential
import NLS.ZakharovShabat.L2WholeLineClosureRepresentative
import NLS.ZakharovShabat.L2WholeLineNonrealResolvent

/-! # Bounded scalar first-order inverses from the free physical resolvent

A nonzero real part of alpha makes i*alpha nonreal. The verified free
whole-line resolvent therefore supplies an L2 solution of y'=alpha*y+h.
-/
noncomputable section
set_option autoImplicit false
open Set Complex MeasureTheory
open NLS.FunctionalAnalysis
namespace NLS.ZakharovShabat

/-- Bounded solution map for the scalar first-order equation. -/
def wholeLineScalarODEInverse (α : ℂ) (hα : α.re ≠ 0) :
    WholeLineScalarL2 →L[ℂ] WholeLineScalarL2 :=
  wholeLineFirstCoordinate.comp
    ((wholeLineNonrealResolvent 0 isClassicalRealType_intervalL2_zero (I*α) (by simpa using hα)).comp
      ((-I) • wholeLineFirstEmbedding))

/-- The bounded scalar solution has a locally AC representative solving
the literal first-order equation almost everywhere on the full line. -/
theorem wholeLineScalarODEInverse_exists_AC_solution (α : ℂ) (hα : α.re ≠ 0)
    (h : WholeLineScalarL2) :
    ∃ y : ℝ → ℂ, wholeLineScalarODEInverse α hα h =ᵐ[volume] y ∧
      MemLp y 2 volume ∧ (∀ a b : ℝ, AbsolutelyContinuousOnInterval y a b) ∧
      ∀ᵐ t : ℝ, HasDerivAt y (α*y t+h t) t := by
  let g : WholeLineL2 := (-I) • wholeLineFirstEmbedding h
  have hz : (I*α).im ≠ 0 := by simpa using hα
  let f := wholeLineNonrealResolventToDomain 0 isClassicalRealType_intervalL2_zero (I*α) hz g
  have hp : (I*α) • (f : WholeLineL2) - (wholeLineMinimalOperator 0).closure f = g :=
    wholeLinePencil_nonrealResolventToDomain 0 isClassicalRealType_intervalL2_zero (I*α) hz g
  have hT : (wholeLineMinimalOperator 0).closure f = (I*α) • (f : WholeLineL2)-g :=
    eq_sub_iff_add_eq.mpr (by rw [← hp]; module)
  obtain ⟨F,he,hac,hd⟩ := wholeLineMinimalOperator_closure_exists_AC_representative 0
    isClassicalRealType_intervalL2_zero f
  have hy : wholeLineScalarODEInverse α hα h =ᵐ[volume] (fun t => (F t).1) := by
    change wholeLineFirstCoordinate (f : WholeLineL2) =ᵐ[volume] (fun t => (F t).1)
    exact (wholeLineFirstCoordinate_ae f).trans (he.mono (fun _ ht => congrArg Prod.fst ht))
  have hG : wholeLineL2Pair ((wholeLineMinimalOperator 0).closure f) =ᵐ[volume]
      (fun t => (I*α) • wholeLineL2Pair f t-wholeLineL2Pair g t) := by
    rw [hT]
    filter_upwards [Lp.coeFn_sub ((I*α) • (f : WholeLineL2)) g,
      Lp.coeFn_smul (I*α) (f : WholeLineL2)] with t hsub hsm
    simp only [Pi.sub_apply,Pi.smul_apply] at hsub hsm
    change WithLp.ofLp (((I*α) • (f : WholeLineL2)-g) t) = _
    rw [hsub,hsm]
    rfl
  have hg : wholeLineL2Pair g =ᵐ[volume] (fun t => (-I*h t,0)) := by
    filter_upwards [Lp.coeFn_smul (-I) (wholeLineFirstEmbedding h),
      wholeLineFirstEmbedding_pair_ae h] with t hsm ht
    change WithLp.ofLp (((-I) • wholeLineFirstEmbedding h) t) = _
    rw [hsm]
    change (-I) • wholeLineL2Pair (wholeLineFirstEmbedding h) t = _
    rw [ht]
    simp
  refine ⟨fun t => (F t).1,hy,(memLp_wholeLineL2Pair f |>.ae_eq he).fst,?_,?_⟩
  · intro a b
    exact absolutelyContinuousOnInterval_clm (hac a b) (ContinuousLinearMap.fst ℝ ℂ ℂ)
  · filter_upwards [hd,he,hG,hg,ae_l2WholeLinePotential_zero] with t hdt het hGt hgt hzero
    convert! (HasFDerivAt.hasDerivAt hdt.fst) using 1
    dsimp only [wholeLineWeakDerivative,Prod.fst_add,Prod.smul_fst]
    rw [hzero,hGt,hgt,het]
    simp only [Prod.smul_fst,Prod.fst_sub,Prod.fst_zero,smul_eq_mul,zero_mul,mul_zero,add_zero]
    ring_nf
    simp [I_sq]

end NLS.ZakharovShabat
