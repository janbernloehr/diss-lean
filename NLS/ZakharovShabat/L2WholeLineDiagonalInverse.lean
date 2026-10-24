import NLS.ZakharovShabat.L2WholeLineScalarODEInverse

/-! # Bounded diagonal first-order solution maps on the original L2 space -/
noncomputable section
set_option autoImplicit false
open MeasureTheory
open NLS.FunctionalAnalysis
namespace NLS.ZakharovShabat

/-- Apply the two verified scalar inverses in the original pair coordinates. -/
def wholeLineDiagonalODEInverse (α β : ℂ) (hα : α.re ≠ 0) (hβ : β.re ≠ 0) :
    WholeLineL2 →L[ℂ] WholeLineL2 :=
  wholeLineFirstEmbedding.comp ((wholeLineScalarODEInverse α hα).comp wholeLineFirstCoordinate)+
    wholeLineSecondEmbedding.comp ((wholeLineScalarODEInverse β hβ).comp wholeLineSecondCoordinate)

/-- The bounded diagonal solution is globally L2 and locally AC, with its
literal inhomogeneous differential equation almost everywhere. -/
theorem wholeLineDiagonalODEInverse_exists_AC_solution
    (α β : ℂ) (hα : α.re ≠ 0) (hβ : β.re ≠ 0) (h : WholeLineL2) :
    ∃ y : ℝ → ℂ × ℂ,
      wholeLineL2Pair (wholeLineDiagonalODEInverse α β hα hβ h) =ᵐ[volume] y ∧
      MemLp y 2 volume ∧ (∀ a b : ℝ, AbsolutelyContinuousOnInterval y a b) ∧
      ∀ᵐ t : ℝ, HasDerivAt y
        (α*(y t).1+(wholeLineL2Pair h t).1,β*(y t).2+(wholeLineL2Pair h t).2) t := by
  obtain ⟨y1,he1,hm1,hac1,hd1⟩ :=
    wholeLineScalarODEInverse_exists_AC_solution α hα (wholeLineFirstCoordinate h)
  obtain ⟨y2,he2,hm2,hac2,hd2⟩ :=
    wholeLineScalarODEInverse_exists_AC_solution β hβ (wholeLineSecondCoordinate h)
  let f1 := wholeLineScalarODEInverse α hα (wholeLineFirstCoordinate h)
  let f2 := wholeLineScalarODEInverse β hβ (wholeLineSecondCoordinate h)
  refine ⟨fun t => (y1 t,y2 t),?_,memLp_prod_iff.mpr ⟨hm1,hm2⟩,?_,?_⟩
  · change wholeLineL2Pair (wholeLineFirstEmbedding f1+wholeLineSecondEmbedding f2) =ᵐ[volume] _
    filter_upwards [Lp.coeFn_add (wholeLineFirstEmbedding f1) (wholeLineSecondEmbedding f2),
      wholeLineFirstEmbedding_pair_ae f1,wholeLineSecondEmbedding_pair_ae f2,he1,he2]
      with t hadd hf1 hf2 hy1 hy2
    change WithLp.ofLp ((wholeLineFirstEmbedding f1+wholeLineSecondEmbedding f2) t) = _
    rw [hadd]
    change wholeLineL2Pair (wholeLineFirstEmbedding f1) t+
      wholeLineL2Pair (wholeLineSecondEmbedding f2) t = _
    rw [hf1,hf2,hy1,hy2]
    simp
  · intro a b
    have h1 := absolutelyContinuousOnInterval_clm (hac1 a b)
      ((ContinuousLinearMap.id ℝ ℂ).prod (0 : ℂ →L[ℝ] ℂ))
    have h2 := absolutelyContinuousOnInterval_clm (hac2 a b)
      ((0 : ℂ →L[ℝ] ℂ).prod (ContinuousLinearMap.id ℝ ℂ))
    simpa [Pi.add_def] using h1.add h2
  · filter_upwards [hd1,hd2,wholeLineFirstCoordinate_ae h,wholeLineSecondCoordinate_ae h]
      with t ht1 ht2 hh1 hh2
    simpa only [hh1,hh2] using ht1.prodMk ht2

end NLS.ZakharovShabat
