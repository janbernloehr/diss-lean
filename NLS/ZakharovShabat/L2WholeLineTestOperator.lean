import NLS.ZakharovShabat.L2WholeLineLocalIntegrability
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.Deriv.Support
import Mathlib.MeasureTheory.Function.LpSpace.Indicator

/-! # The physical differential expression on compactly supported tests

Local square integrability of the actual periodic potential suffices for
its product with a continuous compactly supported function to belong to
L2 on the whole line. For compactly supported C1 pairs, both derivatives
and potential terms are therefore in the actual whole-line L2 space.
-/
noncomputable section
set_option autoImplicit false
open Set MeasureTheory
namespace NLS.ZakharovShabat

/-- A locally square-integrable scalar coefficient times a continuous
compactly supported test function is globally square integrable. -/
theorem memLp_mul_compact_test {a g : ℝ → ℂ}
    (ha : ∀ K : Set ℝ, IsCompact K → MemLp a 2 (volume.restrict K))
    (hg : Continuous g) (hgc : HasCompactSupport g) :
    MemLp (fun t => a t * g t) 2 volume := by
  classical
  have ha' : MemLp ((tsupport g).indicator a) 2 volume :=
    (memLp_indicator_iff_restrict hgc.measurableSet).mpr (ha _ hgc)
  have hm : MemLp (fun t => ((tsupport g).indicator a) t * g t) 2 volume :=
    (hg.memLp_top_of_hasCompactSupport hgc volume).mul' ha'
  have he : (fun t => ((tsupport g).indicator a) t * g t) = (fun t => a t * g t) := by
    funext t
    by_cases ht : t ∈ tsupport g
    · simp [ht]
    · simp [ht,image_eq_zero_of_notMem_tsupport ht]
  rwa [he] at hm

/-- The off-diagonal potential part of the original physical expression
maps continuous compactly supported pairs into whole-line L2. -/
theorem memLp_l2WholeLinePotential_mul_test (u : IntervalPairL2)
    {f : ℝ → ℂ × ℂ} (hf : Continuous f) (hfc : HasCompactSupport f) :
    MemLp (fun t => ((l2WholeLinePotential u t).1 * (f t).2,
      (l2WholeLinePotential u t).2 * (f t).1)) 2 volume := by
  apply memLp_prod_iff.mpr
  constructor
  · exact memLp_mul_compact_test (fun K hK => (memLp_l2WholeLinePotential_on_compact u hK).fst)
      hf.snd (hfc.comp_left (g := Prod.snd) rfl)
  · exact memLp_mul_compact_test (fun K hK => (memLp_l2WholeLinePotential_on_compact u hK).snd)
      hf.fst (hfc.comp_left (g := Prod.fst) rfl)

/-- Every compactly supported C1 test pair has an L2 physical operator
image, with the original signed derivatives and actual periodic potential. -/
theorem memLp_physicalOperator_l2WholeLine_test (u : IntervalPairL2)
    {f : ℝ → ℂ × ℂ} (hf : ContDiff ℝ 1 f) (hfc : HasCompactSupport f) :
    MemLp (physicalOperator (l2WholeLinePotential u) f) 2 volume := by
  have hpot := memLp_l2WholeLinePotential_mul_test u hf.continuous hfc
  have hd1 : MemLp (deriv (fun t => (f t).1)) 2 volume :=
    hf.fst.continuous_deriv_one.memLp_of_hasCompactSupport
      (hfc.comp_left (g := Prod.fst) rfl).deriv
  have hd2 : MemLp (deriv (fun t => (f t).2)) 2 volume :=
    hf.snd.continuous_deriv_one.memLp_of_hasCompactSupport
      (hfc.comp_left (g := Prod.snd) rfl).deriv
  exact memLp_prod_iff.mpr ⟨(hd1.const_mul Complex.I).add hpot.fst,
    (hd2.const_mul (-Complex.I)).add hpot.snd⟩

end NLS.ZakharovShabat
