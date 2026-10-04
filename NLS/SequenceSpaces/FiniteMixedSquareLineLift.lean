import NLS.SequenceSpaces.MixedSquare
import NLS.ComplexAnalysis.QuadraticLineRoot

/-! # Analytic lifts of finite mixed-coordinate lines

After replacing the line parameter by its square, a direction supported
on finitely many coordinates has a lift analytic at zero. A single lift
handles nonzero and zero tail entries as well as retained head entries.
-/
noncomputable section
open Set
open scoped ENNReal
namespace NLS.Coeff
variable {p q : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ q)]

/-- Lift a finite mixed-coordinate line after squaring its parameter. -/
def finiteMixedSquareLineLift (S T : Finset ℤ) (a : Coeff p) (d : Coeff q) (u : ℂ) : Coeff p :=
  a+∑ k ∈ T, lp.single p k (if k ∈ S then u^2*d k
    else ComplexAnalysis.quadraticLineRoot (a k) (d k) u-a k)

omit [Fact (1 ≤ p)] [Fact (1 ≤ q)] in
@[simp] theorem finiteMixedSquareLineLift_apply (S T : Finset ℤ) (a : Coeff p) (d : Coeff q)
    (u : ℂ) (n : ℤ) :
    finiteMixedSquareLineLift S T a d u n =
      if n ∈ T then (if n ∈ S then a n+u^2*d n
        else ComplexAnalysis.quadraticLineRoot (a n) (d n) u) else a n := by
  classical
  change (lp.evalₗ (𝕜 := ℂ) (fun _ : ℤ => ℂ) p n)
    (a+∑ k ∈ T, lp.single p k (if k ∈ S then u^2*d k
      else ComplexAnalysis.quadraticLineRoot (a k) (d k) u-a k)) = _
  rw [map_add,map_sum]
  by_cases hn : n ∈ T <;> by_cases hs : n ∈ S <;>
    simp [lp.evalₗ_apply,lp.single_apply,Pi.single_apply,hn,hs]

omit [Fact (1 ≤ p)] [Fact (1 ≤ q)] in
@[simp] theorem finiteMixedSquareLineLift_zero (S T : Finset ℤ) (a : Coeff p) (d : Coeff q) :
    finiteMixedSquareLineLift S T a d 0 = a := by
  ext n
  by_cases hn : n ∈ T <;> by_cases hs : n ∈ S <;> simp [hn,hs]

omit [Fact (1 ≤ q)] in
/-- Only finitely many analytic coordinate changes are added to the center. -/
theorem analyticAt_finiteMixedSquareLineLift (S T : Finset ℤ) (a : Coeff p) (d : Coeff q) :
    AnalyticAt ℂ (finiteMixedSquareLineLift S T a d) 0 := by
  classical
  apply analyticAt_const.add
  apply T.analyticAt_fun_sum
  intro k _
  change AnalyticAt ℂ (fun u : ℂ => (lp.singleContinuousLinearMap ℂ (fun _ : ℤ => ℂ) p k)
    (if k ∈ S then u^2*d k else ComplexAnalysis.quadraticLineRoot (a k) (d k) u-a k)) 0
  apply AnalyticAt.comp (x := 0) ((lp.singleContinuousLinearMap ℂ (fun _ : ℤ => ℂ) p k).analyticAt _)
  by_cases hk : k ∈ S
  · simp only [if_pos hk]
    exact (analyticAt_id.pow 2).mul analyticAt_const
  · simp only [if_neg hk]
    exact (ComplexAnalysis.analyticAt_quadraticLineRoot (a k) (d k)).sub analyticAt_const

variable [p.HolderTriple p q]

/-- The mixed-square image is exactly the prescribed finite line at `u²`. -/
theorem mixedSquare_finiteMixedSquareLineLift (S T : Finset ℤ) (a : Coeff p) (d : Coeff q) (u : ℂ) :
    mixedSquare S (finiteMixedSquareLineLift S T a d u) = mixedSquare S a+u^2 • truncate T d := by
  ext n
  change mixedSquare S (finiteMixedSquareLineLift S T a d u) n =
    mixedSquare S a n+u^2*(truncate T d n)
  by_cases hn : n ∈ T <;> by_cases hs : n ∈ S <;>
    simp [hn,hs,ComplexAnalysis.quadraticLineRoot_sq]

/-- Simultaneously lift finite directions in both sequence components. -/
def pairFiniteMixedSquareLineLift (S T : Finset ℤ) (z : Coeff p × Coeff p)
    (d : Coeff q × Coeff q) (u : ℂ) : Coeff p × Coeff p :=
  (finiteMixedSquareLineLift S T z.1 d.1 u,finiteMixedSquareLineLift S T z.2 d.2 u)

omit [Fact (1 ≤ p)] [Fact (1 ≤ q)] [p.HolderTriple p q] in
@[simp] theorem pairFiniteMixedSquareLineLift_zero (S T : Finset ℤ) (z : Coeff p × Coeff p)
    (d : Coeff q × Coeff q) : pairFiniteMixedSquareLineLift S T z d 0 = z := by
  simp [pairFiniteMixedSquareLineLift]

omit [Fact (1 ≤ q)] [p.HolderTriple p q] in
theorem analyticAt_pairFiniteMixedSquareLineLift (S T : Finset ℤ) (z : Coeff p × Coeff p)
    (d : Coeff q × Coeff q) : AnalyticAt ℂ (pairFiniteMixedSquareLineLift S T z d) 0 :=
  (analyticAt_finiteMixedSquareLineLift S T z.1 d.1).prod
    (analyticAt_finiteMixedSquareLineLift S T z.2 d.2)

theorem pairMixedSquare_pairFiniteMixedSquareLineLift (S T : Finset ℤ) (z : Coeff p × Coeff p)
    (d : Coeff q × Coeff q) (u : ℂ) :
    pairMixedSquare S (pairFiniteMixedSquareLineLift S T z d u) =
      pairMixedSquare S z+u^2 • truncatePair T d :=
  Prod.ext (mixedSquare_finiteMixedSquareLineLift S T z.1 d.1 u)
    (mixedSquare_finiteMixedSquareLineLift S T z.2 d.2 u)

end NLS.Coeff
