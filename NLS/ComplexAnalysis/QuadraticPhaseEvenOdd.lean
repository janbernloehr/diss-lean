import NLS.ComplexAnalysis.OddSquareDescent

/-! Entire even/odd coefficients of a root exponential. Their joint
analyticity uses square descent, so no continuous square-root choice
or division by a vanishing radicand is required. -/
noncomputable section
open Set Metric Complex Filter Topology
namespace NLS.ComplexAnalysis

def rootPhaseExponential (t : ℂ × ℂ) : ℂ := Complex.exp (I*t.1*t.2)

def rootPhaseEven (t : ℂ × ℂ) : ℂ :=
  (rootPhaseExponential (Complex.sqrt t.1,t.2)+rootPhaseExponential (-Complex.sqrt t.1,t.2))/2

def rootPhaseOdd (t : ℂ × ℂ) : ℂ := oddSquareDescent rootPhaseExponential t

theorem analyticOnNhd_rootPhaseExponential : AnalyticOnNhd ℂ rootPhaseExponential univ := by
  intro t _
  exact ((analyticAt_const.mul analyticAt_fst).mul analyticAt_snd).cexp

theorem analyticOnNhd_rootPhaseEven : AnalyticOnNhd ℂ rootPhaseEven univ := by
  let F : ℂ × ℂ → ℂ := fun t => (rootPhaseExponential t+rootPhaseExponential (-t.1,t.2))/2
  have hF : AnalyticOnNhd ℂ F univ := by
    intro t _
    exact ((analyticOnNhd_rootPhaseExponential t (mem_univ _)).add
      ((analyticOnNhd_rootPhaseExponential (-t.1,t.2) (mem_univ _)).comp
        (f := fun t : ℂ × ℂ => (-t.1,t.2)) (analyticAt_fst.neg.prod analyticAt_snd))).div_const
  exact analyticOnNhd_entire_even_square_descent F hF (by intro h z; dsimp only [F]; rw [neg_neg]; ring)
    Complex.sqrt complex_sqrt_sq

theorem analyticOnNhd_rootPhaseOdd : AnalyticOnNhd ℂ rootPhaseOdd univ := by
  have h := analyticOnNhd_oddSquareDescent rootPhaseExponential (univ : Set ℂ) isOpen_univ
    (analyticOnNhd_rootPhaseExponential.mono (subset_univ _))
  change AnalyticOnNhd ℂ (oddSquareDescent rootPhaseExponential) univ
  simpa only [univ_prod_univ] using h

theorem rootPhaseEven_sq (r h : ℂ) :
    rootPhaseEven (r^2,h) = (Complex.exp (I*r*h)+Complex.exp (-I*r*h))/2 := by
  rcases eq_or_eq_neg_of_sq_eq_sq (Complex.sqrt (r^2)) r (complex_sqrt_sq (r^2)) with he | he
  · simp only [rootPhaseEven,rootPhaseExponential,he,mul_neg,neg_mul]
  · simp only [rootPhaseEven,rootPhaseExponential,he,neg_neg,mul_neg,neg_mul]
    ring

theorem mul_rootPhaseOdd_sq (r h : ℂ) :
    r*rootPhaseOdd (r^2,h) = (Complex.exp (I*r*h)-Complex.exp (-I*r*h))/2 := by
  rw [rootPhaseOdd,oddSquareDescent_sq]
  by_cases hr : r = 0
  · simp [hr]
  · rw [oddPartQuotient_eq_div rootPhaseExponential h r hr]
    dsimp only [rootPhaseExponential]
    field_simp [hr]

theorem rootPhase_even_add_odd (r h : ℂ) :
    rootPhaseEven (r^2,h)+r*rootPhaseOdd (r^2,h) = Complex.exp (I*r*h) := by
  rw [rootPhaseEven_sq,mul_rootPhaseOdd_sq]
  ring

theorem rootPhase_even_sub_odd (r h : ℂ) :
    rootPhaseEven (r^2,h)-r*rootPhaseOdd (r^2,h) = Complex.exp (-I*r*h) := by
  rw [rootPhaseEven_sq,mul_rootPhaseOdd_sq]
  ring

theorem rootPhaseEven_zero (h : ℂ) : rootPhaseEven (0,h) = 1 := by
  simpa using rootPhaseEven_sq 0 h

end NLS.ComplexAnalysis
