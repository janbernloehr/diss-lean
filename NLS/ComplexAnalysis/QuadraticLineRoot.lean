import NLS.ComplexAnalysis.PrescribedAnalyticSquareRoot

/-! # Analytic roots after squaring a line parameter

The radicand `a² + u²*d` has a root analytic near `u = 0` with value `a`,
even when `a = 0`. This supplies simultaneous lifts through finitely many
zero coordinate squares using the same squared line parameter.
-/
noncomputable section
open Set
namespace NLS.ComplexAnalysis

/-- A prescribed root of a quadratic line radicand. -/
def quadraticLineRoot (a d u : ℂ) : ℂ :=
  if a = 0 then u*Complex.sqrt d
  else prescribedSquareRoot (fun v : ℂ => a^2+v^2*d) a u

@[simp] theorem quadraticLineRoot_zero (a d : ℂ) : quadraticLineRoot a d 0 = a := by
  by_cases ha : a = 0
  · simp [quadraticLineRoot,ha]
  · rw [quadraticLineRoot,if_neg ha]
    exact prescribedSquareRoot_base _ a ha 0 (by simp)

/-- The square identity is global, though analyticity is only local. -/
theorem quadraticLineRoot_sq (a d u : ℂ) : (quadraticLineRoot a d u)^2 = a^2+u^2*d := by
  by_cases ha : a = 0
  · have hd : (Complex.sqrt d)^2 = d := by
      have he := Complex.cpow_nat_inv_pow d (Nat.succ_ne_zero 1)
      norm_num at he
      simpa only [Complex.sqrt,one_div] using he
    simp [quadraticLineRoot,ha,mul_pow,hd]
  · rw [quadraticLineRoot,if_neg ha]
    exact prescribedSquareRoot_sq _ a ha u

/-- The prescribed root is analytic at the squared line's center. -/
theorem analyticAt_quadraticLineRoot (a d : ℂ) : AnalyticAt ℂ (quadraticLineRoot a d) 0 := by
  change AnalyticAt ℂ (fun u => quadraticLineRoot a d u) 0
  by_cases ha : a = 0
  · simp only [quadraticLineRoot,if_pos ha]
    exact analyticAt_id.mul analyticAt_const
  · have hf : AnalyticOnNhd ℂ (fun u : ℂ => a^2+u^2*d) univ := by
      intro u _
      exact analyticAt_const.add ((analyticAt_id.pow 2).mul analyticAt_const)
    have hmem := mem_prescribedSquareRootDomain (fun u : ℂ => a^2+u^2*d) a ha 0 (by simp)
    simpa only [quadraticLineRoot,if_neg ha] using analyticOnNhd_prescribedSquareRoot _ a hf 0 hmem

end NLS.ComplexAnalysis
