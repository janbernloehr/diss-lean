import NLS.ComplexAnalysis.ScalarTaylorCoefficient

/-! The sixth coefficient of the inverted quartic phase is the
physical centered Miura Hamiltonian combination. The fourth jet of
the remainder is unrestricted and cancels from this coefficient. -/
noncomputable section
open Complex
namespace NLS.ComplexAnalysis

theorem scalarTaylorCoefficient_quartic_phase (A : ℂ → ℂ) (hA : AnalyticAt ℂ A 0)
    (hA0 : A 0=0) (H₁ H₃ H₅ : ℂ)
    (h₁ : iteratedDeriv 1 A 0=I*H₁/2) (h₂ : iteratedDeriv 2 A 0=0)
    (h₃ : iteratedDeriv 3 A 0=3*I*H₃/4) (h₅ : iteratedDeriv 5 A 0=15*I*H₅/4) :
    scalarTaylorCoefficient 6 (fun w => (-I+w*A w)^4)=
      -(H₅/2-3*H₁*H₃+2*H₁^3)/4 := by
  let F : ℂ → ℂ := fun w => -I+w*A w
  have hF : AnalyticAt ℂ F 0 := analyticAt_const.add (analyticAt_id.mul hA)
  have h0 : scalarTaylorCoefficient 0 F=-I := by simp [scalarTaylorCoefficient,F]
  have h1 : scalarTaylorCoefficient 1 F=0 := by
    rw [scalarTaylorCoefficient_const_add_succ (-I) hA 0]
    simp [scalarTaylorCoefficient,hA0]
  have h2 : scalarTaylorCoefficient 2 F=I*H₁/2 := by
    rw [scalarTaylorCoefficient_const_add_succ (-I) hA 1]
    simp [scalarTaylorCoefficient,h₁]
  have h3 : scalarTaylorCoefficient 3 F=0 := by
    rw [scalarTaylorCoefficient_const_add_succ (-I) hA 2]
    simp [scalarTaylorCoefficient,h₂]
  have h4 : scalarTaylorCoefficient 4 F=I*H₃/8 := by
    rw [scalarTaylorCoefficient_const_add_succ (-I) hA 3]
    norm_num [scalarTaylorCoefficient,h₃,Nat.factorial]
    ring
  have h6 : scalarTaylorCoefficient 6 F=I*H₅/32 := by
    rw [scalarTaylorCoefficient_const_add_succ (-I) hA 5]
    norm_num [scalarTaylorCoefficient,h₅,Nat.factorial]
    ring
  have he : (fun w => (-I+w*A w)^4)=(fun w => (F w*F w)*(F w*F w)) := by funext w; dsimp [F]; ring
  have hFF : AnalyticAt ℂ (fun w => F w*F w) 0 := hF.mul hF
  rw [he,scalarTaylorCoefficient_mul hFF hFF]
  simp only [scalarTaylorCoefficient_mul hF hF]
  norm_num only [Finset.sum_range_succ,Finset.sum_range_zero,Nat.reduceAdd,Nat.reduceSub,zero_add,
    h0,h1,h2,h3,h4,h6,zero_mul,mul_zero,add_zero]
  ring_nf
  simp only [I_pow_four]
  ring

end NLS.ComplexAnalysis
