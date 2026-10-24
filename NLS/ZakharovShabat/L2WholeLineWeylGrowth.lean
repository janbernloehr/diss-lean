import NLS.ZakharovShabat.L2WholeLineWeylCriterion

/-! # A growing-mass criterion for the original whole-line spectrum -/
noncomputable section
set_option autoImplicit false
namespace NLS.ZakharovShabat

/-- Linear growth of the squared input norm with uniformly bounded
squared residual forces spectrum membership. This form suits Floquet
cutoffs directly and does not require choosing normalized representatives. -/
theorem mem_wholeLineSpectrum_of_mass_growth (u : IntervalPairL2) (z : ℂ)
    (m K : ℝ) (hm : 0 < m)
    (hf : ∀ n : ℕ, ∃ f : (wholeLineMinimalOperator u).closure.domain,
      (n : ℝ) * m ≤ ‖(f : WholeLineL2)‖ ^ 2 ∧ ‖wholeLinePencil u z f‖ ^ 2 ≤ K) :
    z ∈ wholeLineSpectrum u := by
  intro hz
  obtain ⟨C,hC,hbound⟩ := wholeLinePencil_norm_bound_of_mem_resolvent u z hz
  obtain ⟨n,hn⟩ := exists_nat_gt (C^2*K/m)
  obtain ⟨f,hmass,hres⟩ := hf n
  have hb := hbound f
  have hsq : ‖(f : WholeLineL2)‖ ^ 2 ≤ C^2 * ‖wholeLinePencil u z f‖ ^ 2 := by
    nlinarith [norm_nonneg (f : WholeLineL2),norm_nonneg (wholeLinePencil u z f)]
  have hupper := mul_le_mul_of_nonneg_left hres (sq_nonneg C)
  have hlower := (div_lt_iff₀ hm).mp hn
  nlinarith

end NLS.ZakharovShabat
