import NLS.KdV.HillEnergyProductReality

/-! At ACTUAL original real Hill zero data, the filled coordinate
variation is nonzero on the ENTIRE selected original gap, including
the selected zero and every collapsed gap. This is the numerator
nonvanishing required by the PERIOD diagonal mean-value argument. -/
noncomputable section
open Set Complex
open scoped ENNReal Classical
namespace NLS.KdV

theorem hillEnergySequenceProduct_real_gap_zero_iff (n m : ℕ+) (hmn : m ≠ n)
    (q : PeriodOneRealHminusOne) (E : ℝ)
    (hE : E ∈ Icc (hillHminusLabels q.val q.property (2*(m:ℕ)-1))
      (hillHminusLabels q.val q.property (2*(m:ℕ)))) :
    hillEnergySequenceProduct n ((E:ℂ),hillHminusPsiZeroDisplacement n q) = 0 ↔
      E = hillHminusCanonicalPsiRealZero n m q.val q.property := by
  constructor
  · intro hp
    have hz : hillHminusCanonicalPsi n ((E:ℂ),q.val) = 0 := by
      rw [hillHminusCanonicalPsi_eq_scalar_mul_literalProduct n (E:ℂ) q]
      change _*hillEnergySequenceProduct n ((E:ℂ),hillHminusPsiZeroDisplacement n q) = 0
      rw [hp,mul_zero]
    exact hillHminusCanonicalPsiRealZero_unique n m q.val q.property hmn E hE hz
  · intro he
    rw [he,← hillEnergySequenceZero_real n m q]
    exact hillEnergySequenceProduct_retained_root n m hmn _

theorem hillEnergyProductCoordinateDerivative_ne_zero_on_real_gap (n m : ℕ+) (hmn : m ≠ n)
    (q : PeriodOneRealHminusOne) (E : ℝ)
    (hE : E ∈ Icc (hillHminusLabels q.val q.property (2*(m:ℕ)-1))
      (hillHminusLabels q.val q.property (2*(m:ℕ)))) :
    hillEnergyProductCoordinateDerivative n m ((E:ℂ),hillHminusPsiZeroDisplacement n q) ≠ 0 := by
  by_cases he : E = hillHminusCanonicalPsiRealZero n m q.val q.property
  · rw [he,← hillEnergySequenceZero_real n m q]
    exact hillEnergyProductCoordinateDerivative_real_diagonal_ne_zero n m hmn q
  · have hp : hillEnergySequenceProduct n ((E:ℂ),hillHminusPsiZeroDisplacement n q) ≠ 0 :=
      fun hz => he ((hillEnergySequenceProduct_real_gap_zero_iff n m hmn q E hE).mp hz)
    have h := hillEnergyProductCoordinateDerivative_restore n m hmn (E:ℂ) (hillHminusPsiZeroDisplacement n q)
    intro hz
    rw [hz,mul_zero] at h
    exact mul_ne_zero (by exact_mod_cast m.ne_zero) hp h.symm

end NLS.KdV
