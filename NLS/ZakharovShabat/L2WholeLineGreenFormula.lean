import NLS.ZakharovShabat.L2WholeLineFloquetGreenFormula
import NLS.ZakharovShabat.L2FloquetNonrealTrace

/-! # Actual nonreal Green formulas without an assumed Floquet basis -/
noncomputable section
set_option autoImplicit false
open MeasureTheory Matrix Module Complex
namespace NLS.ZakharovShabat

/-- At every nonreal parameter, the original physical resolvent admits the
stable/unstable Green formula with actual reciprocal roots of the monodromy. -/
theorem wholeLineNonrealResolvent_exists_green_formula (u : IntervalPairL2)
    (hu : IsClassicalRealType (intervalL2Representative u)) (z : ℂ) (hz : z.im ≠ 0) :
    ∃ μ ν : ℂ, (l2Monodromy u z).trace = μ+ν ∧ μ*ν = 1 ∧
      ‖μ‖ < 1 ∧ 1 < ‖ν‖ ∧ ∀ (g : WholeLineL2) (a c : ℝ),
      (∀ᵐ t : ℝ, t ≤ a → wholeLineL2Pair g t = 0) →
      (∀ᵐ t : ℝ, c ≤ t → wholeLineL2Pair g t = 0) →
      wholeLineL2Pair (wholeLineNonrealResolvent u hu z hz g) =ᵐ[volume]
        (fun t => (∫ s in a..t, wholeLineMatrixAction (l2FloquetModeKernel u z μ ν t s)
          (I*(wholeLineL2Pair g s).1,-I*(wholeLineL2Pair g s).2))-
        ∫ s in t..c, wholeLineMatrixAction (l2FloquetModeKernel u z ν μ t s)
          (I*(wholeLineL2Pair g s).1,-I*(wholeLineL2Pair g s).2)) := by
  obtain ⟨μ,ν,b,hsum,hprod,hpos,hstable,hunstable,hμ,hν⟩ :=
    l2Monodromy_nonreal_exists_stable_unstable_basis_with_trace u hu z hz
  have hne : μ ≠ ν := by intro h; rw [h] at hstable; linarith
  have h0 : ∀ j, ![μ,ν] j ≠ 0 := by
    intro j
    fin_cases j
    · exact norm_pos_iff.mp hpos
    · exact norm_pos_iff.mp (lt_trans zero_lt_one hunstable)
  have hM : ∀ j, l2Monodromy u z *ᵥ b j = ![μ,ν] j • b j := by
    intro j
    fin_cases j
    · exact hμ
    · exact hν
  obtain ⟨C,_,hC⟩ := bounded_l2FloquetPeriodicMatrix_and_inverse u z b ![μ,ν] h0 hM
  have hlogμ : (Complex.log μ).re < 0 := by
    rw [Complex.log_re]
    exact Real.log_neg hpos hstable
  have hlogν : 0 < (Complex.log ν).re := by
    rw [Complex.log_re]
    exact Real.log_pos hunstable
  exact ⟨μ,ν,hsum,hprod,hstable,hunstable,fun g a c hl hr =>
    wholeLineNonrealResolvent_ae_green_formula u hu z hz μ ν hne b hμ hν
      hlogμ hlogν C hC g a c hl hr⟩

end NLS.ZakharovShabat
