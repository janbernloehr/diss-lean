import NLS.KdV.PhysicalDiagonalActionCancellation

/-! The original +6I counterterm cancels the free diagonal physical
moment near every original real Hill source. The remaining norm and
compactness estimates are not asserted by this scalar identity. -/
noncomputable section
set_option autoImplicit false
open Set Metric Complex NLS.KdV NLS.ZakharovShabat
namespace NLS.Articles.KdVKdV2Frequencies

theorem theorem_1_2_local_diagonal_cancellation
    (q : RealPeriodOneHillPotential) (M : ℝ) :
    ∃ B : PhysicalMiuraFrequencyChart,
      hillOriginalHminusSource q.val∈B.domain ∧ M<B.shift ∧
    ∃ W : Set (CoeffPair 2),
      ∃ C : SourceFullAbelianUniformCauchyFamily (by norm_num) (by norm_num) W,
        ∃ r : ℝ, 0<r ∧
          (∀ n k : ℤ, AnalyticOnNhd ℂ (C.normalizedSecondMoment B.psi.family.roots n k)
            (ball (hillMiuraDiagonal (B.psi.miura.lift (hillOriginalHminusSource q.val))) r)) ∧
          (∀ n : ℤ, AnalyticOnNhd ℂ (C.regularDiagonalSecondMomentError B.psi.family.roots n)
            (ball (hillMiuraDiagonal (B.psi.miura.lift (hillOriginalHminusSource q.val))) r) ∧
            AnalyticOnNhd ℂ (C.regularFirstWeightedActionError n)
              (ball (hillMiuraDiagonal (B.psi.miura.lift (hillOriginalHminusSource q.val))) r)) ∧
          ∀ p : RealPeriodOneHillPotential, hillOriginalHminusSource p.val∈B.domain →
            hillMiuraDiagonal (B.psi.miura.lift (hillOriginalHminusSource p.val))∈
              ball (hillMiuraDiagonal (B.psi.miura.lift (hillOriginalHminusSource q.val))) r →
            ∀ n : ℕ+,
            let ψ := hillMiuraDiagonal (B.psi.miura.lift (hillOriginalHminusSource p.val))
            B.correction n (hillOriginalHminusSource p.val)+
                6*(hillRealGapIntegral p.val p.property.1 p.property.2 (n : ℕ) 0 : ℂ) =
              B.offDiagonalCorrection n (hillOriginalHminusSource p.val)+
                3*(sourcePeriodicGapDisplacement (by norm_num) (by norm_num) ψ (n : ℤ))^2*
                  (C.regularFirstWeightedActionError (n : ℤ) ψ-
                    (n : ℂ)*C.regularDiagonalSecondMomentError B.psi.family.roots (n : ℤ) ψ)+
                12*(n : ℂ)*(sourcePeriodicGapDisplacement (by norm_num) (by norm_num) ψ (-(n : ℤ)))^2*
                  C.normalizedSecondMoment B.psi.family.roots (n : ℤ) (-(n : ℤ)) ψ := by
  obtain ⟨B,hq,hM,H⟩ := exists_physicalMiuraFrequencyChart_with_original_estimates
    (hillOriginalHminusSource q.val) (hillOriginalHminusSource_real q.val q.property.2) M
  exact ⟨B,hq,hM,B.exists_regular_diagonal_action_cancellation H q hq⟩

end NLS.Articles.KdVKdV2Frequencies
