import NLS.KdV.PhysicalDiagonalFrequencySymbol

/-! The actual diagonal contribution to the corrected KdV frequency
has a finite-exponent analytic symbol near every real rough source.
Its action-fiber descent and the full compactness conclusion are separate. -/
noncomputable section
set_option autoImplicit false
open Set Complex NLS.KdV NLS.ZakharovShabat
namespace NLS.Articles.KdVKdV2Frequencies

theorem theorem_1_2_local_diagonal_symbol
    (q0 : PeriodOneHminusOne) (hr0 : IsRealPeriodOneHminusOne q0) (L : ℝ) :
    ∃ B : PhysicalMiuraFrequencyChart, L<B.shift ∧
      ∃ T : Set PeriodOneHminusOne, IsOpen T ∧ q0∈T ∧ T⊆B.domain ∧
        ∃ M : ℝ, 0≤M ∧ ∃ S : PeriodOneHminusOne → Coeff 2,
          AnalyticOnNhd ℂ S T ∧ (∀ q∈T, ‖S q‖≤M) ∧
          (∀ q∈T, ∀ j : ℤ, j≤0 → S q j=0) ∧
          ∀ p : RealPeriodOneHillPotential, hillOriginalHminusSource p.val∈T → ∀ n : ℕ+,
            B.correction n (hillOriginalHminusSource p.val)+
                6*(hillRealGapIntegral p.val p.property.1 p.property.2 (n : ℕ) 0 : ℂ)=
              B.offDiagonalCorrection n (hillOriginalHminusSource p.val)+
                6*(hillRealGapIntegral p.val p.property.1 p.property.2 (n : ℕ) 0 : ℂ)*
                  S (hillOriginalHminusSource p.val) (n : ℤ) := by
  obtain ⟨B,hq0,hL,H⟩ := exists_physicalMiuraFrequencyChart_with_original_estimates q0 hr0 L
  exact ⟨B,hL,B.exists_local_diagonal_frequency_symbol H q0 hq0 hr0⟩

end NLS.Articles.KdVKdV2Frequencies
