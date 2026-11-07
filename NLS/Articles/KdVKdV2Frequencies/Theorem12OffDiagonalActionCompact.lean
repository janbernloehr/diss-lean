import NLS.Articles.KdVKdV2Frequencies.OffDiagonalRawActionCompact
import NLS.Articles.KdVKdV2Frequencies.OffDiagonalOriginalActionRecovery

/-! The off-diagonal contribution to Theorem1.2(ii) has compact action
derivatives at EVERY original intermediate positive action point. Its
physical source realizations have exactly the original Arnold actions.
The full diagonal cancellation and corrected derivative remain open. -/
noncomputable section
set_option autoImplicit false
open Set Complex NLS.KdV NLS.ZakharovShabat
open NLS.Articles.KdVConvexity
open scoped ENNReal
namespace NLS.Articles.KdVKdV2Frequencies

theorem GlobalRoughAbelianForwardData.theorem_1_2_offDiagonal_action_compact
    (D : GlobalRoughAbelianForwardData) :
    ∃ Ω : Set PeriodOneHminusOne, ∃ I : PeriodOneHminusOne → BaseActionSpace,
      IsOpen Ω ∧ {q | IsRealPeriodOneHminusOne q}⊆Ω ∧ AnalyticOnNhd ℂ I Ω ∧
      (∀ q (hr : IsRealPeriodOneHminusOne q) (n : ℕ+),
        (I q).val (actionIndexEquiv.symm n)=hillHminusRealGapContourMoment q hr n 0) ∧
      ∀ s : ℝ, -1<s → s< -1/2 → ∀ a0 : WeightedCoeff (Weight.sobolev (2*s+1)) 1,
        a0∈WeightedCoeff.positiveActionLocus (Weight.sobolev (2*s+1)) 1 →
        ∃ ε : ℝ, 0<ε ∧ ε< -(2*s+1) ∧
          ∃ P : OffDiagonalFrequencyPairChart D (-(2*s+1)) (s+1) ε,
            ∃ z0 : Coeff 2 × Coeff 2, z0∈P.domain ∧ z0∈Coeff.realPairLocus 2 ∧
              (∀ k : ℤ, (I (P.roughPotential z0)).val k=a0.val (actionIndexEquiv k : ℤ)) ∧
              ∃ U : Set (WeightedCoeff (Weight.sobolev (2*s+1)) 1),
                ∃ G : WeightedCoeff (Weight.sobolev (2*s+1)) 1 → WeightedCoeff (Weight.sobolev (2*s+1)) 1,
                  IsOpen U ∧ a0∈U ∧ AnalyticOnNhd ℂ G U ∧
                  (∀ a∈U, ∀ j : ℤ, j≤0 → (G a).val j=0) ∧
                  (∀ n : ℕ+, (G a0).val (n : ℤ)=P.correction n z0) ∧
                  (∀ a∈U, a∈WeightedCoeff.positiveActionLocus (Weight.sobolev (2*s+1)) 1 →
                    ∃ z : Coeff 2 × Coeff 2, z∈P.domain ∧ z∈Coeff.realPairLocus 2 ∧
                      (∀ k : ℤ, (I (P.roughPotential z)).val k=a.val (actionIndexEquiv k : ℤ)) ∧
                      ∀ n : ℕ+, (G a).val (n : ℤ)=P.correction n z) ∧
                  ∀ a∈U, IsCompactOperator (fderiv ℂ G a) := by
  obtain ⟨Ω,I,hΩ,hΩr,hI,hrec,_hpos,_hzero,_hI0,_hinv⟩ := exists_global_analytic_weighted_Arnold_action_map
  refine ⟨Ω,I,hΩ,hΩr,hI,hrec,?_⟩
  intro s hs0 hs1 a0 ha0
  obtain ⟨ε,hε,hεβ,P,z0,hz0,hzr,hQ,U,G,hU,haU,hG,hzero,hcenter,hrealize,hcompact⟩ :=
    D.exists_local_offDiagonal_compact_action_germ (-(2*s+1)) (s+1)
      (by linarith) (by linarith) (by linarith) (by ring) (2*s+1) (by ring) a0 ha0
  refine ⟨ε,hε,hεβ,P,z0,hz0,hzr,?_,U,G,hU,haU,hG,hzero,hcenter,?_,hcompact⟩
  · intro k
    exact P.original_actions_of_realization Ω hΩr I hI hrec (2*s+1) (by ring) a0 z0 hz0 hzr hQ k
  · intro a ha hapos
    obtain ⟨z,hz,hzr,hQ,hfreq⟩ := hrealize a ha hapos
    exact ⟨z,hz,hzr,(fun k => P.original_actions_of_realization Ω hΩr I hI hrec
      (2*s+1) (by ring) a z hz hzr hQ k),hfreq⟩

end NLS.Articles.KdVKdV2Frequencies
