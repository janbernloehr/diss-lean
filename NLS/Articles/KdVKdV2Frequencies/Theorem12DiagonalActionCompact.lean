import NLS.Articles.KdVKdV2Frequencies.DiagonalActionCompactFactory

/-! The actual diagonal contribution to Theorem 1.2(ii) has compact
ACTION derivatives in the original intermediate weighted ell1 norm.
The full global frequency identification remains a separate obligation. -/
noncomputable section
set_option autoImplicit false
open Set Complex NLS.KdV NLS.ZakharovShabat
open NLS.Articles.KdVConvexity
open scoped ENNReal
namespace NLS.Articles.KdVKdV2Frequencies

theorem GlobalRoughAbelianForwardData.theorem_1_2_diagonal_action_compact
    (D : GlobalRoughAbelianForwardData) :
    ∃ Ω : Set PeriodOneHminusOne, ∃ I : PeriodOneHminusOne → BaseActionSpace,
      IsOpen Ω ∧ {q | IsRealPeriodOneHminusOne q}⊆Ω ∧ AnalyticOnNhd ℂ I Ω ∧
      (∀ q (hr : IsRealPeriodOneHminusOne q) (n : ℕ+),
        (I q).val (actionIndexEquiv.symm n)=hillHminusRealGapContourMoment q hr n 0) ∧
      ∀ s : ℝ, -1<s → s< -1/2 → ∀ a0 : WeightedCoeff (Weight.sobolev (2*s+1)) 1,
        a0∈WeightedCoeff.positiveActionLocus (Weight.sobolev (2*s+1)) 1 →
        ∃ P : DiagonalFrequencyPairChart D I (s+1), ∃ z0 : Coeff 2 × Coeff 2,
          z0∈P.domain ∧ z0∈Coeff.realPairLocus 2 ∧
          (∀ k : ℤ, (I (P.roughPotential z0)).val k=a0.val (actionIndexEquiv k : ℤ)) ∧
          ∃ C : DiagonalActionSymbolChart P (2*s+1) a0 z0,
            ∃ G : WeightedCoeff (Weight.sobolev (2*s+1)) 1 → WeightedCoeff (Weight.sobolev (2*s+1)) 1,
              AnalyticOnNhd ℂ G C.domain ∧
              (∀ a∈C.domain, ∀ j : ℤ, (G a).val j=6*a.val j*C.symbol a j) ∧
              (∀ a∈C.domain, ∀ j : ℤ, j≤0 → (G a).val j=0) ∧
              (∀ a∈C.domain, a∈WeightedCoeff.positiveActionLocus (Weight.sobolev (2*s+1)) 1 →
                ∃ z : Coeff 2 × Coeff 2, z∈P.domain ∧ z∈Coeff.realPairLocus 2 ∧
                  (∀ k : ℤ, (I (P.roughPotential z)).val k=a.val (actionIndexEquiv k : ℤ)) ∧
                  C.symbol a=P.packet z ∧ ∀ n : ℕ+,
                    P.physicalChart.correction n (P.roughPotential z)+6*a.val (n : ℤ)=
                      P.physicalChart.offDiagonalCorrection n (P.roughPotential z)+(G a).val (n : ℤ)) ∧
              ∀ a∈C.domain, IsCompactOperator (fderiv ℂ G a) := by
  obtain ⟨Ω,I,hΩ,hΩr,hI,hrec,_hpos,_hzero,_hI0,_hinv⟩ := exists_global_analytic_weighted_Arnold_action_map
  refine ⟨Ω,I,hΩ,hΩr,hI,hrec,?_⟩
  intro s hs0 _hs1 a0 ha0
  obtain ⟨P,z0,hz0,hzr,hcenter,⟨C⟩⟩ := D.exists_local_diagonal_action_symbol
    Ω hΩr I hI hΩ hrec (s+1) (by linarith) (2*s+1) (by ring) a0 ha0
  exact ⟨P,z0,hz0,hzr,hcenter,C,C.exists_compact_packet⟩

end NLS.Articles.KdVKdV2Frequencies
