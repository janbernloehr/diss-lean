import NLS.Articles.KdVKdV2Frequencies.DiagonalFrequencyPairCharts
import NLS.Articles.KdVKdV2Frequencies.OffDiagonalPairOriginalEstimates

/-! The actual diagonal factorization on the SAME physical chart and
native inverse as the strictly smoothing off-diagonal packet. -/
noncomputable section
set_option autoImplicit false
open Set Complex NLS.KdV NLS.ZakharovShabat
open NLS.Articles.KdVConvexity
open scoped ENNReal
namespace NLS.Articles.KdVKdV2Frequencies

theorem OffDiagonalFrequencyPairChart.exists_compatible_diagonal_chart
    {D : GlobalRoughAbelianForwardData} {β t ε : ℝ}
    (P : OffDiagonalFrequencyPairChart D β t ε)
    (H : SourceLemma12_12Data (by norm_num) (by norm_num)
      P.physicalChart.psi.family.originalDomain P.physicalChart.psi.family.domain P.physicalChart.psi.family.roots)
    (Ω : Set PeriodOneHminusOne) (hΩ : {q | IsRealPeriodOneHminusOne q}⊆Ω)
    (I : PeriodOneHminusOne → BaseActionSpace) (hI : AnalyticOnNhd ℂ I Ω) (hΩopen : IsOpen Ω)
    (hrec : ∀ q (hr : IsRealPeriodOneHminusOne q) (n : ℕ+),
      (I q).val (actionIndexEquiv.symm n)=hillHminusRealGapContourMoment q hr n 0)
    (z0 : Coeff 2 × Coeff 2) (hz0 : z0∈P.domain) (hzr : z0∈Coeff.realPairLocus 2) :
    ∃ Q : DiagonalFrequencyPairChart D I t, z0∈Q.domain ∧ Q.domain⊆P.domain ∧
      Q.roughPotential=P.roughPotential ∧ Q.physicalChart=P.physicalChart := by
  obtain ⟨T,hT,hqT,hTB,M,hM,S,hSa,hSb,hSz,hfactor⟩ :=
    P.physicalChart.exists_local_diagonal_symbol_rough_Arnold H Ω hΩ I hI hΩopen hrec
      (P.roughPotential z0) (P.rough_mem z0 hz0) (P.rough_real z0 hz0 hzr)
  let V := P.domain∩P.roughPotential ⁻¹' T
  have hV : IsOpen V := P.analytic_potential.continuousOn.isOpen_inter_preimage P.domain_open hT
  refine ⟨{
    domain := V
    domain_open := hV
    roughPotential := P.roughPotential
    analytic_potential := P.analytic_potential.mono inter_subset_left
    rough_zero := fun z hz => P.rough_zero z hz.1
    rough_real := fun z hz hzr => P.rough_real z hz.1 hzr
    rough_signed := fun z hz hzr j => P.rough_signed z hz.1 hzr j
    physicalChart := P.physicalChart
    rough_mem := fun z hz => P.rough_mem z hz.1
    packet := fun z => S (P.roughPotential z)
    analytic_packet := fun z hz => (hSa _ hz.2).comp (P.analytic_potential z hz.1)
    bound := M
    bound_nonneg := hM
    norm_packet := fun z hz => hSb _ hz.2
    nonpositive := fun z hz j hj => hSz _ hz.2 j hj
    factor := fun z hz hzr n => hfactor _ hz.2 (P.rough_real z hz.1 hzr) (P.rough_zero z hz.1) n
  },⟨hz0,hqT⟩,inter_subset_left,rfl,rfl⟩

end NLS.Articles.KdVKdV2Frequencies
