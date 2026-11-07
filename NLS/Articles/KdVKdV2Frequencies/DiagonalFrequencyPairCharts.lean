import NLS.KdV.PhysicalDiagonalRoughArnold
import NLS.KdV.HillNativePairInverse
import NLS.Articles.KdVKdV2Frequencies.WeightedPairArnoldActions
import NLS.SequenceSpaces.AnalyticPacketPullback

/-! Actual diagonal symbols pulled through the same global native
inverse, retaining the original rough Arnold action factorization. -/
noncomputable section
set_option autoImplicit false
open Set Complex NLS.KdV NLS.ZakharovShabat
open NLS.Articles.KdVConvexity
open scoped ENNReal
namespace NLS.Articles.KdVKdV2Frequencies

structure DiagonalFrequencyPairChart (D : GlobalRoughAbelianForwardData)
    (I : PeriodOneHminusOne → BaseActionSpace) (t : ℝ) where
  domain : Set (Coeff 2 × Coeff 2)
  domain_open : IsOpen domain
  roughPotential : (Coeff 2 × Coeff 2) → PeriodOneHminusOne
  analytic_potential : AnalyticOnNhd ℂ roughPotential domain
  rough_zero : ∀ z∈domain, (roughPotential z).val 0=0
  rough_real : ∀ z∈domain, z∈Coeff.realPairLocus 2 → IsRealPeriodOneHminusOne (roughPotential z)
  rough_signed : ∀ z∈domain, z∈Coeff.realPairLocus 2 → ∀ j : ℤ,
    (D.signed (roughPotential z)).val j=(signedPairToDeleted actionIndexEquiv z).val j/(Weight.sobolev (t-1/2) j : ℂ)
  physicalChart : PhysicalMiuraFrequencyChart
  rough_mem : ∀ z∈domain, roughPotential z∈physicalChart.domain
  packet : (Coeff 2 × Coeff 2) → Coeff 2
  analytic_packet : AnalyticOnNhd ℂ packet domain
  bound : ℝ
  bound_nonneg : 0≤bound
  norm_packet : ∀ z∈domain, ‖packet z‖≤bound
  nonpositive : ∀ z∈domain, ∀ j : ℤ, j≤0 → packet z j=0
  factor : ∀ z∈domain, z∈Coeff.realPairLocus 2 → ∀ n : ℕ+,
    physicalChart.correction n (roughPotential z)+6*(I (roughPotential z)).val (actionIndexEquiv.symm n)=
      physicalChart.offDiagonalCorrection n (roughPotential z)+
        6*(I (roughPotential z)).val (actionIndexEquiv.symm n)*packet z (n : ℤ)

theorem exists_diagonalFrequencyPairChart
    (D : GlobalRoughAbelianForwardData)
    (Ω : Set PeriodOneHminusOne) (hΩ : {q | IsRealPeriodOneHminusOne q}⊆Ω)
    (I : PeriodOneHminusOne → BaseActionSpace) (hI : AnalyticOnNhd ℂ I Ω) (hΩopen : IsOpen Ω)
    (hrec : ∀ q (hr : IsRealPeriodOneHminusOne q) (n : ℕ+),
      (I q).val (actionIndexEquiv.symm n)=hillHminusRealGapContourMoment q hr n 0)
    (t : ℝ) (ht : 0≤t) (z0 : Coeff 2 × Coeff 2) (hz0 : z0∈Coeff.realPairLocus 2) :
    ∃ P : DiagonalFrequencyPairChart D I t, z0∈P.domain := by
  obtain ⟨U,hU,hzU,Q,hQ,hmean,hmatch⟩ := exists_hillNative_pair_inverse D actionIndexEquiv t ht z0 hz0
  let J := periodOneSobolevImageInclusion t ht
  let R := fun z => J (Q z)
  have hRa : AnalyticOnNhd ℂ R U := fun z hz => (J.analyticAt _).comp (hQ z hz)
  have hreal (z : Coeff 2 × Coeff 2) (hz : z∈U) (hzr : z∈Coeff.realPairLocus 2) :
      IsRealPeriodOneHminusOne (R z) := by
    change IsRealPeriodOneHminusOne (J (Q z))
    rw [hmatch z hz hzr]
    exact nativeRealPairInverse_real D actionIndexEquiv t ht z hzr
  obtain ⟨B,hqB,_hshift,H⟩ := exists_physicalMiuraFrequencyChart_with_original_estimates
    (R z0) (hreal z0 hzU hz0) 0
  obtain ⟨T,hT,hqT,hTB,M,hM,S,hSa,hSb,hSz,hfactor⟩ :=
    B.exists_local_diagonal_symbol_rough_Arnold H Ω hΩ I hI hΩopen hrec (R z0) hqB (hreal z0 hzU hz0)
  let V := U∩R ⁻¹' T
  have hV : IsOpen V := hRa.continuousOn.isOpen_inter_preimage hU hT
  have hzero (z : Coeff 2 × Coeff 2) (hz : z∈V) : (R z).val 0=0 := by
    rw [periodOneSobolevImageInclusion_apply]
    exact hmean z hz.1
  refine ⟨{
    domain := V
    domain_open := hV
    roughPotential := R
    analytic_potential := hRa.mono inter_subset_left
    rough_zero := hzero
    rough_real := fun z hz hzr => hreal z hz.1 hzr
    rough_signed := ?_
    physicalChart := B
    rough_mem := fun z hz => (hTB hz.2).1
    packet := fun z => S (R z)
    analytic_packet := fun z hz => (hSa (R z) hz.2).comp (hRa z hz.1)
    bound := M
    bound_nonneg := hM
    norm_packet := fun z hz => hSb (R z) hz.2
    nonpositive := fun z hz j hj => hSz (R z) hz.2 j hj
    factor := fun z hz hzr n => hfactor (R z) hz.2 (hreal z hz.1 hzr) (hzero z hz) n
  },⟨hzU,hqT⟩⟩
  intro z hz hzr j
  change (D.signed (J (Q z))).val j=_
  rw [hmatch z hz.1 hzr]
  exact nativeRealPairInverse_signed_apply D actionIndexEquiv t ht z hzr j

end NLS.Articles.KdVKdV2Frequencies
