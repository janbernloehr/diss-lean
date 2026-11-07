import NLS.Articles.KdVPseudomeasures.SourceLocalEndpointFrequencyDecay
import NLS.Articles.KdVPseudomeasures.NativeEndpointBallCompactImage

/-! A compact native envelope of the entire original endpoint norm ball
turns the local moment bounds into uniform o(1) for the genuine frequencies. -/
noncomputable section
open Set Metric Complex Filter Topology NLS.KdV NLS.WeightedCoeff
open scoped ENNReal
namespace NLS.Articles.KdVPseudomeasures

/-- The actual frequency minus its free cubic part tends to zero
uniformly on EVERY original physical endpoint norm ball. -/
theorem source_uniform_endpoint_frequency_remainder (r : ℝ) (hr : AdmissiblePredualOrder r)
    (R : ℝ) (ε : ℝ) (hε : 0 < ε) :
    ∃ N : ℕ, ∀ q : Potential r, ‖q.val‖ ≤ R → ∀ n : ℕ+, N ≤ (n:ℕ) →
      ‖(hillRoughKdVFrequency n (originalHillRealMeanZeroSource (sourceOriginalPotential r hr q)):ℂ)-
          (2*(Real.pi:ℂ)*(n:ℤ))^3‖ < ε := by
  classical
  let K := endpointRealBallNativeEnvelope r hr ((2:ℝ)^r*R)
  have hK : IsCompact K := isCompact_endpointRealBallNativeEnvelope r hr _
  have hlocal (x : PeriodOneHminusOne) (hx : x ∈ K) :
      ∃ U : Set PeriodOneHminusOne, IsOpen U ∧ x ∈ U ∧ ∃ N : ℕ,
        ∀ q : Potential r, ‖q.val‖ ≤ R → sourceNativePeriodOneCLM r hr q.val ∈ U →
          ∀ n : ℕ+, N ≤ (n:ℕ) →
            ‖(hillRoughKdVFrequency n (originalHillRealMeanZeroSource (sourceOriginalPotential r hr q)):ℂ)-
                (2*(Real.pi:ℂ)*(n:ℤ))^3‖ < ε := by
    obtain ⟨b,_,rfl⟩ := hx
    obtain ⟨U,hU,hxU,hdecay⟩ := exists_local_source_endpoint_frequency_decay r hr R
      (hillRealMeanZeroProjection b)
    obtain ⟨N,hN⟩ := hdecay ε hε
    exact ⟨U,hU,hxU,N,hN⟩
  choose U hU hx N hbound using fun x : K => hlocal x x.property
  obtain ⟨J,hJ⟩ := hK.elim_finite_subcover U hU (by
    intro x hxK
    exact mem_iUnion.mpr ⟨⟨x,hxK⟩,hx ⟨x,hxK⟩⟩)
  refine ⟨J.sup N,?_⟩
  intro q hq n hn
  have hqK : sourceNativePeriodOneCLM r hr q.val ∈ K := by
    rw [← originalEndpointRealSource_native r hr q]
    apply endpointNativeInclusion_mem_realBallEnvelope
    exact (norm_originalEndpointRealSource_le r hr q).trans
      (mul_le_mul_of_nonneg_left hq (Real.rpow_nonneg (by norm_num) r))
  obtain ⟨x,hxJ,hqx⟩ := mem_iUnion₂.mp (hJ hqK)
  exact hbound x q hq hqx n ((Finset.le_sup hxJ).trans hn)

end NLS.Articles.KdVPseudomeasures
