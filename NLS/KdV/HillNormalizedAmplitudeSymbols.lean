import NLS.KdV.HillCanonicalActionAmplitude
import NLS.ComplexAnalysis.QuadraticFrequencyShift
import NLS.ComplexAnalysis.UniformUnitInverseBounds
import NLS.SequenceSpaces.EvenUnitExtension

/-! The actual normalized action amplitude and its reciprocal are
analytic bounded signed sequences on the existing amplitude domain.
The normalized amplitude tends locally uniformly to one before all
indices, including through collapsed gaps. -/
noncomputable section
open Set Complex NLS.ComplexAnalysis
open scoped ENNReal
namespace NLS.KdV

theorem hillHminusActionRatioSqrt_ne_zero (n : ℕ+) (q : PeriodOneHminusOne)
    (hq : q ∈ hillHminusActionAmplitudeDomain) : hillHminusActionRatioSqrt n q ≠ 0 := by
  intro he
  have hs := hillHminusActionRatioSqrt_sq n q
  rw [he,zero_pow (by decide : (2:ℕ) ≠ 0)] at hs
  exact hillHminusCanonicalActionRatio_ne_zero n q (hillHminusActionAmplitudeDomain_subset_ratio hq) hs.symm

theorem exists_hillHminusActionRatioSqrt_uniform_high (q : PeriodOneHminusOne)
    (hq : q ∈ hillHminusActionAmplitudeDomain) (ε : ℝ) (hε : 0 < ε) :
    ∃ N : ℕ, ∃ U : Set PeriodOneHminusOne, IsOpen U ∧ q ∈ U ∧
      U ⊆ hillHminusActionAmplitudeDomain ∧
      ∀ n : ℕ+, N ≤ (n:ℕ) → ∀ a ∈ U, ‖hillHminusActionRatioSqrt n a-1‖ ≤ ε := by
  obtain ⟨N,V,_,hV,hqV,_,hb⟩ := exists_hillHminusCanonicalActionRatio_uniform_high q
    (hillHminusActionAmplitudeDomain_subset_ratio hq) ε hε
  refine ⟨N,V ∩ hillHminusActionAmplitudeDomain,hV.inter isOpen_hillHminusActionAmplitudeDomain,
    ⟨hqV,hq⟩,inter_subset_right,?_⟩
  intro n hn a ha
  have hs := norm_sqrt_one_add_sub_one_le (hillHminusCanonicalActionRatio n a-1)
  rw [show 1+(hillHminusCanonicalActionRatio n a-1)=hillHminusCanonicalActionRatio n a by ring] at hs
  exact hs.trans (hb n hn a ha.1)

theorem exists_local_uniform_hillHminusActionRatioSqrt_inverse_bounds (q : PeriodOneHminusOne)
    (hq : q ∈ hillHminusActionAmplitudeDomain) :
    ∃ U : Set PeriodOneHminusOne, IsOpen U ∧ q ∈ U ∧ U ⊆ hillHminusActionAmplitudeDomain ∧
      ∃ C : ℝ, 1 ≤ C ∧ ∀ a ∈ U, ∀ n : ℕ+,
        ‖hillHminusActionRatioSqrt n a‖ ≤ C ∧ ‖(hillHminusActionRatioSqrt n a)⁻¹‖ ≤ C :=
  exists_local_uniform_unit_inverse_bounds hillHminusActionRatioSqrt isOpen_hillHminusActionAmplitudeDomain
    analyticOnNhd_hillHminusActionRatioSqrt hillHminusActionRatioSqrt_ne_zero q hq
    (exists_hillHminusActionRatioSqrt_uniform_high q hq (1/2) (by norm_num))

def hillHminusNormalizedAmplitudeSymbol (q : PeriodOneHminusOne) : Coeff ⊤ :=
  Coeff.ofFunctionOrZero ⊤ (Coeff.evenUnitExtension (fun n => hillHminusActionRatioSqrt n q))

def hillHminusInverseAmplitudeSymbol (q : PeriodOneHminusOne) : Coeff ⊤ :=
  Coeff.ofFunctionOrZero ⊤ (Coeff.evenUnitExtension (fun n => (hillHminusActionRatioSqrt n q)⁻¹))

theorem hillHminusNormalizedAmplitudeSymbol_data :
    (∀ q ∈ hillHminusActionAmplitudeDomain, ∀ k,
      hillHminusNormalizedAmplitudeSymbol q k = Coeff.evenUnitExtension (fun n => hillHminusActionRatioSqrt n q) k) ∧
    AnalyticOnNhd ℂ hillHminusNormalizedAmplitudeSymbol hillHminusActionAmplitudeDomain := by
  apply Coeff.analytic_evenUnit_realization_of_local_bounds hillHminusActionRatioSqrt
    isOpen_hillHminusActionAmplitudeDomain analyticOnNhd_hillHminusActionRatioSqrt
  intro q hq
  obtain ⟨U,hU,hqU,hUD,C,hC,hb⟩ := exists_local_uniform_hillHminusActionRatioSqrt_inverse_bounds q hq
  exact ⟨U,hU,hqU,hUD,C,hC,fun a ha n => (hb a ha n).1⟩

theorem hillHminusInverseAmplitudeSymbol_data :
    (∀ q ∈ hillHminusActionAmplitudeDomain, ∀ k,
      hillHminusInverseAmplitudeSymbol q k = Coeff.evenUnitExtension (fun n => (hillHminusActionRatioSqrt n q)⁻¹) k) ∧
    AnalyticOnNhd ℂ hillHminusInverseAmplitudeSymbol hillHminusActionAmplitudeDomain := by
  apply Coeff.analytic_evenUnit_realization_of_local_bounds (fun n q => (hillHminusActionRatioSqrt n q)⁻¹)
    isOpen_hillHminusActionAmplitudeDomain
    (fun n q hq => (analyticOnNhd_hillHminusActionRatioSqrt n q hq).inv (hillHminusActionRatioSqrt_ne_zero n q hq))
  intro q hq
  obtain ⟨U,hU,hqU,hUD,C,hC,hb⟩ := exists_local_uniform_hillHminusActionRatioSqrt_inverse_bounds q hq
  exact ⟨U,hU,hqU,hUD,C,hC,fun a ha n => (hb a ha n).2⟩

theorem hillHminusNormalizedAmplitudeSymbol_positive (q : PeriodOneHminusOne)
    (hq : q ∈ hillHminusActionAmplitudeDomain) (n : ℕ+) :
    hillHminusNormalizedAmplitudeSymbol q ((n:ℕ):ℤ)=hillHminusActionRatioSqrt n q := by
  rw [hillHminusNormalizedAmplitudeSymbol_data.1 q hq,Coeff.evenUnitExtension_positive]

theorem hillHminusNormalizedAmplitudeSymbol_negative (q : PeriodOneHminusOne)
    (hq : q ∈ hillHminusActionAmplitudeDomain) (n : ℕ+) :
    hillHminusNormalizedAmplitudeSymbol q (-((n:ℕ):ℤ))=hillHminusActionRatioSqrt n q := by
  rw [hillHminusNormalizedAmplitudeSymbol_data.1 q hq,Coeff.evenUnitExtension_negative]

theorem hillHminusAmplitudeSymbols_product (q : PeriodOneHminusOne)
    (hq : q ∈ hillHminusActionAmplitudeDomain) (k : ℤ) :
    hillHminusNormalizedAmplitudeSymbol q k*hillHminusInverseAmplitudeSymbol q k=1 := by
  rw [hillHminusNormalizedAmplitudeSymbol_data.1 q hq,hillHminusInverseAmplitudeSymbol_data.1 q hq,
    Coeff.evenUnitExtension_inv]
  apply mul_inv_cancel₀
  unfold Coeff.evenUnitExtension
  split_ifs
  · exact one_ne_zero
  · exact hillHminusActionRatioSqrt_ne_zero _ q hq

theorem hillHminusNormalizedAmplitudeSymbol_unit_tail (q : PeriodOneHminusOne)
    (hq : q ∈ hillHminusActionAmplitudeDomain) :
    ∀ ε > (0:ℝ), ∃ K : ℕ, ∀ k : ℤ, K ≤ k.natAbs →
      ‖hillHminusNormalizedAmplitudeSymbol q k-1‖ ≤ ε := by
  intro ε hε
  obtain ⟨N,U,_,hqU,_,hb⟩ := exists_hillHminusActionRatioSqrt_uniform_high q hq ε hε
  refine ⟨N,?_⟩
  intro k hk
  rw [hillHminusNormalizedAmplitudeSymbol_data.1 q hq]
  unfold Coeff.evenUnitExtension
  split_ifs with hzero
  · simpa only [sub_self,norm_zero] using hε.le
  · exact hb ⟨k.natAbs,Int.natAbs_pos.mpr hzero⟩ hk q hqU

end NLS.KdV
