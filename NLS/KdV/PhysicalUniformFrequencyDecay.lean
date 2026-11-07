import NLS.KdV.PhysicalUniformDiagonalCancellation
import NLS.ZakharovShabat.SourceUniformOffDiagonalDecay

/-! Sharp uniform little-o for the FULL actual renormalized physical
frequency on one fixed complex source neighborhood. The exact original
counterterm calibration is inherited from the same physical chart. -/
noncomputable section
open Set Complex NLS.ZakharovShabat
open scoped ENNReal
namespace NLS.KdV
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
variable {t : ℝ} {ht : 0≤t} {J : E →L[ℂ] PeriodOneHminusOne}

theorem PhysicalFrequencyParameterization.exists_uniform_offDiagonal_decay
    (A : PhysicalFrequencyParameterization E t ht J) (ht0 : 0<t) (ht1 : t<2/3)
    (q : E) (hq : q∈A.domain) (hqr : IsRealPeriodOneHminusOne (J q)) :
    ∃ T : Set E, IsOpen T ∧ q∈T ∧ T⊆A.domain ∧
      ∀ ε > (0:ℝ), ∃ K : ℕ, ∀ a∈T, ∀ n : ℕ+, K≤(n:ℤ).natAbs →
        Weight.sobolev (3*t-1) (n:ℤ)*‖A.physical.offDiagonalCorrection n (J a)‖≤ε := by
  let L := normalizedWeightedSourceCLM (p := 2) (sourceSobolevSpectralWeight t ht)
  let φ : realTypeSourceSubmodule 2 := ⟨A.normalizedSource q,A.real_source q hq hqr⟩
  obtain ⟨S,hS,hφS,_,hdecay⟩ := A.physical.atlas.exists_uniform_offDiagonal_secondMoment_decay
    t ht0 ht1 A.estimates.angular_extension A.physical.psi.family.domain_open
    A.physical.psi.family.real_subset φ
  obtain ⟨T,hT,hqT,hTA,hTS,_⟩ := exists_open_common_pullback_domain A.domain A.domain_open q hq
    A.normalizedSource A.analytic_source.continuousOn S hS hφS
    J J.continuous A.physical.domain A.physical.domain_open (A.domain_subset hq)
  refine ⟨T,hT,hqT,hTA,?_⟩
  intro ε hε
  obtain ⟨K,hK⟩ := hdecay (ε/12) (by positivity)
  refine ⟨K,?_⟩
  intro a ha n hn
  let d := A.physical.atlas.weightedSecondMomentSum (n:ℤ) (L (A.normalizedSource a))-(n:ℂ)*
    (A.physical.atlas.moment (n:ℤ) (n:ℤ) 2 (L (A.normalizedSource a))-
      A.physical.atlas.moment (n:ℤ) (-(n:ℤ)) 2 (L (A.normalizedSource a)))
  have hraw : A.physical.offDiagonalCorrection n (J a)=(-12:ℂ)*d := by
    dsimp only [PhysicalMiuraFrequencyChart.offDiagonalCorrection,d]
    rw [A.source_identity a (hTA ha)]
  have hb : Weight.sobolev (3*t-1) (n:ℤ)*‖d‖≤ε/12 := by
    simpa only [d,Int.cast_natCast] using hK (A.normalizedSource a) (hTS a ha) (n:ℤ) hn
  rw [hraw,norm_mul,norm_neg,Complex.norm_ofNat]
  calc
    _ = 12*(Weight.sobolev (3*t-1) (n:ℤ)*‖d‖) := by ring
    _ ≤ 12*(ε/12) := mul_le_mul_of_nonneg_left hb (by norm_num)
    _ = ε := by ring

theorem PhysicalFrequencyParameterization.exists_uniform_renormalized_frequency_decay
    (A : PhysicalFrequencyParameterization E t ht J) (ht0 : 0<t) (ht1 : t<2/3)
    (q : E) (hq : q∈A.domain) (hqr : IsRealPeriodOneHminusOne (J q)) :
    ∃ T : Set E, IsOpen T ∧ q∈T ∧ T⊆A.domain ∧
      ∀ ε > (0:ℝ), ∃ K : ℕ, ∀ a∈T, ∀ n : ℕ+, K≤(n:ℤ).natAbs →
        Weight.sobolev (3*t-1) (n:ℤ)*‖A.renormalizedCorrection n a‖≤ε := by
  obtain ⟨Td,hTd,hqTd,hTdA,hd⟩ :=
    A.exists_uniform_sharp_diagonal_cancellation_decay ht0 (by linarith) q hq hqr
  obtain ⟨To,hTo,hqTo,hToA,ho⟩ := A.exists_uniform_offDiagonal_decay ht0 ht1 q hq hqr
  refine ⟨Td∩To,hTd.inter hTo,⟨hqTd,hqTo⟩,(fun _ ha => hTdA ha.1),?_⟩
  intro ε hε
  obtain ⟨Kd,hKd⟩ := hd (ε/2) (half_pos hε)
  obtain ⟨Ko,hKo⟩ := ho (ε/2) (half_pos hε)
  refine ⟨max Kd Ko,?_⟩
  intro a ha n hn
  have he : A.renormalizedCorrection n a=A.diagonalRemainder n a+A.physical.offDiagonalCorrection n (J a) := by
    dsimp only [PhysicalFrequencyParameterization.diagonalRemainder]
    ring
  have hw : 0≤Weight.sobolev (3*t-1) (n:ℤ) := ((Weight.sobolev (3*t-1)).positive (n:ℤ)).le
  rw [he]
  calc
    _ ≤ Weight.sobolev (3*t-1) (n:ℤ)*(‖A.diagonalRemainder n a‖+
        ‖A.physical.offDiagonalCorrection n (J a)‖) := mul_le_mul_of_nonneg_left (norm_add_le _ _) hw
    _ = Weight.sobolev (3*t-1) (n:ℤ)*‖A.diagonalRemainder n a‖+
        Weight.sobolev (3*t-1) (n:ℤ)*‖A.physical.offDiagonalCorrection n (J a)‖ := by ring
    _ ≤ ε/2+ε/2 := add_le_add (hKd a ha.1 n ((le_max_left _ _).trans hn))
      (hKo a ha.2 n ((le_max_right _ _).trans hn))
    _ = ε := by ring

end NLS.KdV
