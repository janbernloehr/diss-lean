import NLS.Articles.KdVKdV2Frequencies.DiagonalSymbolActionCharts
import NLS.Articles.KdVKdV2Frequencies.DiagonalOriginalActionRecovery
import NLS.SequenceSpaces.CompactFiniteSymbolPacket
import NLS.SequenceSpaces.AnalyticLinearPacketTransport

/-! The actual diagonal contribution has compact ACTION derivatives
in the original weighted ell1 norm. Its finite-exponent symbol and exact
rough original Arnold realizations are retained on one complex germ. -/
noncomputable section
set_option autoImplicit false
open Set Metric Complex NLS.KdV NLS.ZakharovShabat
open NLS.Articles.KdVConvexity
open scoped ENNReal
namespace NLS.Articles.KdVKdV2Frequencies

structure DiagonalActionSymbolChart
    {D : GlobalRoughAbelianForwardData} {I : PeriodOneHminusOne → BaseActionSpace} {t : ℝ}
    (P : DiagonalFrequencyPairChart D I t) (α : ℝ)
    (a0 : WeightedCoeff (Weight.sobolev α) 1) (z0 : Coeff 2 × Coeff 2) where
  domain : Set (WeightedCoeff (Weight.sobolev α) 1)
  domain_open : IsOpen domain
  center_mem : a0∈domain
  symbol : WeightedCoeff (Weight.sobolev α) 1 → Coeff 2
  analytic_symbol : AnalyticOnNhd ℂ symbol domain
  norm_symbol : ∀ a∈domain, ‖symbol a‖≤P.bound
  nonpositive : ∀ a∈domain, ∀ j : ℤ, j≤0 → symbol a j=0
  center : symbol a0=P.packet z0
  realization : ∀ a∈domain, a∈WeightedCoeff.positiveActionLocus (Weight.sobolev α) 1 →
    ∃ z : Coeff 2 × Coeff 2, z∈P.domain ∧ z∈Coeff.realPairLocus 2 ∧
      (∀ k : ℤ, (I (P.roughPotential z)).val k=a.val (actionIndexEquiv k : ℤ)) ∧
      symbol a=P.packet z

theorem DiagonalFrequencyPairChart.exists_raw_symbol_chart
    {D : GlobalRoughAbelianForwardData} {I : PeriodOneHminusOne → BaseActionSpace} {t : ℝ}
    (P : DiagonalFrequencyPairChart D I t)
    (Ω : Set PeriodOneHminusOne) (hΩ : {q | IsRealPeriodOneHminusOne q}⊆Ω)
    (hI : AnalyticOnNhd ℂ I Ω)
    (hrec : ∀ q (hr : IsRealPeriodOneHminusOne q) (n : ℕ+),
      (I q).val (actionIndexEquiv.symm n)=hillHminusRealGapContourMoment q hr n 0)
    (α : ℝ) (hα : 2*t-1=α) (z0 : Coeff 2 × Coeff 2)
    (hz0 : z0∈P.domain) (hzreal : z0∈Coeff.realPairLocus 2)
    (a0 : WeightedCoeff (Weight.sobolev α) 1)
    (ha0 : sobolevActionEnumeration α a0=quadraticActionsExponent (q := 1) z0) :
    Nonempty (DiagonalActionSymbolChart P α a0 z0) := by
  obtain ⟨δ,g,hδ,hg,hgb,hgz,hgc,hlift⟩ := P.exists_action_ball Ω hΩ hI hrec z0 hz0 hzreal
  have hc : sobolevActionEnumeration α a0∈ball (quadraticActionsExponent (q := 1) z0) δ := by
    rw [ha0]
    exact mem_ball_self hδ
  obtain ⟨U,S,hU,hcenter,hS,hUV,hraw⟩ := exists_analytic_linear_packet_transport
    (sobolevActionEnumeration α) (ContinuousLinearMap.id ℂ (Coeff 2))
    (ball (quadraticActionsExponent (q := 1) z0) δ) g isOpen_ball hg {a0}
    (by intro a ha;rcases Set.mem_singleton_iff.mp ha with rfl;exact hc)
  have haU : a0∈U := hcenter (mem_singleton a0)
  have he (a : WeightedCoeff (Weight.sobolev α) 1) (ha : a∈U) :
      S a=g (sobolevActionEnumeration α a) := hraw a ha
  refine ⟨{
    domain := U
    domain_open := hU
    center_mem := haU
    symbol := S
    analytic_symbol := hS
    norm_symbol := ?_
    nonpositive := ?_
    center := ?_
    realization := ?_
  }⟩
  · intro a ha
    rw [he a ha]
    exact hgb _ (hUV a ha)
  · intro a ha j hj
    rw [he a ha]
    exact hgz _ (hUV a ha) j hj
  · rw [he a0 haU,ha0,hgc]
  · intro a ha hapos
    obtain ⟨z,hz,hzr,hQ,hgp⟩ := hlift (sobolevActionEnumeration α a) (hUV a ha)
      (sobolevActionEnumeration_nonnegative α a hapos.1)
    refine ⟨z,hz,hzr,(fun k => P.original_actions_of_realization Ω hΩ hI hrec α hα a z hz hzr hQ k),?_⟩
    rw [he a ha,hgp]

theorem DiagonalActionSymbolChart.exists_compact_packet
    {D : GlobalRoughAbelianForwardData} {I : PeriodOneHminusOne → BaseActionSpace} {t α : ℝ}
    {P : DiagonalFrequencyPairChart D I t}
    {a0 : WeightedCoeff (Weight.sobolev α) 1} {z0 : Coeff 2 × Coeff 2}
    (C : DiagonalActionSymbolChart P α a0 z0) :
    ∃ G : WeightedCoeff (Weight.sobolev α) 1 → WeightedCoeff (Weight.sobolev α) 1,
      AnalyticOnNhd ℂ G C.domain ∧
      (∀ a∈C.domain, ∀ j : ℤ, (G a).val j=6*a.val j*C.symbol a j) ∧
      (∀ a∈C.domain, ∀ j : ℤ, j≤0 → (G a).val j=0) ∧
      (∀ a∈C.domain, a∈WeightedCoeff.positiveActionLocus (Weight.sobolev α) 1 →
        ∃ z : Coeff 2 × Coeff 2, z∈P.domain ∧ z∈Coeff.realPairLocus 2 ∧
          (∀ k : ℤ, (I (P.roughPotential z)).val k=a.val (actionIndexEquiv k : ℤ)) ∧
          C.symbol a=P.packet z ∧ ∀ n : ℕ+,
            P.physicalChart.correction n (P.roughPotential z)+6*a.val (n : ℤ)=
              P.physicalChart.offDiagonalCorrection n (P.roughPotential z)+(G a).val (n : ℤ)) ∧
      ∀ a∈C.domain, IsCompactOperator (fderiv ℂ G a) := by
  obtain ⟨G,hG,hraw,hcompact⟩ := WeightedCoeff.exists_analytic_finiteSymbol_packet_compact
    (Weight.sobolev α) (by norm_num : (1 : ℝ≥0∞)≠⊤) (by norm_num : (2 : ℝ≥0∞)≠⊤)
    C.domain C.symbol (fun a : WeightedCoeff (Weight.sobolev α) 1 => (6 : ℂ) • a)
    C.analytic_symbol (analyticOnNhd_const.smul analyticOnNhd_id)
  have hraw' (a : WeightedCoeff (Weight.sobolev α) 1) (j : ℤ) :
      (G a).val j=6*a.val j*C.symbol a j := by
    rw [hraw]
    change C.symbol a j*(6*a.val j)=_
    ring
  refine ⟨G,hG,(fun a _ j => hraw' a j),?_,?_,hcompact⟩
  · intro a ha j hj
    rw [hraw',C.nonpositive a ha j hj,mul_zero]
  · intro a ha hapos
    obtain ⟨z,hz,hzr,hi,hgp⟩ := C.realization a ha hapos
    refine ⟨z,hz,hzr,hi,hgp,?_⟩
    intro n
    have hin := hi (actionIndexEquiv.symm n)
    simp only [Equiv.apply_symm_apply] at hin
    have hf := P.factor z hz hzr n
    rw [hin] at hf
    rw [hraw',hgp]
    exact hf

end NLS.Articles.KdVKdV2Frequencies
