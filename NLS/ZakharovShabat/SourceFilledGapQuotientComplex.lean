import NLS.ZakharovShabat.SourceFilledGapQuotient
import NLS.ZakharovShabat.SourceFullAbelianSquare

/-! The filled primitive/root quotient is analytic at complex sources on
the entire domain omitting the other cuts. No relation between an
integration circle and the local Cauchy disc is required. -/
noncomputable section
open Set Metric Filter Topology Complex
open scoped ENNReal
namespace NLS.ZakharovShabat.SourceFullAbelianUniformCauchyFamily
variable {p : ℝ≥0∞} [Fact (1 ≤ p)] {hp : p ≠ ⊤} {hp1 : 1 < p}
variable {W : Set (CoeffPair p)}

theorem filledGapQuotient_analytic_complex
    (C : SourceFullAbelianUniformCauchyFamily hp hp1 W) (n : ℤ)
    (ψ : CoeffPair p) (hψ : ψ ∈ ball C.discs.source.val C.discs.sourceRadius) :
    AnalyticOnNhd ℂ (C.filledGapQuotient n ψ)
      (sourceStandardRootOmittedDomain hp hp1 ψ n) := by
  obtain ⟨E⟩ := C.charts ψ hψ
  intro z hz
  by_cases hb : z ∈ ball (C.discs.center n) (C.discs.outer n)
  · apply (analyticAt_const.mul (C.quotient_slice_analytic n ψ hψ z hb)).congr
    filter_upwards [isOpen_ball.mem_nhds hb] with w hw
    exact (C.filledGapQuotient_eq_local n ψ w hw).symm
  · have hzs : z ∉ sourcePeriodicSegment hp hp1 ψ n := by
      intro hs
      exact hb (C.segment_subset_outer n ψ hψ hs)
    have hroot : z ∈ sourceCanonicalRootDomain hp hp1 ψ := by
      intro j
      by_cases hj : j = n
      · simpa only [hj] using hzs
      · exact hz j hj
    have hzo := sourceCanonicalRootDomain_subset_openGapComplement hp hp1 ψ hroot
    have ha := (sourceFullAbelianPrimitive_spectral_analytic E n z hzo).div
      (sourceStandardRoot_analyticAt hp hp1 ψ n z hzs)
      (sourceStandardRoot_ne_zero_off_segment hp hp1 ψ n z hzs)
    apply (analyticAt_const.mul ha).congr
    filter_upwards [(isClosed_sourcePeriodicSegment hp hp1 ψ n).isOpen_compl.mem_nhds hzs] with w hw
    exact (C.filledGapQuotient_eq_div n ψ hψ w hw).symm

theorem odd_primitive_div_root_eq_filled
    (C : SourceFullAbelianUniformCauchyFamily hp hp1 W) (n : ℤ) (l : ℕ)
    (ψ : CoeffPair p) (hψ : ψ ∈ ball C.discs.source.val C.discs.sourceRadius)
    (z : ℂ) (hz : z ∈ sourceCanonicalRootDomain hp hp1 ψ) :
    (sourceFullAbelianPrimitive hp hp1 W n (z,ψ))^(2*l+1) /
        sourceStandardRoot hp hp1 ψ n z =
      I * (sourceFullAbelianSquare hp hp1 W n (z,ψ))^l * C.filledGapQuotient n ψ z := by
  obtain ⟨E⟩ := C.charts ψ hψ
  have hs := sourceFullAbelianSquare_eq_sq E n
    (sourceCanonicalRootDomain_subset_openGapComplement hp hp1 ψ hz)
  dsimp only at hs
  rw [hs,C.filledGapQuotient_eq_div n ψ hψ z (hz n),pow_add,pow_one,pow_mul]
  simp only [div_eq_mul_inv]
  linear_combination (sourceFullAbelianPrimitive hp hp1 W n (z,ψ))^(2*l) *
    sourceFullAbelianPrimitive hp hp1 W n (z,ψ) *
    (sourceStandardRoot hp hp1 ψ n z)⁻¹ * I_sq

end NLS.ZakharovShabat.SourceFullAbelianUniformCauchyFamily
