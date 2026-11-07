import NLS.ZakharovShabat.SourcePsiOpenGapQuotient

/-! The actual real normalized psi numerator has an analytic filled
quotient off the open gaps whenever its selected gap is open. This does
not require an auxiliary complex-family certificate. -/
noncomputable section
open Set Complex NLS.ComplexAnalysis
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

theorem sourcePsiFilledQuotient_analytic_real
    (hp : p ≠ ⊤) (hp1 : 1 < p) (φ : realTypeSourceLocus p) (n : ℤ)
    (hn : canonicalPeriodicGap hp hp1 (periodOnePotential φ.val)
      (periodOnePotential_mem φ.val) n ≠ 0) :
    AnalyticOnNhd ℂ (sourcePsiFilledQuotient hp hp1 n (sourcePsiGapRoot hp hp1 n φ) φ.val)
      (sourceOpenGapComplement hp hp1 φ.val) := by
  intro z hz
  apply analyticAt_filledSimpleQuotient
    (((differentiable_sourcePsiCandidate hp hp1 n (sourcePsiGapRoot hp hp1 n φ)).differentiableOn.analyticOnNhd
      isOpen_univ) z (mem_univ _))
    (sourceCanonicalRoot_analyticOnNhd_openGapComplement hp hp1 φ.val φ.property z hz)
  intro hzero
  rcases mem_sourceOpenGapComplement_cases hp hp1 φ.val z hz with hoff | ⟨m,hm,hzm⟩
  · exact (sourceCanonicalRoot_ne_zero_off_gaps hp hp1 φ.val z hoff hzero).elim
  · rw [sourcePeriodicSegment_eq_midpoint_singleton_of_zeroGap hp hp1 φ.val m hm] at hzm
    rw [Set.mem_singleton_iff.mp hzm]
    refine ⟨?_,deriv_sourceCanonicalRoot_ne_zero_at_collapsedGap hp hp1 φ.val φ.property m hm⟩
    have hmn : m ≠ n := by intro he; exact hn (he ▸ hm)
    have hroot := sourcePsiGapRoot_mem_periodicSegment hp hp1 n m hmn φ
    rw [sourcePeriodicSegment_eq_midpoint_singleton_of_zeroGap hp hp1 φ.val m hm] at hroot
    rw [← Set.mem_singleton_iff.mp hroot]
    exact sourcePsiCandidate_other_root hp hp1 n m hmn _

end NLS.ZakharovShabat
