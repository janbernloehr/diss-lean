import NLS.ComplexAnalysis.FilledSimpleQuotient
import NLS.ZakharovShabat.SourceOpenGapComplement
import NLS.ZakharovShabat.SourceCriticalRootGapNeighborhood
import NLS.ZakharovShabat.SourcePsiLemma12_11

/-! # The normalized psi quotient through closed gaps

For an open selected gap, every zero of the canonical root in the open-gap
complement is a simple, collapsed-gap zero of the normalized psi numerator.
Filling the quotient by the derivative ratio therefore makes it analytic
on that whole complement, including infinitely many closed gaps.
-/
noncomputable section
open Set Complex NLS.ComplexAnalysis
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- A collapsed segment consists of its midpoint. -/
theorem sourcePeriodicSegment_eq_midpoint_singleton_of_zeroGap
    (hp : p ≠ ⊤) (hp1 : 1 < p) (ψ : CoeffPair p) (m : ℤ)
    (hm : canonicalPeriodicGap hp hp1 (periodOnePotential ψ)
      (periodOnePotential_mem ψ) m = 0) :
    sourcePeriodicSegment hp hp1 ψ m = {sourceStandardRootMidpoint hp hp1 ψ m} := by
  rw [sourcePeriodicSegment_eq_singleton_of_zeroGap hp hp1 ψ m hm]
  have he := sub_eq_zero.mp hm
  congr 1
  dsimp only [sourceStandardRootMidpoint, canonicalPeriodicMidpoint]
  rw [he]
  ring

/-- The canonical root has a simple zero at every collapsed real gap. -/
theorem deriv_sourceCanonicalRoot_at_collapsedGap
    (hp : p ≠ ⊤) (hp1 : 1 < p) (ψ : CoeffPair p)
    (hψ : IsRealType (CoeffPair.toMax p ψ)) (m : ℤ)
    (hm : canonicalPeriodicGap hp hp1 (periodOnePotential ψ)
      (periodOnePotential_mem ψ) m = 0) :
    deriv (sourceCanonicalRoot hp hp1 ψ) (sourceStandardRootMidpoint hp hp1 ψ m) =
      -(2*I) * sourceStandardRootOmittedProduct hp hp1 m ψ
        (sourceStandardRootMidpoint hp hp1 ψ m) := by
  let τ := sourceStandardRootMidpoint hp hp1 ψ m
  have hτseg : τ ∈ sourcePeriodicSegment hp hp1 ψ m := by
    rw [sourcePeriodicSegment_eq_midpoint_singleton_of_zeroGap hp hp1 ψ m hm]
    exact rfl
  obtain ⟨V, _, _, hrealV, hdisjoint⟩ := exists_global_source_disjoint_periodicSegments hp hp1
  have hτ : τ ∈ sourceStandardRootOmittedDomain hp hp1 ψ m := by
    intro k hkm
    exact Set.disjoint_left.mp (hdisjoint ψ (hrealV hψ) m k hkm.symm) hτseg
  obtain ⟨W, _, _, hreal, hdata⟩ := exists_global_source_analytic_omittedJointProduct hp hp1
  have hP := sourceStandardRootOmittedProduct_analyticOnNhd_spectral hp hp1 m W
    (hdata m).2.1 ψ (hreal hψ) τ hτ
  have heq : sourceCanonicalRoot hp hp1 ψ =
      fun z => 2*I*(τ-z)*sourceStandardRootOmittedProduct hp hp1 m ψ z := by
    funext z
    rw [sourceCanonicalRoot_eq_omitted hp hp1 m, sourceStandardRoot_of_zeroGap hp hp1 ψ m z hm]
  rw [heq]
  have hd := (((hasDerivAt_const τ τ).sub (hasDerivAt_id τ)).const_mul (2*I)).mul
    hP.differentiableAt.hasDerivAt
  dsimp only [Pi.sub_apply, id_eq] at hd
  simpa only [sub_self, mul_zero, zero_mul, add_zero, zero_sub, mul_neg, mul_one] using! hd.deriv

/-- The canonical root derivative cannot vanish at a collapsed real gap. -/
theorem deriv_sourceCanonicalRoot_ne_zero_at_collapsedGap
    (hp : p ≠ ⊤) (hp1 : 1 < p) (ψ : CoeffPair p)
    (hψ : IsRealType (CoeffPair.toMax p ψ)) (m : ℤ)
    (hm : canonicalPeriodicGap hp hp1 (periodOnePotential ψ)
      (periodOnePotential_mem ψ) m = 0) :
    deriv (sourceCanonicalRoot hp hp1 ψ) (sourceStandardRootMidpoint hp hp1 ψ m) ≠ 0 := by
  rw [deriv_sourceCanonicalRoot_at_collapsedGap hp hp1 ψ hψ m hm]
  apply mul_ne_zero (neg_ne_zero.mpr (mul_ne_zero (by norm_num) Complex.I_ne_zero))
  apply sourceStandardRootOmittedProduct_ne_zero
  obtain ⟨W, _, _, hreal, hdisjoint⟩ := exists_global_source_disjoint_periodicSegments hp hp1
  intro k hkm
  apply Set.disjoint_left.mp (hdisjoint ψ (hreal hψ) m k hkm.symm)
  simpa only [sourceStandardRootMidpoint] using sourcePeriodicMidpoint_mem_segment hp hp1 ψ m

/-- Fill the spectral quotient only at canonical-root zeros. -/
def sourcePsiFilledQuotient (hp : p ≠ ⊤) (hp1 : 1 < p)
    (n : ℤ) (a : Coeff p) (ψ : CoeffPair p) : ℂ → ℂ :=
  filledSimpleQuotient (fun z => sourcePsiCandidate n (z,a)) (sourceCanonicalRoot hp hp1 ψ)

theorem sourcePsiFilledQuotient_eq_contourIntegrand
    (hp : p ≠ ⊤) (hp1 : 1 < p) (n : ℤ) (a : Coeff p) (ψ : CoeffPair p)
    (z : ℂ) (hz : z ∈ sourceCanonicalRootDomain hp hp1 ψ) :
    sourcePsiFilledQuotient hp hp1 n a ψ z =
      sourcePsiContourIntegrandJoint hp hp1 n (z,(a,ψ)) :=
  filledSimpleQuotient_eq_div (sourceCanonicalRoot_ne_zero_off_gaps hp hp1 ψ z hz)

namespace SourcePsiNormalizedComplexExtension
variable {hp : p ≠ ⊤} {hp1 : 1 < p} {W : Set (CoeffPair p)}
  {s : (n : ℤ) → CoeffPair p → DeletedCoeff p n}

/-- Normalized psi vanishes at each collapsed gap other than its deleted index. -/
theorem candidate_zero_at_collapsedGap (hs : SourcePsiNormalizedComplexExtension hp hp1 W s)
    (φ : realTypeSourceLocus p) (n m : ℤ) (hmn : m ≠ n)
    (hm : canonicalPeriodicGap hp hp1 (periodOnePotential φ.val)
      (periodOnePotential_mem φ.val) m = 0) :
    sourcePsiCandidate n (sourceStandardRootMidpoint hp hp1 φ.val m,(s n φ.val : Coeff p)) = 0 := by
  rw [hs.real_agreement n φ]
  have hroot := sourcePsiGapRoot_mem_periodicSegment hp hp1 n m hmn φ
  rw [sourcePeriodicSegment_eq_midpoint_singleton_of_zeroGap hp hp1 φ.val m hm] at hroot
  rw [← Set.mem_singleton_iff.mp hroot]
  exact sourcePsiCandidate_other_root hp hp1 n m hmn _

/-- When the selected angle gap is open, the filled quotient is analytic
away from the open gaps. No finite-gap assumption is needed here. -/
theorem analytic_filledQuotient (hs : SourcePsiNormalizedComplexExtension hp hp1 W s)
    (φ : realTypeSourceLocus p) (n : ℤ)
    (hn : canonicalPeriodicGap hp hp1 (periodOnePotential φ.val)
      (periodOnePotential_mem φ.val) n ≠ 0) :
    AnalyticOnNhd ℂ (sourcePsiFilledQuotient hp hp1 n (s n φ.val) φ.val)
      (sourceOpenGapComplement hp hp1 φ.val) := by
  intro z hz
  apply analyticAt_filledSimpleQuotient
    (((differentiable_sourcePsiCandidate hp hp1 n (s n φ.val)).differentiableOn.analyticOnNhd
      isOpen_univ) z (mem_univ _))
    (sourceCanonicalRoot_analyticOnNhd_openGapComplement hp hp1 φ.val φ.property z hz)
  intro hzero
  rcases mem_sourceOpenGapComplement_cases hp hp1 φ.val z hz with hoff | ⟨m, hm, hzm⟩
  · exact (sourceCanonicalRoot_ne_zero_off_gaps hp hp1 φ.val z hoff hzero).elim
  · rw [sourcePeriodicSegment_eq_midpoint_singleton_of_zeroGap hp hp1 φ.val m hm] at hzm
    rw [Set.mem_singleton_iff.mp hzm]
    exact ⟨hs.candidate_zero_at_collapsedGap φ n m (fun he => hn (he ▸ hm)) hm,
      deriv_sourceCanonicalRoot_ne_zero_at_collapsedGap hp hp1 φ.val φ.property m hm⟩

end SourcePsiNormalizedComplexExtension
end NLS.ZakharovShabat
