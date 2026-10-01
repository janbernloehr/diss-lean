import NLS.ZakharovShabat.SourceAngularThetaRealCotangent
import NLS.ZakharovShabat.SourceEntireGapContourZeros
import NLS.ZakharovShabat.SourcePsiSelectedKernelGapZeroSequence
import NLS.ZakharovShabat.SourceRealActionRealCenteredChart

/-! # A full gap-zero sequence for the actual angle/angle spectral variation

The actual entire variation is real on the real spectral axis and has
zero weighted period on every constructed real-centered action chart.
Mean value gives a zero in each open periodic gap; the collapsed-gap
Cauchy formula gives a zero at each collapsed midpoint. Simultaneous
choice produces a full displaced spectral zero sequence in the actual
source exponent, with no omitted index.
-/

noncomputable section
open Set Metric Complex Filter Topology NLS.Poisson
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]
namespace SourceAngularThetaCommonDomainData
variable {hp : p ≠ ⊤} {hp1 : 1 < p} {W₀ B W : Set (CoeffPair p)}
  {s : (j : ℤ) → CoeffPair p → DeletedCoeff p j}

/-- The actual discriminant variation of the angle/angle bracket
has a zero in every real periodic gap, including collapsed gaps. -/
theorem exists_thetaThetaDiscriminant_zero_on_gap
    (D : SourceAngularThetaCommonDomainData hp hp1 W₀ B W s)
    (h2p : (2 : ℝ≥0∞) ≤ p) (n m k : ℤ) (φ : realTypeSourceLocus p)
    (hn : canonicalPeriodicGap hp hp1 (periodOnePotential φ.val) (periodOnePotential_mem φ.val) n ≠ 0)
    (hm : canonicalPeriodicGap hp hp1 (periodOnePotential φ.val) (periodOnePotential_mem φ.val) m ≠ 0) :
    ∃ w ∈ sourcePeriodicSegment hp hp1 φ.val k,
      sourceAngularThetaThetaDiscriminantBracket hp hp1 h2p n m s φ.val w = 0 := by
  obtain ⟨ch,hch,hc⟩ := exists_sourceRealActionBallChart_realCentered hp hp1 k φ
  have hφ : φ.val ∈ ball ch.center ch.radius := by rw [hch]; exact mem_ball_self ch.radius_pos
  have hgeom := ch.geometry φ.val hφ
  have hcircle := sourceCanonicalRootDomain_of_enclosingCircle hp hp1 φ.val k
    ch.spectralCenter ch.spectralRadius hgeom.1 hgeom.2
  let F := sourceAngularThetaThetaDiscriminantBracket hp hp1 h2p n m s φ.val
  have hF : AnalyticOnNhd ℂ F univ :=
    analyticOnNhd_sourceAngularThetaThetaDiscriminantBracket hp hp1 h2p n m s φ.val
  have hperiod := D.thetaThetaDiscriminant_period_eq_zero h2p n m k φ hn hm ch hφ
  rcases sourcePeriodicGap_eq_zero_or_open hp hp1 φ.val φ.property k with hcollapsed | hopen
  · have hmid := sourcePeriodicMidpoint_mem_segment hp hp1 φ.val k
    refine ⟨sourceStandardRootMidpoint hp hp1 φ.val k,hmid,?_⟩
    exact sourceEntireNumerator_zero_at_collapsedGap hp hp1 φ.val φ.property k F hF
      hcollapsed ch.spectralCenter ch.spectralRadius ch.spectralRadius_pos (hgeom.1 hmid)
      hgeom.2 hcircle hperiod
  · have hx : (ch.spectralCenter.re : ℂ) = ch.spectralCenter := by
      apply Complex.ext
      · rfl
      · simpa using hc.symm
    obtain ⟨w,hw,hzero⟩ := exists_sourceEntireNumerator_zero_on_openGap hp hp1 φ.val φ.property k F hF
      (D.thetaThetaDiscriminant_im_eq_zero h2p n m φ hn hm) hopen
      ch.spectralCenter.re ch.spectralRadius ch.spectralRadius_pos
      (by simpa only [hx] using hgeom.1) (by simpa only [hx] using hgeom.2)
      (by simpa only [hx] using hcircle) (by simpa only [hx] using hperiod)
    exact ⟨w,sourceStandardRoot_gapSegment_subset_periodicSegment hp hp1 φ.val k hw,hzero⟩

/-- Choosing all actual gap zeros gives a full spectral displacement
sequence in `ℓp`, with no extra zero or summability assumption. -/
theorem exists_thetaThetaDiscriminant_gapZero_sequence
    (D : SourceAngularThetaCommonDomainData hp hp1 W₀ B W s)
    (h2p : (2 : ℝ≥0∞) ≤ p) (n m : ℤ) (φ : realTypeSourceLocus p)
    (hn : canonicalPeriodicGap hp hp1 (periodOnePotential φ.val) (periodOnePotential_mem φ.val) n ≠ 0)
    (hm : canonicalPeriodicGap hp hp1 (periodOnePotential φ.val) (periodOnePotential_mem φ.val) m ≠ 0) :
    ∃ ρ : ℤ → ℂ, Memℓp (fun k => ρ k-(Real.pi:ℂ)*k) p ∧
      ∀ k : ℤ, ρ k ∈ sourcePeriodicSegment hp hp1 φ.val k ∧
        sourceAngularThetaThetaDiscriminantBracket hp hp1 h2p n m s φ.val (ρ k) = 0 := by
  classical
  choose ρ hρ hzero using (fun k => D.exists_thetaThetaDiscriminant_zero_on_gap h2p n m k φ hn hm)
  exact ⟨ρ,memℓp_sourcePeriodicSegment_samples hp hp1 φ.val ρ hρ,fun k => ⟨hρ k,hzero k⟩⟩

end SourceAngularThetaCommonDomainData
end NLS.ZakharovShabat
