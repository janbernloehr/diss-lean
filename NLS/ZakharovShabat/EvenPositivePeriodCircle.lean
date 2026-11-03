import NLS.ZakharovShabat.EvenPsiAntisymmetricPeriods
import NLS.ComplexAnalysis.RightHalfPlaneSquareRoot

/-! # Positive original circles lie in the right half-plane

An even discriminant puts zero in the actual central gap. Complete
canonical order and the original isolating-circle geometry then force
every positive-index closed disc strictly into the right half-plane.
-/
noncomputable section
open Set Metric Complex
open NLS.ComplexAnalysis
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]
variable (hp : p ≠ ⊤) (hp1 : 1 < p) (ψ : CoeffPair p)
  (heven : ∀ z, canonicalDiscriminant hp (periodOnePotential ψ) (-z) =
    canonicalDiscriminant hp (periodOnePotential ψ) z)
include heven

theorem zero_mem_sourcePeriodicSegment_of_discriminant_even :
    (0:ℂ) ∈ sourcePeriodicSegment hp hp1 ψ 0 := by
  have hm := sourcePeriodicMidpoint_neg_of_discriminant_even hp hp1 ψ heven 0
  simp only [neg_zero] at hm
  have hz : canonicalPeriodicMidpoint hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) 0 = 0 := by
    linear_combination hm / 2
  simpa only [hz] using sourcePeriodicMidpoint_mem_segment hp hp1 ψ 0

theorem SourceCriticalRootPeriodCircle.center_sub_radius_pos_of_even
    {m : ℤ} (hm : 0 < m) (D : SourceCriticalRootPeriodCircle hp hp1 ψ m) :
    0 < D.center-D.radius := by
  let l := canonicalPeriodicLeft hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ)
  let r := canonicalPeriodicRight hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ)
  have hs := canonicalPeriodicEndpoints_spec hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ)
  have hn := (canonicalPeriodicEndpoints_neg_of_discriminant_even hp hp1 (periodOnePotential ψ)
    (periodOnePotential_mem ψ) heven 0).1
  have hw := re_le_of_complexLexLE (hs.2.1 0)
  have hl0 : l 0 = -r 0 := by simpa only [neg_zero] using hn
  change (l 0).re ≤ (r 0).re at hw
  rw [hl0,neg_re] at hw
  have hr0 : 0 ≤ (r 0).re := by linarith
  have hlm : 0 ≤ (l m).re := hr0.trans (re_le_of_complexLexLE (hs.2.2 0 m hm))
  have hb := re_bounds_of_mem_realCenteredBall
    (D.gap (left_mem_segment ℝ (l m) (r m)))
  rcases D.other 0 (ne_of_lt hm) 0
    (zero_mem_sourcePeriodicSegment_of_discriminant_even hp hp1 ψ heven) with h | h
  · simpa only [zero_re] using h
  · simp only [zero_re] at h
    linarith [hb.2]

theorem SourceCriticalRootPeriodCircle.re_pos_on_closedBall_of_even
    {m : ℤ} (hm : 0 < m) (D : SourceCriticalRootPeriodCircle hp hp1 ψ m)
    (z : ℂ) (hz : z ∈ closedBall (D.center:ℂ) D.radius) : 0 < z.re :=
  (D.center_sub_radius_pos_of_even hp hp1 ψ heven hm).trans_le
    (re_bounds_of_mem_realCenteredClosedBall hz).1

theorem SourceCriticalRootPeriodCircle.sqrt_sq_on_closedBall_of_even
    {m : ℤ} (hm : 0 < m) (D : SourceCriticalRootPeriodCircle hp hp1 ψ m)
    (z : ℂ) (hz : z ∈ closedBall (D.center:ℂ) D.radius) : sqrt (z^2) = z :=
  sqrt_sq_of_re_pos z (D.re_pos_on_closedBall_of_even hp hp1 ψ heven hm z hz)

end NLS.ZakharovShabat
