import NLS.ZakharovShabat.SourcePeriodCircleSymmetries
import NLS.ZakharovShabat.SourceCanonicalRootReflection
import NLS.ComplexAnalysis.TwoEndpointRoot

/-! # The zero-frequency pole in Lemma 10's lower action level

Both printed symmetry hypotheses force the actual central gap to contain
zero, even for complex sources. Every original isolating circuit then avoids
zero. Noncentral discs exclude it, while the central disc encloses it.
These distinctions are retained before any Laurent contour is differentiated.
-/
noncomputable section
open Set Metric Complex
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

theorem sourcePeriodicReflection_of_componentSwap_scaling (hp : p ≠ ⊤) (hp1 : 1 < p)
    (φ : CoeffPair p) (c : ℂ) (hc : c ≠ 0)
    (hφ : sourceComponentSwap φ = sourceReciprocalScaling c φ) :
    SourcePeriodicReflection hp hp1 φ := by
  obtain ⟨hl,hr⟩ := sourceCanonicalPeriodicEndpoints_reciprocalScaling hp hp1 c hc φ
  intro n
  have he := sourceCanonicalPeriodicEndpoints_componentSwap hp hp1 φ (-n)
  rw [hφ,hl,hr,neg_neg] at he
  exact he

theorem sourceReciprocalScaling_negative_identity (φ : CoeffPair p) :
    sourceReciprocalScaling (-1) φ = -φ := by
  apply (CoeffPair.toMax p).injective
  apply Prod.ext <;> simp

theorem sourcePeriodicReflection_of_signed_midpoint (hp : p ≠ ⊤) (hp1 : 1 < p)
    (φ : CoeffPair p) (hφ : sourceMidpointReflection φ = φ ∨ sourceMidpointReflection φ = -φ) :
    SourcePeriodicReflection hp hp1 φ := by
  intro n
  have he := sourceCanonicalPeriodicEndpoints_midpointReflection hp hp1 φ (-n)
  rcases hφ with hφ | hφ
  · simpa only [hφ,neg_neg] using he
  · obtain ⟨hl,hr⟩ := sourceCanonicalPeriodicEndpoints_reciprocalScaling hp hp1 (-1) (by norm_num) φ
    rw [sourceReciprocalScaling_negative_identity] at hl hr
    simpa only [hφ,hl,hr,neg_neg] using he

theorem SourcePeriodicReflection.zero_mem_central_segment
    {hp : p ≠ ⊤} {hp1 : 1 < p} {φ : CoeffPair p} (h : SourcePeriodicReflection hp hp1 φ) :
    (0:ℂ) ∈ sourcePeriodicSegment hp hp1 φ 0 := by
  have he := (h 0).1
  simp only [neg_zero] at he
  have hm := NLS.ComplexAnalysis.pair_midpoint_mem_segment
    (canonicalPeriodicLeft hp hp1 (periodOnePotential φ) (periodOnePotential_mem φ) 0)
    (canonicalPeriodicRight hp hp1 (periodOnePotential φ) (periodOnePotential_mem φ) 0)
  rw [he,neg_add_cancel,zero_div] at hm
  change (0:ℂ) ∈ segment ℝ _ _
  rw [he]
  exact hm

theorem SourceCriticalRootPeriodCircle.zero_not_mem_sphere_of_reflection
    {hp : p ≠ ⊤} {hp1 : 1 < p} {φ : CoeffPair p} {n : ℤ}
    (D : SourceCriticalRootPeriodCircle hp hp1 φ n) (h : SourcePeriodicReflection hp hp1 φ) :
    (0:ℂ) ∉ sphere (D.center:ℂ) D.radius := by
  intro hz
  exact D.sphere_subset_rootDomain hz 0 h.zero_mem_central_segment

theorem SourceCriticalRootPeriodCircle.zero_not_mem_noncentral_disc_of_reflection
    {hp : p ≠ ⊤} {hp1 : 1 < p} {φ : CoeffPair p} {n : ℤ}
    (D : SourceCriticalRootPeriodCircle hp hp1 φ n) (h : SourcePeriodicReflection hp hp1 φ)
    (hn : n ≠ 0) : (0:ℂ) ∉ closedBall (D.center:ℂ) D.radius := by
  intro hz
  exact D.closedBall_subset_omittedDomain hz 0 hn.symm h.zero_mem_central_segment

theorem SourceCriticalRootPeriodCircle.zero_mem_central_ball_of_reflection
    {hp : p ≠ ⊤} {hp1 : 1 < p} {φ : CoeffPair p}
    (D : SourceCriticalRootPeriodCircle hp hp1 φ 0) (h : SourcePeriodicReflection hp hp1 φ) :
    (0:ℂ) ∈ ball (D.center:ℂ) D.radius := D.gap h.zero_mem_central_segment

end NLS.ZakharovShabat
