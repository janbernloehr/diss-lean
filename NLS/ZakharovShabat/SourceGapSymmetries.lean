import NLS.ZakharovShabat.SourceMidpointSpectralData
import NLS.ZakharovShabat.SourceReciprocalScaling
import NLS.ZakharovShabat.SourceOpenGapComplement

/-! # Literal closed periodic gap transport on the full complex source space -/
noncomputable section
open Set Complex
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

private theorem neg_mem_reversed_segment (a b z : ℂ) :
    -z ∈ segment ℝ (-b) (-a) ↔ z ∈ segment ℝ a b := by
  let f : ℂ →ᵃ[ℝ] ℂ := (-LinearMap.id : ℂ →ₗ[ℝ] ℂ).toAffineMap
  have hi : f '' segment ℝ a b = segment ℝ (-a) (-b) := image_segment ℝ f a b
  rw [segment_symm ℝ (-b),← hi]
  constructor
  · rintro ⟨w,hw,he⟩
    change -w = -z at he
    exact neg_injective he ▸ hw
  · intro hz
    exact ⟨z,hz,rfl⟩

theorem sourcePeriodicSegment_componentSwap (hp : p ≠ ⊤) (hp1 : 1 < p)
    (φ : CoeffPair p) (n : ℤ) (z : ℂ) :
    -z ∈ sourcePeriodicSegment hp hp1 (sourceComponentSwap φ) (-n) ↔
      z ∈ sourcePeriodicSegment hp hp1 φ n := by
  obtain ⟨hl,hr⟩ := sourceCanonicalPeriodicEndpoints_componentSwap hp hp1 φ (-n)
  simp only [neg_neg] at hl hr
  unfold sourcePeriodicSegment
  rw [hl,hr]
  exact neg_mem_reversed_segment _ _ _

theorem sourcePeriodicSegment_midpointReflection (hp : p ≠ ⊤) (hp1 : 1 < p)
    (φ : CoeffPair p) (n : ℤ) (z : ℂ) :
    -z ∈ sourcePeriodicSegment hp hp1 (sourceMidpointReflection φ) (-n) ↔
      z ∈ sourcePeriodicSegment hp hp1 φ n := by
  obtain ⟨hl,hr⟩ := sourceCanonicalPeriodicEndpoints_midpointReflection hp hp1 φ (-n)
  simp only [neg_neg] at hl hr
  unfold sourcePeriodicSegment
  rw [hl,hr]
  exact neg_mem_reversed_segment _ _ _

theorem sourcePeriodicSegment_reciprocalScaling (hp : p ≠ ⊤) (hp1 : 1 < p)
    (c : ℂ) (hc : c ≠ 0) (φ : CoeffPair p) (n : ℤ) :
    sourcePeriodicSegment hp hp1 (sourceReciprocalScaling c φ) n = sourcePeriodicSegment hp hp1 φ n := by
  obtain ⟨hl,hr⟩ := sourceCanonicalPeriodicEndpoints_reciprocalScaling hp hp1 c hc φ
  unfold sourcePeriodicSegment
  rw [hl,hr]

theorem sourceCanonicalRootDomain_componentSwap (hp : p ≠ ⊤) (hp1 : 1 < p)
    (φ : CoeffPair p) (z : ℂ) :
    -z ∈ sourceCanonicalRootDomain hp hp1 (sourceComponentSwap φ) ↔
      z ∈ sourceCanonicalRootDomain hp hp1 φ := by
  constructor
  · intro hz n hn
    exact hz (-n) ((sourcePeriodicSegment_componentSwap hp hp1 φ n z).mpr hn)
  · intro hz n hn
    apply hz (-n)
    apply (sourcePeriodicSegment_componentSwap hp hp1 φ (-n) z).mp
    simpa only [neg_neg] using hn

theorem sourceCanonicalRootDomain_midpointReflection (hp : p ≠ ⊤) (hp1 : 1 < p)
    (φ : CoeffPair p) (z : ℂ) :
    -z ∈ sourceCanonicalRootDomain hp hp1 (sourceMidpointReflection φ) ↔
      z ∈ sourceCanonicalRootDomain hp hp1 φ := by
  constructor
  · intro hz n hn
    exact hz (-n) ((sourcePeriodicSegment_midpointReflection hp hp1 φ n z).mpr hn)
  · intro hz n hn
    apply hz (-n)
    apply (sourcePeriodicSegment_midpointReflection hp hp1 φ (-n) z).mp
    simpa only [neg_neg] using hn

theorem sourceCanonicalRootDomain_reciprocalScaling (hp : p ≠ ⊤) (hp1 : 1 < p)
    (c : ℂ) (hc : c ≠ 0) (φ : CoeffPair p) :
    sourceCanonicalRootDomain hp hp1 (sourceReciprocalScaling c φ) = sourceCanonicalRootDomain hp hp1 φ := by
  ext z
  simp only [sourceCanonicalRootDomain,mem_ofPred_eq,sourcePeriodicSegment_reciprocalScaling hp hp1 c hc]

theorem sourcePeriodicGap_midpointReflection (hp : p ≠ ⊤) (hp1 : 1 < p) (φ : CoeffPair p) (n : ℤ) :
    canonicalPeriodicGap hp hp1 (periodOnePotential (sourceMidpointReflection φ)) (periodOnePotential_mem _) (-n) =
      canonicalPeriodicGap hp hp1 (periodOnePotential φ) (periodOnePotential_mem _) n := by
  obtain ⟨hl,hr⟩ := sourceCanonicalPeriodicEndpoints_midpointReflection hp hp1 φ (-n)
  simp only [neg_neg] at hl hr
  unfold canonicalPeriodicGap
  rw [hl,hr]
  ring

theorem sourcePeriodicGap_reciprocalScaling (hp : p ≠ ⊤) (hp1 : 1 < p)
    (c : ℂ) (hc : c ≠ 0) (φ : CoeffPair p) (n : ℤ) :
    canonicalPeriodicGap hp hp1 (periodOnePotential (sourceReciprocalScaling c φ)) (periodOnePotential_mem _) n =
      canonicalPeriodicGap hp hp1 (periodOnePotential φ) (periodOnePotential_mem _) n := by
  obtain ⟨hl,hr⟩ := sourceCanonicalPeriodicEndpoints_reciprocalScaling hp hp1 c hc φ
  unfold canonicalPeriodicGap
  rw [hl,hr]

theorem sourceOpenGapComplement_componentSwap (hp : p ≠ ⊤) (hp1 : 1 < p)
    (φ : CoeffPair p) (z : ℂ) :
    -z ∈ sourceOpenGapComplement hp hp1 (sourceComponentSwap φ) ↔ z ∈ sourceOpenGapComplement hp hp1 φ := by
  constructor
  · intro hz n hg hn
    exact hz (-n) (by simpa only [sourcePeriodicGap_componentSwap,neg_neg] using hg)
      ((sourcePeriodicSegment_componentSwap hp hp1 φ n z).mpr hn)
  · intro hz n hg hn
    apply hz (-n) (by simpa only [sourcePeriodicGap_componentSwap] using hg)
    apply (sourcePeriodicSegment_componentSwap hp hp1 φ (-n) z).mp
    simpa only [neg_neg] using hn

theorem sourceOpenGapComplement_midpointReflection (hp : p ≠ ⊤) (hp1 : 1 < p)
    (φ : CoeffPair p) (z : ℂ) :
    -z ∈ sourceOpenGapComplement hp hp1 (sourceMidpointReflection φ) ↔ z ∈ sourceOpenGapComplement hp hp1 φ := by
  constructor
  · intro hz n hg hn
    exact hz (-n) (by simpa only [sourcePeriodicGap_midpointReflection] using hg)
      ((sourcePeriodicSegment_midpointReflection hp hp1 φ n z).mpr hn)
  · intro hz n hg hn
    apply hz (-n) (by simpa only [← sourcePeriodicGap_midpointReflection hp hp1 φ (-n),neg_neg] using hg)
    apply (sourcePeriodicSegment_midpointReflection hp hp1 φ (-n) z).mp
    simpa only [neg_neg] using hn

theorem sourceOpenGapComplement_reciprocalScaling (hp : p ≠ ⊤) (hp1 : 1 < p)
    (c : ℂ) (hc : c ≠ 0) (φ : CoeffPair p) :
    sourceOpenGapComplement hp hp1 (sourceReciprocalScaling c φ) = sourceOpenGapComplement hp hp1 φ := by
  ext z
  simp only [sourceOpenGapComplement,mem_ofPred_eq,sourcePeriodicGap_reciprocalScaling hp hp1 c hc,
    sourcePeriodicSegment_reciprocalScaling hp hp1 c hc]

end NLS.ZakharovShabat
