import NLS.ZakharovShabat.SourceCanonicalRootProduct

/-! Exact reflection of the literal canonical root product. The single
root formula, the central factor and every symmetric finite cutoff retain
their signs, so the limiting identity includes points on the gap cuts. -/
noncomputable section
open Set Complex Filter Topology
open scoped ENNReal Classical
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- Both ordered endpoint slots reflect with reversed order. -/
def SourcePeriodicReflection (hp : p ≠ ⊤) (hp1 : 1 < p) (ψ : CoeffPair p) : Prop :=
  ∀ n : ℤ,
    canonicalPeriodicLeft hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) (-n) =
      -canonicalPeriodicRight hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) n ∧
    canonicalPeriodicRight hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) (-n) =
      -canonicalPeriodicLeft hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) n

theorem SourcePeriodicReflection.midpoint_neg {hp : p ≠ ⊤} {hp1 : 1 < p} {ψ : CoeffPair p}
    (h : SourcePeriodicReflection hp hp1 ψ) (n : ℤ) :
    canonicalPeriodicMidpoint hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) (-n) =
      -canonicalPeriodicMidpoint hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) n := by
  rw [canonicalPeriodicMidpoint,canonicalPeriodicMidpoint,(h n).1,(h n).2]
  ring

theorem SourcePeriodicReflection.gap_neg {hp : p ≠ ⊤} {hp1 : 1 < p} {ψ : CoeffPair p}
    (h : SourcePeriodicReflection hp hp1 ψ) (n : ℤ) :
    canonicalPeriodicGap hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) (-n) =
      canonicalPeriodicGap hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) n := by
  rw [canonicalPeriodicGap,canonicalPeriodicGap,(h n).1,(h n).2]
  ring

theorem normalizedStandardRoot_neg_center (t g z : ℂ) :
    normalizedStandardRoot (-t) g (-z) = -normalizedStandardRoot t g z := by
  unfold normalizedStandardRoot
  have he : -t-(-z) = -(t-z) := by ring
  rw [he,neg_sq]
  ring

theorem SourcePeriodicReflection.standardRoot_neg {hp : p ≠ ⊤} {hp1 : 1 < p} {ψ : CoeffPair p}
    (h : SourcePeriodicReflection hp hp1 ψ) (n : ℤ) (z : ℂ) :
    sourceStandardRoot hp hp1 ψ (-n) (-z) = -sourceStandardRoot hp hp1 ψ n z := by
  rw [sourceStandardRoot,sourceStandardRoot,h.midpoint_neg n,h.gap_neg n,
    normalizedStandardRoot_neg_center]

/-- The central factor changes sign; every positive/negative pair is invariant. -/
theorem SourcePeriodicReflection.canonicalRootPartial_neg
    {hp : p ≠ ⊤} {hp1 : 1 < p} {ψ : CoeffPair p}
    (h : SourcePeriodicReflection hp hp1 ψ) (N : ℕ) (z : ℂ) :
    sourceCanonicalRootPartialProduct hp hp1 N ψ (-z) =
      -sourceCanonicalRootPartialProduct hp hp1 N ψ z := by
  have hr (m : ℤ) : sourceStandardRoot hp hp1 ψ m (-z) =
      -sourceStandardRoot hp hp1 ψ (-m) z := by
    simpa only [neg_neg] using h.standardRoot_neg (-m) z
  unfold sourceCanonicalRootPartialProduct
  simp_rw [hr]
  rw [prod_symmetric_interval,prod_symmetric_interval]
  have hpairs : (∏ j ∈ Finset.range N,
      ((-sourceStandardRoot hp hp1 ψ (-((j:ℤ)+1)) z / singleSpectralDenominator ((j:ℤ)+1)) *
       (-sourceStandardRoot hp hp1 ψ (-(-((j:ℤ)+1))) z / singleSpectralDenominator (-((j:ℤ)+1))))) =
      ∏ j ∈ Finset.range N,
      ((sourceStandardRoot hp hp1 ψ ((j:ℤ)+1) z / singleSpectralDenominator ((j:ℤ)+1)) *
       (sourceStandardRoot hp hp1 ψ (-((j:ℤ)+1)) z / singleSpectralDenominator (-((j:ℤ)+1)))) := by
    apply Finset.prod_congr rfl
    intro j _
    simp only [neg_neg]
    ring
  rw [hpairs]
  simp only [neg_zero]
  ring

/-- Exact oddness of the actual full product, including its sign and all cut points. -/
theorem SourcePeriodicReflection.canonicalRoot_neg
    {hp : p ≠ ⊤} {hp1 : 1 < p} {ψ : CoeffPair p}
    (h : SourcePeriodicReflection hp hp1 ψ) (z : ℂ) :
    sourceCanonicalRoot hp hp1 ψ (-z) = -sourceCanonicalRoot hp hp1 ψ z := by
  have ht := (tendsto_sourceCanonicalRootPartialProduct hp hp1 ψ z).neg
  have ht' := tendsto_sourceCanonicalRootPartialProduct hp hp1 ψ (-z)
  simp_rw [h.canonicalRootPartial_neg] at ht'
  exact tendsto_nhds_unique ht' ht

/-- Reflection sends the entire closed gap segment to its opposite-index segment. -/
theorem SourcePeriodicReflection.neg_mem_segment_iff
    {hp : p ≠ ⊤} {hp1 : 1 < p} {ψ : CoeffPair p}
    (h : SourcePeriodicReflection hp hp1 ψ) (n : ℤ) (z : ℂ) :
    -z ∈ sourcePeriodicSegment hp hp1 ψ (-n) ↔ z ∈ sourcePeriodicSegment hp hp1 ψ n := by
  let a := canonicalPeriodicLeft hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) n
  let b := canonicalPeriodicRight hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) n
  let f : ℂ →ᵃ[ℝ] ℂ := (-LinearMap.id : ℂ →ₗ[ℝ] ℂ).toAffineMap
  have hi : f '' segment ℝ a b = segment ℝ (-a) (-b) := image_segment ℝ f a b
  change -z ∈ segment ℝ _ _ ↔ z ∈ segment ℝ a b
  rw [(h n).1,(h n).2,segment_symm]
  change -z ∈ segment ℝ (-a) (-b) ↔ z ∈ segment ℝ a b
  rw [← hi]
  constructor
  · rintro ⟨w,hw,he⟩
    change -w = -z at he
    exact neg_injective he ▸ hw
  · intro hz
    exact ⟨z,hz,rfl⟩

/-- The full canonical cut complement is invariant under spectral negation. -/
theorem SourcePeriodicReflection.neg_mem_rootDomain_iff
    {hp : p ≠ ⊤} {hp1 : 1 < p} {ψ : CoeffPair p}
    (h : SourcePeriodicReflection hp hp1 ψ) (z : ℂ) :
    -z ∈ sourceCanonicalRootDomain hp hp1 ψ ↔ z ∈ sourceCanonicalRootDomain hp hp1 ψ := by
  constructor
  · intro hz n hn
    exact hz (-n) ((h.neg_mem_segment_iff n z).mpr hn)
  · intro hz n hn
    apply hz (-n)
    apply (h.neg_mem_segment_iff (-n) z).mp
    simpa only [neg_neg] using hn

end NLS.ZakharovShabat
