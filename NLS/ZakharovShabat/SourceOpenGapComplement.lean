import NLS.ZakharovShabat.SourceFloquetMultiplier
import NLS.ZakharovShabat.SourceCanonicalRootGapIsolation
import NLS.ZakharovShabat.CanonicalPeriodicLevels

/-! # Analytic continuation through collapsed periodic gaps

Only noncollapsed segments obstruct the actual canonical root and Floquet
multiplier. The multiplier's logarithmic derivative supplies the regular
extension of `Δ'/root`; the literal quotient is not used at collapsed points.
-/
noncomputable section
open Set Complex
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The spectral plane with only the noncollapsed periodic cuts removed. -/
def sourceOpenGapComplement (hp : p ≠ ⊤) (hp1 : 1 < p) (φ : CoeffPair p) : Set ℂ :=
  {z | ∀ n : ℤ, canonicalPeriodicGap hp hp1 (periodOnePotential φ)
    (periodOnePotential_mem φ) n ≠ 0 → z ∉ sourcePeriodicSegment hp hp1 φ n}

theorem sourceCanonicalRootDomain_subset_openGapComplement (hp : p ≠ ⊤) (hp1 : 1 < p)
    (φ : CoeffPair p) : sourceCanonicalRootDomain hp hp1 φ ⊆ sourceOpenGapComplement hp hp1 φ :=
  fun _ hz n _ => hz n

/-- A point in the enlarged domain is either off all cuts or on a collapsed cut. -/
theorem mem_sourceOpenGapComplement_cases (hp : p ≠ ⊤) (hp1 : 1 < p)
    (φ : CoeffPair p) (z : ℂ) (hz : z ∈ sourceOpenGapComplement hp hp1 φ) :
    z ∈ sourceCanonicalRootDomain hp hp1 φ ∨
      ∃ n : ℤ, canonicalPeriodicGap hp hp1 (periodOnePotential φ)
        (periodOnePotential_mem φ) n = 0 ∧ z ∈ sourcePeriodicSegment hp hp1 φ n := by
  classical
  by_cases h : z ∈ sourceCanonicalRootDomain hp hp1 φ
  · exact Or.inl h
  · right
    simp only [sourceCanonicalRootDomain, mem_ofPred_eq, not_forall, not_not] at h
    obtain ⟨n, hn⟩ := h
    exact ⟨n, by_contra fun hg => hz n hg hn, hn⟩

/-- Collapsing a gap turns its entire segment into the common endpoint. -/
theorem sourcePeriodicSegment_eq_singleton_of_zeroGap (hp : p ≠ ⊤) (hp1 : 1 < p)
    (φ : CoeffPair p) (n : ℤ)
    (hn : canonicalPeriodicGap hp hp1 (periodOnePotential φ) (periodOnePotential_mem φ) n = 0) :
    sourcePeriodicSegment hp hp1 φ n =
      {canonicalPeriodicLeft hp hp1 (periodOnePotential φ) (periodOnePotential_mem φ) n} := by
  have he := sub_eq_zero.mp hn
  simp only [sourcePeriodicSegment, he, segment_same]

/-- An entire collapsed segment belongs to the enlarged domain. -/
theorem sourcePeriodicSegment_subset_openGapComplement_of_zeroGap
    (hp : p ≠ ⊤) (hp1 : 1 < p) (φ : CoeffPair p)
    (hφ : IsRealType (CoeffPair.toMax p φ)) (n : ℤ)
    (hn : canonicalPeriodicGap hp hp1 (periodOnePotential φ) (periodOnePotential_mem φ) n = 0) :
    sourcePeriodicSegment hp hp1 φ n ⊆ sourceOpenGapComplement hp hp1 φ := by
  obtain ⟨W, _, _, hreal, hdisjoint⟩ := exists_global_source_disjoint_periodicSegments hp hp1
  intro z hz m hm
  have hnm : n ≠ m := by
    rintro rfl
    exact hm hn
  exact Set.disjoint_left.mp (hdisjoint φ (hreal hφ) n m hnm) hz

/-- The actual product, including its defined value at a collapsed point, is analytic. -/
theorem sourceCanonicalRoot_analyticOnNhd_openGapComplement (hp : p ≠ ⊤) (hp1 : 1 < p)
    (φ : CoeffPair p) (hφ : IsRealType (CoeffPair.toMax p φ)) :
    AnalyticOnNhd ℂ (sourceCanonicalRoot hp hp1 φ) (sourceOpenGapComplement hp hp1 φ) := by
  obtain ⟨W, _, _, hreal, _, _, hclosed, _⟩ :=
    exists_global_source_canonicalRoot_gapSide_theorem hp hp1
  obtain ⟨V, _, _, hrealV, hdisjoint⟩ := exists_global_source_disjoint_periodicSegments hp hp1
  intro z hz
  rcases mem_sourceOpenGapComplement_cases hp hp1 φ z hz with hz | ⟨n, hn, hzn⟩
  · exact sourceCanonicalRoot_analyticOnNhd hp hp1 φ z hz
  · apply hclosed φ (hreal hφ) n hn z
    intro m hmn
    exact Set.disjoint_left.mp (hdisjoint φ (hrealV hφ) n m hmn.symm) hzn

/-- The square identity persists at the collapsed endpoints. -/
theorem sourceCanonicalRoot_sq_eq_on_openGapComplement (hp : p ≠ ⊤) (hp1 : 1 < p)
    (φ : CoeffPair p) (hφ : IsRealType (CoeffPair.toMax p φ))
    (z : ℂ) (hz : z ∈ sourceOpenGapComplement hp hp1 φ) :
    sourceCanonicalRoot hp hp1 φ z ^ 2 =
      canonicalDiscriminant hp (periodOnePotential φ) z ^ 2 - 4 := by
  rcases mem_sourceOpenGapComplement_cases hp hp1 φ z hz with hz | ⟨n, hn, hzn⟩
  · exact sourceCanonicalRoot_sq_eq_discriminant_sq_sub_four hp hp1 φ z hz
  · rw [sourcePeriodicSegment_eq_singleton_of_zeroGap hp hp1 φ n hn] at hzn
    have hz := Set.mem_singleton_iff.mp hzn
    have he := sub_eq_zero.mp hn
    have hr : sourceCanonicalRoot hp hp1 φ z = 0 := by
      rw [sourceCanonicalRoot_eq_omitted hp hp1 n, sourceStandardRoot_of_zeroGap hp hp1 φ n z hn]
      rw [canonicalPeriodicMidpoint, he, ← hz]
      ring
    have hd := (canonicalPeriodicEndpoints_discriminant_of_realType hp hp1
      (periodOnePotential φ) (periodOnePotential_mem φ) (isRealType_periodOnePotential φ hφ) n).1
    rw [hr, hz, hd]
    split <;> norm_num

/-- The Floquet multiplier remains analytic through every collapsed gap. -/
theorem sourceFloquetMultiplier_analyticOnNhd_openGapComplement (hp : p ≠ ⊤) (hp1 : 1 < p)
    (φ : CoeffPair p) (hφ : IsRealType (CoeffPair.toMax p φ)) :
    AnalyticOnNhd ℂ (sourceFloquetMultiplier hp hp1 φ) (sourceOpenGapComplement hp hp1 φ) := by
  intro z hz
  exact ((analyticOnNhd_canonicalDiscriminant hp hp1 _ (periodOnePotential_mem φ) z (mem_univ z)).add
    (sourceCanonicalRoot_analyticOnNhd_openGapComplement hp hp1 φ hφ z hz)).div_const (c := (2 : ℂ))

theorem sourceFloquetMultiplier_mul_companion_openGapComplement (hp : p ≠ ⊤) (hp1 : 1 < p)
    (φ : CoeffPair p) (hφ : IsRealType (CoeffPair.toMax p φ))
    (z : ℂ) (hz : z ∈ sourceOpenGapComplement hp hp1 φ) :
    sourceFloquetMultiplier hp hp1 φ z *
      ((canonicalDiscriminant hp (periodOnePotential φ) z - sourceCanonicalRoot hp hp1 φ z)/2) = 1 := by
  have hs := sourceCanonicalRoot_sq_eq_on_openGapComplement hp hp1 φ hφ z hz
  unfold sourceFloquetMultiplier
  linear_combination -(1/4 : ℂ) * hs

theorem sourceFloquetMultiplier_ne_zero_openGapComplement (hp : p ≠ ⊤) (hp1 : 1 < p)
    (φ : CoeffPair p) (hφ : IsRealType (CoeffPair.toMax p φ))
    (z : ℂ) (hz : z ∈ sourceOpenGapComplement hp hp1 φ) :
    sourceFloquetMultiplier hp hp1 φ z ≠ 0 := by
  intro h
  have he := sourceFloquetMultiplier_mul_companion_openGapComplement hp hp1 φ hφ z hz
  rw [h, zero_mul] at he
  exact zero_ne_one he

/-- The filled critical-root quotient, defined using the nonzero multiplier. -/
def sourceFloquetLogDerivative (hp : p ≠ ⊤) (hp1 : 1 < p) (φ : CoeffPair p) (z : ℂ) : ℂ :=
  deriv (sourceFloquetMultiplier hp hp1 φ) z / sourceFloquetMultiplier hp hp1 φ z

theorem sourceFloquetLogDerivative_analyticOnNhd (hp : p ≠ ⊤) (hp1 : 1 < p)
    (φ : CoeffPair p) (hφ : IsRealType (CoeffPair.toMax p φ)) :
    AnalyticOnNhd ℂ (sourceFloquetLogDerivative hp hp1 φ) (sourceOpenGapComplement hp hp1 φ) := by
  intro z hz
  have ha := sourceFloquetMultiplier_analyticOnNhd_openGapComplement hp hp1 φ hφ z hz
  exact ha.deriv.div ha (sourceFloquetMultiplier_ne_zero_openGapComplement hp hp1 φ hφ z hz)

/-- On the original cut complement, the filled expression is exactly the spectral quotient. -/
theorem sourceFloquetLogDerivative_eq_criticalRootRatio (hp : p ≠ ⊤) (hp1 : 1 < p)
    (φ : CoeffPair p) (hφ : IsRealType (CoeffPair.toMax p φ))
    (z : ℂ) (hz : z ∈ sourceCanonicalRootDomain hp hp1 φ) :
    sourceFloquetLogDerivative hp hp1 φ z =
      deriv (canonicalDiscriminant hp (periodOnePotential φ)) z / sourceCanonicalRoot hp hp1 φ z := by
  unfold sourceFloquetLogDerivative
  rw [(hasDerivAt_sourceFloquetMultiplier hp hp1 φ hφ z hz).deriv]
  field_simp [sourceFloquetMultiplier_ne_zero hp hp1 φ z hz]

end NLS.ZakharovShabat
