import NLS.ZakharovShabat.SourceReflectionSymmetry

/-! # Actual signed gap coordinates on the reflection-symmetric slice

At a reflection-fixed real source, the Dirichlet and Neumann roots occupy
the two opposite periodic endpoints. Their difference is therefore a
signed gap length. The full difference sequence belongs to the original
coefficient space; its square is the actual squared periodic gap at every
index. These assertions do not claim global injectivity of the signed-gap map.
-/
noncomputable section
open Set Complex
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- A zero of an ordinary boundary characteristic in the nth real gap has the nth label. -/
theorem sourceBoundaryRoot_eq_of_zero_mem_gap (hp : p ≠ ⊤) (hp1 : 1 < p)
    (b : BoundaryCondition) (φ : realTypeSourceSubmodule p) (n : ℤ) (z : ℂ)
    (hz : periodOneBoundaryCharacteristic hp hp1 b φ.val z = 0)
    (hgap : z.re ∈ Icc
      (canonicalPeriodicLeft hp hp1 (periodOnePotential φ.val) (periodOnePotential_mem _) n).re
      (canonicalPeriodicRight hp hp1 (periodOnePotential φ.val) (periodOnePotential_mem _) n).re) :
    canonicalPeriodOneBoundaryRoots hp hp1 b φ.val n = z := by
  obtain ⟨k,hk⟩ := (canonicalPeriodOneBoundaryRoots_exhaustive hp hp1 b φ.val z).mp
    ((periodOneBoundaryCharacteristic_eq_zero_iff hp hp1 b φ.val z).mp hz)
  have hm := canonicalPeriodOneBoundaryRoots_mem_gap hp hp1 b φ.val φ.property k
  rw [hk] at hm
  have hkn : k = n := by
    rcases lt_trichotomy k n with h | h | h
    · have hs := canonicalPeriodicRight_re_lt_left_of_lt hp hp1 _
        (periodOnePotential_mem φ.val) (isRealType_periodOnePotential φ.val φ.property) h
      exact False.elim ((not_lt_of_ge (hgap.1.trans hm.2)) hs)
    · exact h
    · have hs := canonicalPeriodicRight_re_lt_left_of_lt hp hp1 _
        (periodOnePotential_mem φ.val) (isRealType_periodOnePotential φ.val φ.property) h
      exact False.elim ((not_lt_of_ge (hm.1.trans hgap.2)) hs)
  simpa only [hkn] using hk

/-- The full actual anti-discriminant vanishes on the symmetric slice. -/
theorem sourceAntiDiscriminant_eq_zero_of_reflection_fixed (hp : p ≠ ⊤) (hp1 : 1 < p)
    (φ : realTypeSourceSubmodule p) (hφ : realSourceSpatialReflection φ = φ) (z : ℂ) :
    sourceAntiDiscriminantCandidate hp hp1 φ.val z = 0 := by
  have h : sourceSpatialReflection φ.val = φ.val := congrArg Subtype.val hφ
  have he := sourceAntiDiscriminant_spatialReflection hp hp1 φ.val z
  rw [h] at he
  linear_combination (1/2 : ℂ) * he

/-- At a symmetric real source the two boundary roots are the opposite periodic endpoints. -/
theorem sourceBoundaryRoots_opposite_endpoints_of_reflection_fixed
    (hp : p ≠ ⊤) (hp1 : 1 < p) (φ : realTypeSourceSubmodule p)
    (hφ : realSourceSpatialReflection φ = φ) (n : ℤ) :
    let L := canonicalPeriodicLeft hp hp1 (periodOnePotential φ.val) (periodOnePotential_mem _) n
    let R := canonicalPeriodicRight hp hp1 (periodOnePotential φ.val) (periodOnePotential_mem _) n
    let μ := canonicalPeriodOneBoundaryRoots hp hp1 .dirichlet φ.val n
    let ν := canonicalPeriodOneBoundaryRoots hp hp1 .neumann φ.val n
    (μ = L ∧ ν = R) ∨ (μ = R ∧ ν = L) := by
  let L := canonicalPeriodicLeft hp hp1 (periodOnePotential φ.val) (periodOnePotential_mem _) n
  let R := canonicalPeriodicRight hp hp1 (periodOnePotential φ.val) (periodOnePotential_mem _) n
  let μ := canonicalPeriodOneBoundaryRoots hp hp1 .dirichlet φ.val n
  let ν := canonicalPeriodOneBoundaryRoots hp hp1 .neumann φ.val n
  change (μ = L ∧ ν = R) ∨ (μ = R ∧ ν = L)
  have hμ := canonicalPeriodOneBoundaryRoots_mem_gap hp hp1 .dirichlet φ.val φ.property n
  have hle : L.re ≤ R.re := hμ.1.trans hμ.2
  have him := canonicalPeriodicEndpoints_im_eq_zero_of_realType hp hp1 _
    (periodOnePotential_mem _) (isRealType_periodOnePotential φ.val φ.property) n
  have he : μ = L ∨ μ = R := by
    have h := (realSourceSpatialReflection_eq_self_iff_endpoints hp hp1 φ).mp hφ n
    have hμim := canonicalPeriodOneBoundaryRoots_im_eq_zero hp hp1 .dirichlet φ.val φ.property n
    rcases h with h | h
    · exact Or.inl (Complex.ext h (hμim.trans him.1.symm))
    · exact Or.inr (Complex.ext h (hμim.trans him.2.symm))
  have hprod (z : ℂ) (hz : z = L ∨ z = R) :
      periodOneBoundaryCharacteristic hp hp1 .dirichlet φ.val z *
        periodOneBoundaryCharacteristic hp hp1 .neumann φ.val z = 0 := by
    have hd := canonicalPeriodicEndpoints_discriminant_of_realType hp hp1 _
      (periodOnePotential_mem _) (isRealType_periodOnePotential φ.val φ.property) n
    have hlevel : (canonicalDiscriminant hp (periodOnePotential φ.val) z)^2-4 = 0 := by
      rcases hz with rfl | rfl
      · rw [hd.1]
        split_ifs <;> norm_num
      · rw [hd.2]
        split_ifs <;> norm_num
    have hs := sourceDiscriminant_sq_sub_four hp hp1 φ.val z
    rw [hlevel,sourceAntiDiscriminant_eq_zero_of_reflection_fixed hp hp1 φ hφ z] at hs
    linear_combination (1/4 : ℂ) * hs
  have hother (z : ℂ) (hz : z = L ∨ z = R) (hne : μ ≠ z) : ν = z := by
    have hmem : z.re ∈ Icc L.re R.re := by
      rcases hz with rfl | rfl
      · exact ⟨le_rfl,hle⟩
      · exact ⟨hle,le_rfl⟩
    have hD : periodOneBoundaryCharacteristic hp hp1 .dirichlet φ.val z ≠ 0 := by
      intro h
      exact hne (sourceBoundaryRoot_eq_of_zero_mem_gap hp hp1 .dirichlet φ n z h hmem)
    exact sourceBoundaryRoot_eq_of_zero_mem_gap hp hp1 .neumann φ n z
      ((mul_eq_zero.mp (hprod z hz)).resolve_left hD) hmem
  by_cases hLR : L = R
  · have hD := canonicalPeriodOneBoundaryRoots_eq_of_collapsed_gap hp hp1 .dirichlet φ.val φ.property n hLR
    have hN := canonicalPeriodOneBoundaryRoots_eq_of_collapsed_gap hp hp1 .neumann φ.val φ.property n hLR
    exact Or.inl ⟨hD,hN.trans hLR⟩
  rcases he with h | h
  · exact Or.inl ⟨h,hother R (Or.inr rfl) (by simpa only [h] using hLR)⟩
  · exact Or.inr ⟨h,hother L (Or.inl rfl) (by intro he; exact hLR (he.symm.trans h))⟩

/-- The actual difference of Dirichlet and Neumann roots, in the original coefficient space. -/
def sourceSignedGapSequence (hp : p ≠ ⊤) (hp1 : 1 < p) (φ : CoeffPair p) : Coeff p :=
  sourceBoundaryDisplacement hp hp1 .dirichlet φ - sourceBoundaryDisplacement hp hp1 .neumann φ

@[simp] theorem sourceSignedGapSequence_apply (hp : p ≠ ⊤) (hp1 : 1 < p)
    (φ : CoeffPair p) (n : ℤ) :
    sourceSignedGapSequence hp hp1 φ n = canonicalPeriodOneBoundaryRoots hp hp1 .dirichlet φ n -
      canonicalPeriodOneBoundaryRoots hp hp1 .neumann φ n := by
  simp [sourceSignedGapSequence]

/-- On the symmetric slice the square of each signed boundary difference is the actual squared gap. -/
theorem sourceSignedGapSequence_sq_of_reflection_fixed (hp : p ≠ ⊤) (hp1 : 1 < p)
    (φ : realTypeSourceSubmodule p) (hφ : realSourceSpatialReflection φ = φ) (n : ℤ) :
    (sourceSignedGapSequence hp hp1 φ.val n)^2 =
      (canonicalPeriodicGap hp hp1 (periodOnePotential φ.val) (periodOnePotential_mem _) n)^2 := by
  rcases sourceBoundaryRoots_opposite_endpoints_of_reflection_fixed hp hp1 φ hφ n with h | h
  · rw [sourceSignedGapSequence_apply,h.1,h.2]
    simp only [canonicalPeriodicGap]
    ring
  · rw [sourceSignedGapSequence_apply,h.1,h.2]
    rfl

/-- The signed boundary difference is analytic in the full coefficient norm on one complex
neighborhood of the entire real-type locus. -/
theorem exists_sourceSignedGapSequence_analytic_common_domain (hp : p ≠ ⊤) (hp1 : 1 < p) :
    ∃ W : Set (CoeffPair p), IsOpen W ∧ realTypeSourceLocus p ⊆ W ∧
      AnalyticOnNhd ℂ (sourceSignedGapSequence hp hp1) W := by
  obtain ⟨W,hW,hreal,hseq⟩ := exists_sourceBoundaryDisplacement_analytic_common_domain hp hp1
  exact ⟨W,hW,hreal,fun φ hφ => (hseq .dirichlet φ hφ).sub (hseq .neumann φ hφ)⟩

/-- Every signed boundary difference is real at real-type sources. -/
theorem sourceSignedGapSequence_im_eq_zero (hp : p ≠ ⊤) (hp1 : 1 < p)
    (φ : realTypeSourceSubmodule p) (n : ℤ) :
    (sourceSignedGapSequence hp hp1 φ.val n).im = 0 := by
  simp only [sourceSignedGapSequence_apply,sub_im,
    canonicalPeriodOneBoundaryRoots_im_eq_zero hp hp1 .dirichlet φ.val φ.property,
    canonicalPeriodOneBoundaryRoots_im_eq_zero hp hp1 .neumann φ.val φ.property,sub_self]

/-- The absolute signed difference on the symmetric slice is precisely the indexed periodic gap length. -/
theorem abs_sourceSignedGapSequence_re_of_reflection_fixed (hp : p ≠ ⊤) (hp1 : 1 < p)
    (φ : realTypeSourceSubmodule p) (hφ : realSourceSpatialReflection φ = φ) (n : ℤ) :
    |(sourceSignedGapSequence hp hp1 φ.val n).re| =
      (canonicalPeriodicGap hp hp1 (periodOnePotential φ.val) (periodOnePotential_mem _) n).re := by
  have hm := canonicalPeriodOneBoundaryRoots_mem_gap hp hp1 .dirichlet φ.val φ.property n
  have hle := sub_nonneg.mpr (hm.1.trans hm.2)
  rcases sourceBoundaryRoots_opposite_endpoints_of_reflection_fixed hp hp1 φ hφ n with h | h
  · rw [sourceSignedGapSequence_apply,h.1,h.2]
    simp only [sub_re,canonicalPeriodicGap]
    rw [abs_sub_comm,abs_of_nonneg hle]
  · rw [sourceSignedGapSequence_apply,h.1,h.2]
    simp only [sub_re,canonicalPeriodicGap]
    exact abs_of_nonneg hle

end NLS.ZakharovShabat
