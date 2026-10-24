import NLS.ZakharovShabat.SourceRealBandCoverage
import NLS.ZakharovShabat.RealGapArcoshIntegral

/-! # The real Floquet band set and the canonical open gaps

The discriminant criterion is identified with the complement of the
actual open periodic gaps, including their endpoints and collapsed gaps.
The identification with the whole-line operator spectrum and its
absolute continuity require further operator-theoretic work.
-/
noncomputable section
set_option autoImplicit false
open Set Complex
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The real points outside all open canonical periodic gaps. -/
def sourceFloquetBandSet (hp : p ≠ ⊤) (hp1 : 1 < p) (φ : CoeffPair p) : Set ℝ :=
  (⋃ n : ℤ, Ioo
    (canonicalPeriodicLeft hp hp1 (periodOnePotential φ) (periodOnePotential_mem φ) n).re
    (canonicalPeriodicRight hp hp1 (periodOnePotential φ) (periodOnePotential_mem φ) n).re)ᶜ

/-- Strictly inside a gap the real discriminant has modulus greater than two. -/
theorem two_lt_abs_sourceDiscriminant_re_of_mem_openGap
    (hp : p ≠ ⊤) (hp1 : 1 < p) (φ : CoeffPair p)
    (hφ : IsRealType (CoeffPair.toMax p φ)) (n : ℤ) (x : ℝ)
    (hx : x ∈ Ioo
      (canonicalPeriodicLeft hp hp1 (periodOnePotential φ) (periodOnePotential_mem φ) n).re
      (canonicalPeriodicRight hp hp1 (periodOnePotential φ) (periodOnePotential_mem φ) n).re) :
    2 < |(canonicalDiscriminant hp (periodOnePotential φ) (x : ℂ)).re| := by
  obtain ⟨_,_,_,_,_,hgt⟩ := realGapHalfDiscriminant_arcosh_gap_data hp hp1
    (periodOnePotential φ) (periodOnePotential_mem φ) (isRealType_periodOnePotential φ hφ) n
  have h := hgt x hx
  dsimp only [realGapHalfDiscriminant] at h
  split_ifs at h
  · exact (by linarith : 2 < (canonicalDiscriminant hp (periodOnePotential φ) (x : ℂ)).re).trans_le (le_abs_self _)
  · exact (by linarith : 2 < -(canonicalDiscriminant hp (periodOnePotential φ) (x : ℂ)).re).trans_le (neg_le_abs _)

/-- The full closed band criterion for the actual canonical discriminant. -/
theorem mem_sourceFloquetBandSet_iff_abs_discriminant_le_two
    (hp : p ≠ ⊤) (hp1 : 1 < p) (φ : CoeffPair p)
    (hφ : IsRealType (CoeffPair.toMax p φ)) (x : ℝ) :
    x ∈ sourceFloquetBandSet hp hp1 φ ↔
      |(canonicalDiscriminant hp (periodOnePotential φ) (x : ℂ)).re| ≤ 2 := by
  have hmem : x ∈ sourceFloquetBandSet hp hp1 φ ↔ ∀ n : ℤ, x ∉ Ioo
      (canonicalPeriodicLeft hp hp1 (periodOnePotential φ) (periodOnePotential_mem φ) n).re
      (canonicalPeriodicRight hp hp1 (periodOnePotential φ) (periodOnePotential_mem φ) n).re := by
    simp only [sourceFloquetBandSet,mem_compl_iff,mem_iUnion,not_exists]
  rw [hmem]
  constructor
  · intro hx
    by_cases hroot : (x : ℂ) ∈ sourceCanonicalRootDomain hp hp1 φ
    · obtain ⟨n,hn⟩ := exists_sourceRealBand_of_mem_rootDomain hp hp1 φ hφ x hroot
      have h := sourceDiscriminant_realBand_sq_lt_four hp hp1 φ hφ n x hn
      rw [abs_le]
      constructor <;> nlinarith
    · simp only [sourceCanonicalRootDomain,mem_ofPred_eq,not_forall,not_not] at hroot
      obtain ⟨n,hn⟩ := hroot
      have hI := sourcePeriodicSegment_re_mem_Icc hp hp1 φ n (x : ℂ) hn
      change (canonicalPeriodicLeft hp hp1 (periodOnePotential φ) (periodOnePotential_mem φ) n).re ≤ x ∧
        x ≤ (canonicalPeriodicRight hp hp1 (periodOnePotential φ) (periodOnePotential_mem φ) n).re at hI
      have hend := realGapHalfDiscriminant_arcosh_gap_data hp hp1
        (periodOnePotential φ) (periodOnePotential_mem φ) (isRealType_periodOnePotential φ hφ) n
      have hg : realGapHalfDiscriminant hp (periodOnePotential φ) n x = 1 := by
        rcases eq_or_lt_of_le hI.1 with he | he
        · rw [← he]; exact hend.2.2.2.1
        · have hright : x = (canonicalPeriodicRight hp hp1 (periodOnePotential φ) (periodOnePotential_mem φ) n).re :=
            le_antisymm hI.2 (le_of_not_gt (fun h => hx n ⟨he,h⟩))
          rw [hright]; exact hend.2.2.2.2.1
      dsimp only [realGapHalfDiscriminant] at hg
      rw [abs_le]
      split_ifs at hg <;> constructor <;> linarith
  · intro hd n hn
    exact (two_lt_abs_sourceDiscriminant_re_of_mem_openGap hp hp1 φ hφ n x hn).not_ge hd

/-- The band set is closed, including every finite gap endpoint. -/
theorem isClosed_sourceFloquetBandSet (hp : p ≠ ⊤) (hp1 : 1 < p) (φ : CoeffPair p) :
    IsClosed (sourceFloquetBandSet hp hp1 φ) :=
  (isOpen_iUnion fun _ => isOpen_Ioo).isClosed_compl

end NLS.ZakharovShabat
