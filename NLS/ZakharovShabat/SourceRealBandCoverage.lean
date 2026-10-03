import NLS.ZakharovShabat.SourceAbelianBandTransfer
import Mathlib.Data.Int.LeastGreatest

/-! # The spectral bands exhaust the real cut complement

The bounded displacement of the canonical endpoints from `pi * n`
provides a greatest gap to the left of every real point off the cuts.
-/
noncomputable section
open Set Complex NLS.ComplexAnalysis
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- Every real point off all cuts belongs to a band between two
consecutive gaps. This includes the tails in both spectral directions. -/
theorem exists_sourceRealBand_of_mem_rootDomain
    (hp : p ≠ ⊤) (hp1 : 1 < p) (φ : CoeffPair p)
    (hφ : IsRealType (CoeffPair.toMax p φ)) (x : ℝ)
    (hx : (x : ℂ) ∈ sourceCanonicalRootDomain hp hp1 φ) :
    ∃ n : ℤ, x ∈ sourceRealBand hp hp1 φ n := by
  let R := canonicalPeriodicRight hp hp1 (periodOnePotential φ) (periodOnePotential_mem φ)
  let d := canonicalPeriodicRightDisplacement hp hp1 (periodOnePotential φ) (periodOnePotential_mem φ)
  have hb (n : ℤ) : |(R n).re-Real.pi*n| ≤ ‖d‖ := by
    have h := (abs_re_le_norm (d n)).trans
      (lp.norm_apply_le_norm (zero_lt_one.trans hp1).ne' d n)
    simpa [d,R] using h
  have hne : ∃ n : ℤ, (R n).re < x := by
    obtain ⟨n,hn⟩ := exists_int_lt ((x-‖d‖)/Real.pi)
    refine ⟨n,?_⟩
    have hmul := (lt_div_iff₀ Real.pi_pos).mp hn
    have := (abs_le.mp (hb n)).2
    nlinarith
  have hbounded : ∃ k : ℤ, ∀ n : ℤ, (R n).re < x → n ≤ k := by
    obtain ⟨k,hk⟩ := exists_int_gt ((x+‖d‖)/Real.pi)
    refine ⟨k,?_⟩
    intro n hn
    have hmul := (div_lt_iff₀ Real.pi_pos).mp hk
    have hlow := (abs_le.mp (hb n)).1
    have hnk : (n : ℝ) < k := by nlinarith [Real.pi_pos]
    exact (Int.cast_lt.mp hnk).le
  obtain ⟨n,hn,hmax⟩ := Int.exists_greatest_of_bdd hbounded hne
  refine ⟨n,hn,?_⟩
  have hnext : x ≤ (R (n+1)).re := by
    by_contra h
    have := hmax (n+1) (lt_of_not_ge h)
    omega
  by_contra h
  exact hx (n+1) (sourcePeriodicSegment_mem_of_realIcc hp hp1 φ hφ (n+1) x
    ⟨le_of_not_gt h,hnext⟩)

/-- The complete complex cut complement is covered by the half-planes
and the full vertical band strips. -/
theorem sourceCanonicalRootDomain_eq_halfPlanes_union_bandStrips
    (hp : p ≠ ⊤) (hp1 : 1 < p) (φ : CoeffPair p)
    (hφ : IsRealType (CoeffPair.toMax p φ)) :
    sourceCanonicalRootDomain hp hp1 φ =
      (sourceAbelianHalfPlane true ∪ sourceAbelianHalfPlane false) ∪
        ⋃ n : ℤ, sourceRealBandStrip hp hp1 φ n := by
  ext z
  constructor
  · intro hz
    by_cases hu : 0 < z.im
    · exact Or.inl (Or.inl hu)
    by_cases hl : z.im < 0
    · exact Or.inl (Or.inr hl)
    have hi : z.im = 0 := le_antisymm (le_of_not_gt hu) (le_of_not_gt hl)
    have he : z = (z.re : ℂ) := Complex.ext rfl hi
    obtain ⟨n,hn⟩ := exists_sourceRealBand_of_mem_rootDomain hp hp1 φ hφ z.re (by rwa [← he])
    exact Or.inr (mem_iUnion.mpr ⟨n,hn⟩)
  · rintro ((hu | hl) | hs)
    · exact sourceAbelianHalfPlane_subset_rootDomain hp hp1 φ hφ true hu
    · exact sourceAbelianHalfPlane_subset_rootDomain hp hp1 φ hφ false hl
    · obtain ⟨n,hn⟩ := mem_iUnion.mp hs
      exact sourceRealBandStrip_subset_rootDomain hp hp1 φ hφ n hn

end NLS.ZakharovShabat
