import NLS.ZakharovShabat.RealGapCriticalIdentification

/-!
# Global interlacing of canonical critical and periodic coordinates

Every canonical critical coordinate belongs to its indexed periodic gap.
Strict separation and exhaustive critical labeling give uniqueness in
each gap, strict interlacing for open gaps, and equality at collapsed gaps.
-/

noncomputable section
open Set Complex
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- Any critical point in an indexed real gap equals that index's canonical critical point. -/
theorem critical_eq_canonicalCriticalPoints_of_mem_gap (hp : p ≠ ⊤) (hp1 : 1 < p) (φ : PairSpace p)
    (heven : φ ∈ pairParitySubspace 0) (hreal : IsRealType φ) (n : ℤ) (z : ℂ)
    (hz : deriv (canonicalDiscriminant hp φ) z = 0)
    (hgap : z.re ∈ Icc (canonicalPeriodicLeft hp hp1 φ heven n).re (canonicalPeriodicRight hp hp1 φ heven n).re) :
    z = canonicalCriticalPoints hp hp1 φ heven n := by
  obtain ⟨m,hm⟩ := (canonicalCriticalPoints_exhaustive hp hp1 φ heven z).mp hz
  have hmgap := canonicalCriticalPoints_mem_canonicalPeriodicGap hp hp1 φ heven hreal m
  by_cases hmn : m = n
  · simpa only [hmn] using hm.symm
  · have hd := canonicalPeriodicGaps_disjoint hp hp1 φ heven hreal hmn
    exact False.elim (Set.disjoint_left.mp hd hmgap (by rwa [hm]))

/-- Every canonical real gap contains exactly one critical point. -/
theorem existsUnique_critical_in_canonicalPeriodicGap (hp : p ≠ ⊤) (hp1 : 1 < p) (φ : PairSpace p)
    (heven : φ ∈ pairParitySubspace 0) (hreal : IsRealType φ) (n : ℤ) :
    ∃! z : ℂ, deriv (canonicalDiscriminant hp φ) z = 0 ∧
      z.re ∈ Icc (canonicalPeriodicLeft hp hp1 φ heven n).re (canonicalPeriodicRight hp hp1 φ heven n).re := by
  refine ⟨canonicalCriticalPoints hp hp1 φ heven n,
    ⟨canonicalCriticalPoints_is_critical hp hp1 φ heven n,
      canonicalCriticalPoints_mem_canonicalPeriodicGap hp hp1 φ heven hreal n⟩,?_⟩
  intro z hz
  exact critical_eq_canonicalCriticalPoints_of_mem_gap hp hp1 φ heven hreal n z hz.1 hz.2

/-- The canonical critical point is strictly inside every open canonical real gap. -/
theorem canonicalCriticalPoints_between_of_open_gap (hp : p ≠ ⊤) (hp1 : 1 < p) (φ : PairSpace p)
    (heven : φ ∈ pairParitySubspace 0) (hreal : IsRealType φ) (n : ℤ)
    (hlt : (canonicalPeriodicLeft hp hp1 φ heven n).re < (canonicalPeriodicRight hp hp1 φ heven n).re) :
    (canonicalCriticalPoints hp hp1 φ heven n).re ∈
      Ioo (canonicalPeriodicLeft hp hp1 φ heven n).re (canonicalPeriodicRight hp hp1 φ heven n).re := by
  obtain ⟨c,hc,hzero⟩ := exists_critical_between_canonicalPeriodicEndpoints hp hp1 φ heven hreal n hlt
  have he := critical_eq_canonicalCriticalPoints_of_mem_gap hp hp1 φ heven hreal n (c : ℂ) hzero
    ⟨hc.1.le,hc.2.le⟩
  rw [← he,Complex.ofReal_re]
  exact hc

/-- In a collapsed real gap the canonical critical coordinate is the common periodic endpoint. -/
theorem canonicalCriticalPoints_eq_of_collapsed_gap (hp : p ≠ ⊤) (hp1 : 1 < p) (φ : PairSpace p)
    (heven : φ ∈ pairParitySubspace 0) (hreal : IsRealType φ) (n : ℤ)
    (he : canonicalPeriodicLeft hp hp1 φ heven n = canonicalPeriodicRight hp hp1 φ heven n) :
    canonicalCriticalPoints hp hp1 φ heven n = canonicalPeriodicLeft hp hp1 φ heven n := by
  have hc := canonicalCriticalPoints_mem_canonicalPeriodicGap hp hp1 φ heven hreal n
  rw [← he] at hc
  exact Complex.ext (le_antisymm hc.2 hc.1)
    ((canonicalCriticalPoints_im_eq_zero hp hp1 φ heven hreal n).trans
      (canonicalPeriodicEndpoints_im_eq_zero_of_realType hp hp1 φ heven hreal n).1.symm)

/-- Every critical point belongs to exactly one indexed canonical real gap; there are no others. -/
theorem critical_mem_unique_canonicalPeriodicGap (hp : p ≠ ⊤) (hp1 : 1 < p) (φ : PairSpace p)
    (heven : φ ∈ pairParitySubspace 0) (hreal : IsRealType φ) (z : ℂ)
    (hz : deriv (canonicalDiscriminant hp φ) z = 0) :
    ∃! n : ℤ, z.re ∈ Icc (canonicalPeriodicLeft hp hp1 φ heven n).re (canonicalPeriodicRight hp hp1 φ heven n).re := by
  obtain ⟨n,rfl⟩ := (canonicalCriticalPoints_exhaustive hp hp1 φ heven z).mp hz
  refine ⟨n,canonicalCriticalPoints_mem_canonicalPeriodicGap hp hp1 φ heven hreal n,?_⟩
  intro m hm
  apply (canonicalCriticalPoints_injective_of_realType hp hp1 φ heven hreal)
  exact (critical_eq_canonicalCriticalPoints_of_mem_gap hp hp1 φ heven hreal m _ hz hm).symm

end NLS.ZakharovShabat
