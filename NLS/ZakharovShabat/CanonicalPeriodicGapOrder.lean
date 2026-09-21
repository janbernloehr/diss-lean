import NLS.ZakharovShabat.CanonicalPeriodicParity

/-!
# Strict separation of real canonical periodic gaps

Neighboring pairs have opposite discriminant levels. Their ordered real
endpoints therefore cannot meet. This separates every pair of distinct
indexed gaps, including gaps in the central cluster.
-/

noncomputable section
open Set Complex
open NLS.ComplexAnalysis
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- Consecutive canonical periodic gaps are strictly separated at real-type potentials. -/
theorem canonicalPeriodicRight_re_lt_next_left (hp : p ≠ ⊤) (hp1 : 1 < p)
    (φ : PairSpace p) (heven : φ ∈ pairParitySubspace 0) (hreal : IsRealType φ) (n : ℤ) :
    (canonicalPeriodicRight hp hp1 φ heven n).re < (canonicalPeriodicLeft hp hp1 φ heven (n+1)).re := by
  have hle := re_le_of_complexLexLE ((canonicalPeriodicEndpoints_spec hp hp1 φ heven).2.2 n (n+1) (by omega))
  apply lt_of_le_of_ne hle
  intro he
  have him := canonicalPeriodicEndpoints_im_eq_zero_of_realType hp hp1 φ heven hreal
  have hz : canonicalPeriodicRight hp hp1 φ heven n = canonicalPeriodicLeft hp hp1 φ heven (n+1) :=
    Complex.ext he ((him n).2.trans (him (n+1)).1.symm)
  have hl := (canonicalPeriodicEndpoints_discriminant_of_realType hp hp1 φ heven hreal n).2
  have hr := (canonicalPeriodicEndpoints_discriminant_of_realType hp hp1 φ heven hreal (n+1)).1
  have hlevels := hl.symm.trans ((congrArg (canonicalDiscriminant hp φ) hz).trans hr)
  by_cases hn : n % 2 = 0
  · have hn' : (n+1) % 2 ≠ 0 := by omega
    norm_num [hn,hn'] at hlevels
  · have hn' : (n+1) % 2 = 0 := by omega
    norm_num [hn,hn'] at hlevels

/-- Any two distinct indexed real gaps are strictly ordered by their indices. -/
theorem canonicalPeriodicRight_re_lt_left_of_lt (hp : p ≠ ⊤) (hp1 : 1 < p)
    (φ : PairSpace p) (heven : φ ∈ pairParitySubspace 0) (hreal : IsRealType φ)
    {i j : ℤ} (hij : i < j) :
    (canonicalPeriodicRight hp hp1 φ heven i).re < (canonicalPeriodicLeft hp hp1 φ heven j).re := by
  have hi := canonicalPeriodicRight_re_lt_next_left hp hp1 φ heven hreal i
  by_cases he : i+1 = j
  · simpa only [he] using hi
  · have hh : i+1 < j := by omega
    have hw := re_le_of_complexLexLE ((canonicalPeriodicEndpoints_spec hp hp1 φ heven).2.1 (i+1))
    have hc := re_le_of_complexLexLE ((canonicalPeriodicEndpoints_spec hp hp1 φ heven).2.2 (i+1) j hh)
    exact hi.trans_le (hw.trans hc)

/-- Closed canonical real gaps with different indices are disjoint, including collapsed gaps. -/
theorem canonicalPeriodicGaps_disjoint (hp : p ≠ ⊤) (hp1 : 1 < p)
    (φ : PairSpace p) (heven : φ ∈ pairParitySubspace 0) (hreal : IsRealType φ)
    {i j : ℤ} (hij : i ≠ j) :
    Disjoint (Icc (canonicalPeriodicLeft hp hp1 φ heven i).re (canonicalPeriodicRight hp hp1 φ heven i).re)
      (Icc (canonicalPeriodicLeft hp hp1 φ heven j).re (canonicalPeriodicRight hp hp1 φ heven j).re) := by
  apply Set.disjoint_left.mpr
  intro x hx hy
  rcases lt_or_gt_of_ne hij with h | h
  · exact (canonicalPeriodicRight_re_lt_left_of_lt hp hp1 φ heven hreal h).not_ge (hy.1.trans hx.2)
  · exact (canonicalPeriodicRight_re_lt_left_of_lt hp hp1 φ heven hreal h).not_ge (hx.1.trans hy.2)

end NLS.ZakharovShabat
