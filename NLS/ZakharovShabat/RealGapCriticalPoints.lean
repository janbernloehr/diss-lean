import NLS.ZakharovShabat.CanonicalPeriodicGapCritical

/-!
# One ordered critical witness in each real periodic gap

Choose a critical point in each canonical real gap. Strict gap separation
makes these witnesses strictly increasing and distinct. Every central
block lies inside its corresponding critical-counting disc.
-/

noncomputable section
open Set Complex Metric
open NLS.ComplexAnalysis
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- A real critical point selected from each canonical periodic gap. -/
def realGapCriticalPoint (hp : p ≠ ⊤) (hp1 : 1 < p) (φ : PairSpace p)
    (heven : φ ∈ pairParitySubspace 0) (hreal : IsRealType φ) (n : ℤ) : ℝ :=
  (exists_critical_mem_canonicalPeriodicGap hp hp1 φ heven hreal n).choose

/-- Each selected witness lies in its indexed gap and is an actual critical point. -/
theorem realGapCriticalPoint_spec (hp : p ≠ ⊤) (hp1 : 1 < p) (φ : PairSpace p)
    (heven : φ ∈ pairParitySubspace 0) (hreal : IsRealType φ) (n : ℤ) :
    realGapCriticalPoint hp hp1 φ heven hreal n ∈
      Icc (canonicalPeriodicLeft hp hp1 φ heven n).re (canonicalPeriodicRight hp hp1 φ heven n).re ∧
      deriv (canonicalDiscriminant hp φ) (realGapCriticalPoint hp hp1 φ heven hreal n : ℂ) = 0 :=
  (exists_critical_mem_canonicalPeriodicGap hp hp1 φ heven hreal n).choose_spec

/-- Selected gap critical points are strictly increasing because different gaps are strictly separated. -/
theorem strictMono_realGapCriticalPoint (hp : p ≠ ⊤) (hp1 : 1 < p) (φ : PairSpace p)
    (heven : φ ∈ pairParitySubspace 0) (hreal : IsRealType φ) :
    StrictMono (realGapCriticalPoint hp hp1 φ heven hreal) := by
  intro i j hij
  exact ((realGapCriticalPoint_spec hp hp1 φ heven hreal i).1.2.trans_lt
    (canonicalPeriodicRight_re_lt_left_of_lt hp hp1 φ heven hreal hij)).trans_le
    (realGapCriticalPoint_spec hp hp1 φ heven hreal j).1.1

/-- The complex-valued gap witness sequence has no repeated values. -/
theorem realGapCriticalPoint_complex_injective (hp : p ≠ ⊤) (hp1 : 1 < p) (φ : PairSpace p)
    (heven : φ ∈ pairParitySubspace 0) (hreal : IsRealType φ) :
    Function.Injective (fun n => (realGapCriticalPoint hp hp1 φ heven hreal n : ℂ)) :=
  Complex.ofReal_injective.comp (strictMono_realGapCriticalPoint hp hp1 φ heven hreal).injective

/-- The witnesses in a central block lie strictly inside its critical-counting disc. -/
theorem norm_realGapCriticalPoint_lt (hp : p ≠ ⊤) (hp1 : 1 < p) (φ : PairSpace p)
    (heven : φ ∈ pairParitySubspace 0) (hreal : IsRealType φ) (K : ℕ)
    (hK : canonicalPeriodicCutoff hp hp1 φ heven ≤ K) (n : ℤ) (hn : n.natAbs ≤ K) :
    ‖(realGapCriticalPoint hp hp1 φ heven hreal n : ℂ)‖ < centralCircleRadius K := by
  have hc := (canonicalPeriodicEndpoints_spec hp hp1 φ heven).1.central_at_larger_cutoff K hK
  have hx := ((mem_centralPeriodicSpectrum hp φ K _).mp
    ((hc.root_iff _).mp ⟨n,hn,Or.inl rfl⟩)).2.1
  have hy := ((mem_centralPeriodicSpectrum hp φ K _).mp
    ((hc.root_iff _).mp ⟨n,hn,Or.inr rfl⟩)).2.1
  have hb := (realGapCriticalPoint_spec hp hp1 φ heven hreal n).1
  rw [Complex.norm_real, Real.norm_eq_abs, abs_lt]
  exact ⟨(abs_lt.mp hx).1.trans_le hb.1,hb.2.trans_lt (abs_lt.mp hy).2⟩

/-- Every selected central witness belongs to the full central critical multiset. -/
theorem realGapCriticalPoint_mem_centralRoots (hp : p ≠ ⊤) (hp1 : 1 < p) (φ : PairSpace p)
    (heven : φ ∈ pairParitySubspace 0) (hreal : IsRealType φ) (K : ℕ)
    (hK : canonicalPeriodicCutoff hp hp1 φ heven ≤ K) (n : ℤ) (hn : n.natAbs ≤ K) :
    (realGapCriticalPoint hp hp1 φ heven hreal n : ℂ) ∈ centralCriticalRoots hp hp1 φ heven K := by
  apply (mem_centralCriticalRoots hp hp1 φ heven K _).mpr
  exact ⟨by simpa only [mem_closedBall,dist_zero_right] using
    (norm_realGapCriticalPoint_lt hp hp1 φ heven hreal K hK n hn).le,
    (realGapCriticalPoint_spec hp hp1 φ heven hreal n).2⟩

end NLS.ZakharovShabat
