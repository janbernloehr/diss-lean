import NLS.ZakharovShabat.PeriodicEndpointGlobalMultiplicity
import NLS.ZakharovShabat.CanonicalPeriodicGapOrder

/-! # Exact multiplicity inside a real canonical periodic gap

Strict separation of distinct real gaps reduces the full original
algebraic multiplicity to the two actual endpoint occurrences of the
selected gap. This includes all central indices and collapsed gaps.
-/
noncomputable section
set_option autoImplicit false
open Set Complex NLS.ComplexAnalysis
open scoped ENNReal Classical
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

theorem periodicAlgebraicMultiplicity_eq_real_gap_endpoints
    (hp : p ≠ ⊤) (hp1 : 1 < p) (φ : PairSpace p)
    (heven : φ ∈ pairParitySubspace 0) (hreal : IsRealType φ)
    (n : ℤ) (x : ℝ)
    (hx : x ∈ Icc (canonicalPeriodicLeft hp hp1 φ heven n).re
      (canonicalPeriodicRight hp hp1 φ heven n).re) :
    periodicAlgebraicMultiplicity hp φ (x : ℂ) =
      (if (canonicalPeriodicLeft hp hp1 φ heven n).re = x then 1 else 0)+
      (if (canonicalPeriodicRight hp hp1 φ heven n).re = x then 1 else 0) := by
  let l := canonicalPeriodicLeft hp hp1 φ heven
  let r := canonicalPeriodicRight hp hp1 φ heven
  have him := canonicalPeriodicEndpoints_im_eq_zero_of_realType hp hp1 φ heven hreal
  have hz (m : ℤ) (hm : m ≠ n) : ({l m,r m} : Multiset ℂ).count (x : ℂ) = 0 := by
    apply Multiset.count_eq_zero.mpr
    intro hmem
    have he : l m = (x : ℂ) ∨ r m = (x : ℂ) := by
      simpa only [Multiset.insert_eq_cons,Multiset.mem_cons,Multiset.mem_singleton,eq_comm] using hmem
    have hwithin : (l m).re ≤ x ∧ x ≤ (r m).re := by
      have hle := re_le_of_complexLexLE ((canonicalPeriodicEndpoints_spec hp hp1 φ heven).2.1 m)
      change (l m).re ≤ (r m).re at hle
      rcases he with h | h
      · have hr : (l m).re = x := congrArg Complex.re h
        exact ⟨hr.le,hr.symm.le.trans hle⟩
      · have hr : (r m).re = x := congrArg Complex.re h
        exact ⟨hle.trans hr.le,hr.symm.le⟩
    rcases lt_or_gt_of_ne hm with h | h
    · have hs := canonicalPeriodicRight_re_lt_left_of_lt hp hp1 φ heven hreal h
      exact hs.not_ge (hx.1.trans hwithin.2)
    · have hs := canonicalPeriodicRight_re_lt_left_of_lt hp hp1 φ heven hreal h
      exact hs.not_ge (hwithin.1.trans hx.2)
  have hg := (canonicalPeriodicEndpoints_spec hp hp1 φ heven).1.global_multiplicity (x : ℂ)
  change (∑ᶠ m : ℤ, ({l m,r m} : Multiset ℂ).count (x : ℂ)) = _ at hg
  rw [finsum_eq_single _ n hz] at hg
  have hl : l n = (x : ℂ) ↔ (l n).re = x := by
    constructor
    · intro h; exact congrArg Complex.re h
    · intro h; exact Complex.ext h (him n).1
  have hr : r n = (x : ℂ) ↔ (r n).re = x := by
    constructor
    · intro h; exact congrArg Complex.re h
    · intro h; exact Complex.ext h (him n).2
  have hl' : (x : ℂ) = l n ↔ (l n).re = x := eq_comm.trans hl
  have hr' : (x : ℂ) = r n ↔ (r n).re = x := eq_comm.trans hr
  simpa only [Multiset.insert_eq_cons,Multiset.count_cons,Multiset.count_singleton,hl',hr',Nat.add_comm] using hg.symm

end NLS.ZakharovShabat
