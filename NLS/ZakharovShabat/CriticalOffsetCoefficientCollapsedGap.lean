import NLS.ZakharovShabat.CriticalOffsetCoefficientOpenGap
import NLS.ZakharovShabat.FiniteDiscriminant

/-!
# A collapsed real periodic pair has exactly two spectral occurrences

The complete canonical endpoint labeling records original algebraic
multiplicity. At a real-type potential, different indexed gaps are
strictly disjoint. Thus a collapsed pair contributes exactly its two
slots, even among the central indices.
-/

noncomputable section
open Set Complex
open NLS.ComplexAnalysis
open scoped ENNReal Classical
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- At a real-type potential a collapsed canonical periodic pair has
original algebraic multiplicity exactly two, including centrally. -/
theorem canonicalPeriodicMultiplicity_eq_two_of_collapsed_real_gap
    (hp : p ≠ ⊤) (hp1 : 1 < p) (φ : PairSpace p)
    (heven : φ ∈ pairParitySubspace 0) (hreal : IsRealType φ) (n : ℤ)
    (hcollapsed : canonicalPeriodicLeft hp hp1 φ heven n =
      canonicalPeriodicRight hp hp1 φ heven n) :
    periodicAlgebraicMultiplicity hp φ
      (canonicalPeriodicLeft hp hp1 φ heven n) = 2 := by
  let L := canonicalPeriodicLeft hp hp1 φ heven
  let R := canonicalPeriodicRight hp hp1 φ heven
  let a := L n
  let C := canonicalPeriodicCutoff hp hp1 φ heven
  let K := max C n.natAbs
  have hlabel := (canonicalPeriodicEndpoints_spec hp hp1 φ heven).1
  have hcentral := hlabel.central_at_larger_cutoff K (le_max_left _ _)
  have hnK : n ∈ Finset.Icc (-(K : ℤ)) (K : ℤ) := by
    simp only [Finset.mem_Icc]
    have hnat : n.natAbs ≤ K := le_max_right C n.natAbs
    omega
  have hroot : a ∈ centralPeriodicSpectrum hp φ K :=
    (hcentral.root_iff a).mp ⟨n,by omega,Or.inl rfl⟩
  have haGap : a.re ∈ Icc (L n).re (R n).re := by
    change (L n).re ∈ Icc (L n).re (R n).re
    exact ⟨le_rfl,re_le_of_complexLexLE
      ((canonicalPeriodicEndpoints_spec hp hp1 φ heven).2.1 n)⟩
  have hzero (m : ℤ) (hmn : m ≠ n) :
      ({L m,R m} : Multiset ℂ).count a = 0 := by
    have hgap : Disjoint (Icc (L n).re (R n).re) (Icc (L m).re (R m).re) :=
      canonicalPeriodicGaps_disjoint hp hp1 φ heven hreal (Ne.symm hmn)
    have hle : (L m).re ≤ (R m).re := re_le_of_complexLexLE
      ((canonicalPeriodicEndpoints_spec hp hp1 φ heven).2.1 m)
    have hL : L m ≠ a := by
      intro he
      have hm : a.re ∈ Icc (L m).re (R m).re := by
        rw [← he]
        exact ⟨le_rfl,hle⟩
      exact Set.disjoint_left.mp hgap haGap hm
    have hR : R m ≠ a := by
      intro he
      have hm : a.re ∈ Icc (L m).re (R m).re := by
        rw [← he]
        exact ⟨hle,le_rfl⟩
      exact Set.disjoint_left.mp hgap haGap hm
    apply Multiset.count_eq_zero.mpr
    intro hm
    have hm' : a = L m ∨ a = R m := by
      simpa only [Multiset.insert_eq_cons, Multiset.mem_cons, Multiset.mem_singleton]
        using hm
    rcases hm' with he | he
    · exact hL he.symm
    · exact hR he.symm
  have hsum :
      (∑ m ∈ Finset.Icc (-(K : ℤ)) (K : ℤ),
        ({L m,R m} : Multiset ℂ).count a) =
          ({L n,R n} : Multiset ℂ).count a := by
    apply Finset.sum_eq_single n
    · intro m hm hmn
      exact hzero m hmn
    · intro hn
      exact False.elim (hn hnK)
  have hcount := hcentral.count_eq a
  rw [hsum, if_pos hroot] at hcount
  have hpair : ({L n,R n} : Multiset ℂ).count a = 2 := by
    change ({canonicalPeriodicLeft hp hp1 φ heven n,
      canonicalPeriodicRight hp hp1 φ heven n} : Multiset ℂ).count
        (canonicalPeriodicLeft hp hp1 φ heven n) = 2
    rw [← hcollapsed]
    simp
  exact hcount.symm.trans hpair

/-- Removing a collapsed pair leaves a nonzero periodic product at
its common root. Exact multiplicity two rules out another zero in
the remaining factor. -/
theorem canonicalDeletedPeriodicProduct_ne_zero_at_collapsed_real_gap
    (hp : p ≠ ⊤) (hp1 : 1 < p) (φ : PairSpace p)
    (heven : φ ∈ pairParitySubspace 0) (hreal : IsRealType φ) (n : ℤ)
    (hcollapsed : canonicalPeriodicLeft hp hp1 φ heven n =
      canonicalPeriodicRight hp hp1 φ heven n) :
    canonicalDeletedPeriodicProduct hp hp1 φ heven n
      (canonicalPeriodicLeft hp hp1 φ heven n) ≠ 0 := by
  let a := canonicalPeriodicLeft hp hp1 φ heven n
  let P := canonicalDeletedPeriodicProduct hp hp1 φ heven n
  have hmult := canonicalPeriodicMultiplicity_eq_two_of_collapsed_real_gap
    hp hp1 φ heven hreal n hcollapsed
  have horder : analyticOrderAt
      (fun z : ℂ => (canonicalDiscriminant hp φ z)^2-4) a = 2 := by
    rw [analyticOrderAt_canonicalDiscriminant_sq_sub_four hp hp1 φ heven a]
    simpa [a] using congrArg (fun k : ℕ => (k : ℕ∞)) hmult
  have hfun : (fun z : ℂ => (canonicalDiscriminant hp φ z)^2-4) =
      (fun z : ℂ => -4*(a-z)*(a-z)) * P := by
    funext z
    change (canonicalDiscriminant hp φ z)^2-4 =
      (-4*(a-z)*(a-z))*P z
    rw [canonicalDiscriminant_sq_sub_four_eq_pair_mul hp hp1 φ heven n z]
    rw [← hcollapsed]
  rw [hfun] at horder
  have hfactor : AnalyticAt ℂ (fun z : ℂ => -4*(a-z)*(a-z)) a := by fun_prop
  have hP : AnalyticAt ℂ P a :=
    analyticOnNhd_canonicalDeletedPeriodicProduct hp hp1 φ heven n a (mem_univ _)
  rw [analyticOrderAt_mul hfactor hP] at horder
  have hfactorOrder : analyticOrderAt (fun z : ℂ => -4*(a-z)*(a-z)) a = 2 := by
    change analyticOrderAt ((fun z : ℂ => -4*(a-z)) *
      (fun z : ℂ => a-z)) a = 2
    rw [analyticOrderAt_mul (by fun_prop) (by fun_prop)]
    change analyticOrderAt ((fun _ : ℂ => (-4 : ℂ)) *
      (fun z : ℂ => a-z)) a + analyticOrderAt (fun z : ℂ => a-z) a = 2
    rw [analyticOrderAt_mul (by fun_prop) (by fun_prop),
      NLS.ComplexAnalysis.analyticOrderAt_const_sub]
    have hconst : analyticOrderAt (fun _ : ℂ => (-4 : ℂ)) a = 0 :=
      analyticOrderAt_eq_zero.mpr (Or.inr (by norm_num))
    rw [hconst]
    norm_num
  rw [hfactorOrder] at horder
  have hPorder : analyticOrderAt P a = 0 := by
    simpa using horder
  exact ((analyticOrderAt_eq_zero.mp hPorder).resolve_left (not_not.mpr hP))

/-- At a collapsed real gap the critical root is the common endpoint,
so the offset coefficient is twice the nonzero deleted product. -/
theorem canonicalCriticalOffsetCoefficient_ne_zero_of_collapsed_real_gap
    (hp : p ≠ ⊤) (hp1 : 1 < p) (φ : PairSpace p)
    (heven : φ ∈ pairParitySubspace 0) (hreal : IsRealType φ) (n : ℤ)
    (hcollapsed : canonicalPeriodicLeft hp hp1 φ heven n =
      canonicalPeriodicRight hp hp1 φ heven n) :
    canonicalCriticalOffsetCoefficient hp hp1 φ heven n ≠ 0 := by
  have hc := canonicalCriticalPoints_eq_of_collapsed_gap
    hp hp1 φ heven hreal n hcollapsed
  have hmid : canonicalPeriodicMidpoint hp hp1 φ heven n =
      canonicalPeriodicLeft hp hp1 φ heven n := by
    unfold canonicalPeriodicMidpoint
    rw [← hcollapsed]
    ring
  have hcoef : canonicalCriticalOffsetCoefficient hp hp1 φ heven n =
      2*canonicalDeletedPeriodicProduct hp hp1 φ heven n
        (canonicalPeriodicLeft hp hp1 φ heven n) := by
    simp [canonicalCriticalOffsetCoefficient, canonicalCriticalMidpointOffset_apply,
      hc, hmid]
  rw [hcoef]
  exact mul_ne_zero (by norm_num)
    (canonicalDeletedPeriodicProduct_ne_zero_at_collapsed_real_gap
      hp hp1 φ heven hreal n hcollapsed)

/-- The midpoint coefficient never vanishes at any index of a
real-type potential, whether its periodic gap is open or collapsed. -/
theorem canonicalCriticalOffsetCoefficient_ne_zero_of_realType
    (hp : p ≠ ⊤) (hp1 : 1 < p) (φ : PairSpace p)
    (heven : φ ∈ pairParitySubspace 0) (hreal : IsRealType φ) (n : ℤ) :
    canonicalCriticalOffsetCoefficient hp hp1 φ heven n ≠ 0 := by
  have hle : (canonicalPeriodicLeft hp hp1 φ heven n).re ≤
      (canonicalPeriodicRight hp hp1 φ heven n).re :=
    re_le_of_complexLexLE ((canonicalPeriodicEndpoints_spec hp hp1 φ heven).2.1 n)
  rcases lt_or_eq_of_le hle with hlt | heq
  · exact canonicalCriticalOffsetCoefficient_ne_zero_of_open_real_gap
      hp hp1 φ heven hreal n hlt
  · have him := canonicalPeriodicEndpoints_im_eq_zero_of_realType
      hp hp1 φ heven hreal n
    have hcollapsed : canonicalPeriodicLeft hp hp1 φ heven n =
        canonicalPeriodicRight hp hp1 φ heven n :=
      Complex.ext heq (him.1.trans him.2.symm)
    exact canonicalCriticalOffsetCoefficient_ne_zero_of_collapsed_real_gap
      hp hp1 φ heven hreal n hcollapsed

/-- At every real-type potential, all indexed critical roots satisfy
the exact squared-gap offset formula, including collapsed gaps. -/
theorem canonicalCriticalPoints_midpoint_gap_sq_of_realType
    (hp : p ≠ ⊤) (hp1 : 1 < p) (φ : PairSpace p)
    (heven : φ ∈ pairParitySubspace 0) (hreal : IsRealType φ) (n : ℤ) :
    canonicalCriticalPoints hp hp1 φ heven n -
        canonicalPeriodicMidpoint hp hp1 φ heven n =
      (canonicalPeriodicGap hp hp1 φ heven n)^2 *
        canonicalCriticalGapQuotient hp hp1 φ heven n := by
  simpa only [canonicalCriticalMidpointOffset_apply, canonicalCriticalGapQuotient] using
    canonicalCriticalMidpointOffset_eq_gap_sq_mul_quotient hp hp1 φ heven n
      (canonicalCriticalOffsetCoefficient_ne_zero_of_realType
        hp hp1 φ heven hreal n)

end NLS.ZakharovShabat
