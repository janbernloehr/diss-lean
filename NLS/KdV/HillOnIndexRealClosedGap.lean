import NLS.KdV.HillOnIndexPhysicalPhaseSquare

/-! At REAL closed gaps the actual auxiliary Dirichlet divisor is the
collapsed endpoint. Both physical diagonal Cartesian factors vanish.
This real interlacing statement is not imposed on complex collapses. -/
noncomputable section
open Set Metric Complex Filter Topology NLS.ComplexAnalysis NLS.ZakharovShabat
open scoped ENNReal Classical
namespace NLS.KdV.HillProductEquationPatch

theorem frequency_gap_zero_of_real_original_gap_zero (P : HillProductEquationPatch) (n : ℕ+)
    (q : PeriodOneHminusOne) (hq : q ∈ P.source) (hr : IsRealPeriodOneHminusOne q)
    (hg : hillHminusCanonicalGapSquare n q = 0) :
    canonicalPeriodicGap (by norm_num) (by norm_num) (periodOnePotential (P.sourcePsi q)) (periodOnePotential_mem _) ((n:ℕ):ℤ) = 0 := by
  let τ := sourceStandardRootMidpoint (by norm_num) (by norm_num) (P.sourcePsi q) ((n:ℕ):ℤ)
  have hτD : τ ∈ ball (P.centers ((n:ℕ):ℤ):ℂ) (P.radii ((n:ℕ):ℤ)) := by
    rw [← P.discs_eq]
    exact P.isolating.gap (P.sourcePsi q) (P.image q hq).2 _ (sourcePeriodicMidpoint_mem_segment (by norm_num) (by norm_num) (P.sourcePsi q) _)
  have hτpos := P.abelianGapDisc_re_pos_of_real n q hq hr τ hτD
  have hτne : τ ≠ 0 := by intro he; rw [he,zero_re] at hτpos; exact lt_irrefl 0 hτpos
  have hprod := P.physicalOnIndexCartesian_product n q (P.real_mem_physicalDirichletSource q hq hr)
  rw [P.physicalOnIndexCartesian_product_eq_original_gap_square n q (P.real_mem_physicalDirichletSource q hq hr),hg] at hprod
  have hs := (mul_eq_zero.mp hprod.symm).resolve_left (mul_ne_zero (by norm_num) (pow_ne_zero 2 hτne))
  exact eq_zero_of_pow_eq_zero hs

theorem actual_frequency_eq_midpoint_of_real_closed_gap (P : HillProductEquationPatch) (n : ℕ+)
    (q : PeriodOneHminusOne) (hq : q ∈ P.source) (hr : IsRealPeriodOneHminusOne q)
    (hg : hillHminusCanonicalGapSquare n q = 0) :
    P.physicalDirichletFrequency ((n:ℕ):ℤ) q = sourceStandardRootMidpoint (by norm_num) (by norm_num) (P.sourcePsi q) ((n:ℕ):ℤ) := by
  let l := canonicalPeriodicLeft (by norm_num) (by norm_num) (periodOnePotential (P.sourcePsi q)) (periodOnePotential_mem _) ((n:ℕ):ℤ)
  let r := canonicalPeriodicRight (by norm_num) (by norm_num) (periodOnePotential (P.sourcePsi q)) (periodOnePotential_mem _) ((n:ℕ):ℤ)
  have hf : r-l = 0 := P.frequency_gap_zero_of_real_original_gap_zero n q hq hr hg
  have he : r = l := sub_eq_zero.mp hf
  let u : PeriodOneRealL2 := ⟨P.parent.parent.miuraBall.actionBall.lift q,
    P.parent.parent.miuraBall.actionBall.lift_real q (P.parent.subset (P.subset hq)).1 hr⟩
  have hmem : P.physicalDirichletFrequency ((n:ℕ):ℤ) q ∈ sourcePeriodicSegment (by norm_num) (by norm_num) (P.sourcePsi q) ((n:ℕ):ℤ) :=
    canonicalAuxiliaryPeriodOneRoots_mem_sourcePeriodicSegment_of_realType (by norm_num) (by norm_num) .dirichlet (P.sourcePsi q) (hillMiuraRealSource u).property _
  change P.physicalDirichletFrequency ((n:ℕ):ℤ) q ∈ segment ℝ l r at hmem
  rw [he,segment_same] at hmem
  rw [mem_singleton_iff.mp hmem]
  change l = (l+r)/2
  rw [he]
  ring

theorem physical_root_coefficient_zero_of_real_closed_gap (P : HillProductEquationPatch) (n : ℕ+)
    (q : PeriodOneHminusOne) (hq : q ∈ P.source) (hr : IsRealPeriodOneHminusOne q)
    (hg : hillHminusCanonicalGapSquare n q = 0) : P.physicalDirichletRootCoefficient n q = 0 := by
  apply eq_zero_of_pow_eq_zero
  have hs := P.physicalDirichletRootCoefficient_sq n q (P.real_mem_physicalDirichletSource q hq hr)
  rw [sourceAngularSelectedPolynomial,quadraticRootPolynomial,
    P.actual_frequency_eq_midpoint_of_real_closed_gap n q hq hr hg,
    P.frequency_gap_zero_of_real_original_gap_zero n q hq hr hg] at hs
  simpa only [sub_self,zero_pow (by decide : (2:ℕ) ≠ 0),zero_div,sub_zero] using hs

theorem physicalOnIndexCartesian_zero_of_real_closed_gap (P : HillProductEquationPatch) (n : ℕ+)
    (q : PeriodOneHminusOne) (hq : q ∈ P.source) (hr : IsRealPeriodOneHminusOne q)
    (hg : hillHminusCanonicalGapSquare n q = 0) :
    P.physicalOnIndexCartesianPlus n q = 0 ∧ P.physicalOnIndexCartesianMinus n q = 0 := by
  have hμ := P.actual_frequency_eq_midpoint_of_real_closed_gap n q hq hr hg
  have hr0 := P.physical_root_coefficient_zero_of_real_closed_gap n q hq hr hg
  simp [physicalOnIndexCartesianPlus,physicalOnIndexCartesianMinus,hμ,hr0]

end NLS.KdV.HillProductEquationPatch
