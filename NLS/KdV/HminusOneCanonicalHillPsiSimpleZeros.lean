import NLS.KdV.HminusOneCanonicalHillPsiProperties
import NLS.KdV.HillRetainedGapZeroRigidity

/-! Every real-source intrinsic Hill numerator has EXACTLY its retained
real gap zeros, and every zero is simple. Normalized actual periods
first exclude the identically zero function at EVERY complex source.
No normalized infinite-product formula or uniform zero bound is assumed. -/
noncomputable section
open Set Metric Complex NLS.ZakharovShabat NLS.ComplexAnalysis
open scoped ENNReal Classical
namespace NLS.KdV

theorem hillHminusCanonicalPsi_energy_ne_zero (n : ℕ+) (q : PeriodOneHminusOne)
    (hq : q ∈ hillHminusCanonicalPsiDomain) : (fun E : ℂ => hillHminusCanonicalPsi n (E,q)) ≠ 0 := by
  intro hzero
  obtain ⟨B,hB⟩ := mem_iUnion.mp hq
  obtain ⟨D⟩ := B.nonempty_canonicalPeriodCircle q hB n
  have hp := B.canonical_pullback_period n n q hB D
  have hz (E : ℂ) : hillHminusCanonicalPsi n (E,q) = 0 := congrFun hzero E
  simp_rw [hz] at hp
  simp [circleIntegral] at hp

theorem exists_hillHminusCanonicalPsi_real_gap_samples
    (q : PeriodOneHminusOne) (hr : IsRealPeriodOneHminusOne q) (n : ℕ+) :
    ∃ σ : ℕ+ → ℝ,
      (∀ m : ℕ+, σ m ∈ Icc (hillHminusLabels q hr (2*(m:ℕ)-1)) (hillHminusLabels q hr (2*(m:ℕ)))) ∧
      ∀ m : ℕ+, m ≠ n → hillHminusCanonicalPsi n ((σ m:ℂ),q) = 0 := by
  have hex (m : ℕ+) : ∃ E : ℝ,
      E ∈ Icc (hillHminusLabels q hr (2*(m:ℕ)-1)) (hillHminusLabels q hr (2*(m:ℕ))) ∧
      (m ≠ n → hillHminusCanonicalPsi n ((E:ℂ),q) = 0) := by
    by_cases hm : m = n
    · have hle := monotone_hillHminusLabels q hr (show 2*(m:ℕ)-1 ≤ 2*(m:ℕ) by omega)
      refine ⟨(hillHminusLabels q hr (2*(m:ℕ)-1)+hillHminusLabels q hr (2*(m:ℕ)))/2,
        ⟨by linarith,by linarith⟩,fun hne => (hne hm).elim⟩
    · obtain ⟨E,hE,hz⟩ := exists_hillHminusCanonicalPsi_zero_in_original_gap q hr n m hm
      exact ⟨E,hE,fun _ => hz⟩
  choose σ hgap hz using hex
  exact ⟨σ,hgap,hz⟩

/-- Exact zero classification and simplicity, with all original gap indices. -/
theorem exists_hillHminusCanonicalPsi_exact_real_zeros
    (q : PeriodOneHminusOne) (hr : IsRealPeriodOneHminusOne q) (n : ℕ+) :
    ∃ σ : ℕ+ → ℝ,
      (∀ m : ℕ+, σ m ∈ Icc (hillHminusLabels q hr (2*(m:ℕ)-1)) (hillHminusLabels q hr (2*(m:ℕ)))) ∧
      (∀ a : ℂ, hillHminusCanonicalPsi n (a,q) = 0 ↔ ∃ m : ℕ+, m ≠ n ∧ (σ m:ℂ) = a) ∧
      ∀ a : ℂ, hillHminusCanonicalPsi n (a,q) = 0 →
        deriv (fun E : ℂ => hillHminusCanonicalPsi n (E,q)) a ≠ 0 := by
  have hq := real_mem_hillHminusCanonicalPsiDomain q hr
  obtain ⟨B,hB⟩ := mem_iUnion.mp hq
  let u : PeriodOneRealL2 := ⟨B.parent.miuraBall.actionBall.lift q,
    B.parent.miuraBall.actionBall.lift_real q (B.subset hB).1 hr⟩
  let c := B.parent.miuraBall.actionBall.shift
  have hi : periodOneMiura u.val = q+periodOneL2Inclusion (lp.single 2 0 (c:ℂ)) :=
    B.parent.miuraBall.actionBall.image q (B.subset hB).1
  have hc : -(c:ℂ) ∉ singularHillSpectrum (periodOneOriginal q) :=
    B.parent.miuraBall.actionBall.outside q (B.subset hB).1
  obtain ⟨σ,hσ,hzero⟩ := exists_hillHminusCanonicalPsi_real_gap_samples q hr n
  have hP := hillHminusCanonicalPsi_energy_entire n q hq
  have hnz := hillHminusCanonicalPsi_energy_ne_zero n q hq
  have hsmall := hillHminusCanonicalPsi_arbitrary_shift_sub_sine n q hq (c:ℂ)
  refine ⟨σ,hσ,?_,?_⟩
  · exact fun a => hillMiura_energy_zero_iff_retained_sample (q:=q) (hq:=hr) (u:=u) (c:=c)
      (hi:=hi) (hc:=hc) (P:=fun E => hillHminusCanonicalPsi n (E,q)) (hP:=hP) (hnz:=hnz)
      (n:=n) (σ:=σ) (hσ:=hσ) (hzero:=hzero) (hsmall:=hsmall) a
  · exact fun a ha => hillMiura_energy_deriv_ne_zero_at_zero (q:=q) (hq:=hr) (u:=u) (c:=c)
      (hi:=hi) (hc:=hc) (P:=fun E => hillHminusCanonicalPsi n (E,q)) (hP:=hP) (hnz:=hnz)
      (n:=n) (σ:=σ) (hσ:=hσ) (hzero:=hzero) (hsmall:=hsmall) a ha

theorem hillHminusCanonicalPsi_deriv_ne_zero_of_real_source
    (q : PeriodOneHminusOne) (hr : IsRealPeriodOneHminusOne q) (n : ℕ+) (a : ℂ)
    (ha : hillHminusCanonicalPsi n (a,q) = 0) :
    deriv (fun E : ℂ => hillHminusCanonicalPsi n (E,q)) a ≠ 0 := by
  obtain ⟨_,_,_,hsimple⟩ := exists_hillHminusCanonicalPsi_exact_real_zeros q hr n
  exact hsimple a ha

theorem hillHminusCanonicalPsi_zero_real_and_in_retained_gap
    (q : PeriodOneHminusOne) (hr : IsRealPeriodOneHminusOne q) (n : ℕ+) (a : ℂ)
    (ha : hillHminusCanonicalPsi n (a,q) = 0) :
    ∃ m : ℕ+, m ≠ n ∧ ∃ E : ℝ,
      E ∈ Icc (hillHminusLabels q hr (2*(m:ℕ)-1)) (hillHminusLabels q hr (2*(m:ℕ))) ∧ (E:ℂ) = a := by
  obtain ⟨σ,hσ,hzeros,_⟩ := exists_hillHminusCanonicalPsi_exact_real_zeros q hr n
  obtain ⟨m,hm,he⟩ := (hzeros a).mp ha
  exact ⟨m,hm,σ m,hσ m,he⟩

end NLS.KdV
