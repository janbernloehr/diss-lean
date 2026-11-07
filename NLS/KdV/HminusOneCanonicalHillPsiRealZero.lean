import NLS.KdV.HminusOneCanonicalHillPsiSimpleZeros
import NLS.KdV.HillOriginalPositiveGapSeparation

/-! Every retained ORIGINAL real Hill gap contains exactly one zero
of its intrinsic numerator, including collapsed gaps. This defines the
actual real energy zero coefficients; the omitted coefficient is filled
by its original gap midpoint, as in the source. No complex analytic
extension or finer all-index zero estimate is asserted here. -/
noncomputable section
open Set Complex
open scoped ENNReal Classical
namespace NLS.KdV

theorem existsUnique_hillHminusCanonicalPsi_zero_in_original_gap
    (q : PeriodOneHminusOne) (hr : IsRealPeriodOneHminusOne q) (n m : ℕ+) (hmn : m ≠ n) :
    ∃! E : ℝ, E ∈ Icc (hillHminusLabels q hr (2*(m:ℕ)-1)) (hillHminusLabels q hr (2*(m:ℕ))) ∧
      hillHminusCanonicalPsi n ((E:ℂ),q) = 0 := by
  obtain ⟨σ,hσ,hzeros,_⟩ := exists_hillHminusCanonicalPsi_exact_real_zeros q hr n
  refine ⟨σ m,⟨hσ m,(hzeros (σ m:ℂ)).mpr ⟨m,hmn,rfl⟩⟩,?_⟩
  intro E hE
  obtain ⟨j,_,hj⟩ := (hzeros (E:ℂ)).mp hE.2
  have hjm : j = m := by
    by_contra hne
    have he : σ j = E := Complex.ofReal_inj.mp hj
    exact Set.disjoint_left.mp (hillHminusOriginal_positive_gaps_disjoint q hr j m hne)
      (hσ j) (he ▸ hE.1)
  rw [hjm] at hj
  exact (Complex.ofReal_inj.mp hj).symm

def hillHminusCanonicalPsiRealZero (n m : ℕ+) (q : PeriodOneHminusOne)
    (hr : IsRealPeriodOneHminusOne q) : ℝ :=
  if hmn : m = n then
    (hillHminusLabels q hr (2*(m:ℕ)-1)+hillHminusLabels q hr (2*(m:ℕ)))/2
  else Classical.choose (existsUnique_hillHminusCanonicalPsi_zero_in_original_gap q hr n m hmn)

theorem hillHminusCanonicalPsiRealZero_mem_gap (n m : ℕ+) (q : PeriodOneHminusOne)
    (hr : IsRealPeriodOneHminusOne q) :
    hillHminusCanonicalPsiRealZero n m q hr ∈
      Icc (hillHminusLabels q hr (2*(m:ℕ)-1)) (hillHminusLabels q hr (2*(m:ℕ))) := by
  by_cases hm : m = n
  · rw [hillHminusCanonicalPsiRealZero,dif_pos hm]
    have hle := monotone_hillHminusLabels q hr (show 2*(m:ℕ)-1 ≤ 2*(m:ℕ) by omega)
    exact ⟨by linarith,by linarith⟩
  · rw [hillHminusCanonicalPsiRealZero,dif_neg hm]
    exact (Classical.choose_spec (existsUnique_hillHminusCanonicalPsi_zero_in_original_gap q hr n m hm)).1.1

theorem hillHminusCanonicalPsiRealZero_is_zero (n m : ℕ+) (q : PeriodOneHminusOne)
    (hr : IsRealPeriodOneHminusOne q) (hmn : m ≠ n) :
    hillHminusCanonicalPsi n ((hillHminusCanonicalPsiRealZero n m q hr:ℂ),q) = 0 := by
  rw [hillHminusCanonicalPsiRealZero,dif_neg hmn]
  exact (Classical.choose_spec (existsUnique_hillHminusCanonicalPsi_zero_in_original_gap q hr n m hmn)).1.2

theorem hillHminusCanonicalPsiRealZero_unique (n m : ℕ+) (q : PeriodOneHminusOne)
    (hr : IsRealPeriodOneHminusOne q) (hmn : m ≠ n) (E : ℝ)
    (hE : E ∈ Icc (hillHminusLabels q hr (2*(m:ℕ)-1)) (hillHminusLabels q hr (2*(m:ℕ))))
    (hz : hillHminusCanonicalPsi n ((E:ℂ),q) = 0) : E = hillHminusCanonicalPsiRealZero n m q hr := by
  rw [hillHminusCanonicalPsiRealZero,dif_neg hmn]
  exact (Classical.choose_spec (existsUnique_hillHminusCanonicalPsi_zero_in_original_gap q hr n m hmn)).2 E ⟨hE,hz⟩

theorem hillHminusCanonicalPsi_zero_iff_realZero (n : ℕ+) (q : PeriodOneHminusOne)
    (hr : IsRealPeriodOneHminusOne q) (a : ℂ) :
    hillHminusCanonicalPsi n (a,q) = 0 ↔
      ∃ m : ℕ+, m ≠ n ∧ (hillHminusCanonicalPsiRealZero n m q hr:ℂ) = a := by
  constructor
  · intro ha
    obtain ⟨m,hm,E,hE,he⟩ := hillHminusCanonicalPsi_zero_real_and_in_retained_gap q hr n a ha
    have hz : hillHminusCanonicalPsi n ((E:ℂ),q) = 0 := by rw [he]; exact ha
    have huniq := hillHminusCanonicalPsiRealZero_unique n m q hr hm E hE hz
    exact ⟨m,hm,by rw [← huniq]; exact he⟩
  · rintro ⟨m,hm,he⟩
    rw [← he]
    exact hillHminusCanonicalPsiRealZero_is_zero n m q hr hm

theorem hillHminusCanonicalPsiRealZero_at_real_collapse (n m : ℕ+) (q : PeriodOneHminusOne)
    (hr : IsRealPeriodOneHminusOne q)
    (hc : hillHminusLabels q hr (2*(m:ℕ)-1) = hillHminusLabels q hr (2*(m:ℕ))) :
    hillHminusCanonicalPsiRealZero n m q hr = hillHminusLabels q hr (2*(m:ℕ)) := by
  have h := hillHminusCanonicalPsiRealZero_mem_gap n m q hr
  rw [hc] at h
  exact le_antisymm h.2 h.1

end NLS.KdV
