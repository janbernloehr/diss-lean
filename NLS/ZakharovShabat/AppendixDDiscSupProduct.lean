import NLS.ZakharovShabat.AppendixDFactorCutoff

/-! # The actual disc-supremum inequality in the proof of D.6 -/
noncomputable section
open Set Metric
open scoped ENNReal
namespace NLS.ZakharovShabat

/-- The norm supremum over one original open quarter-pi disc. -/
def appendixDDiscNormSup (n : ℤ) (f : ℂ → ℂ) : ℝ :=
  sSup ((fun z => ‖f z‖) '' refinedResonantDisk n)

/-- A uniform bound makes the disc norm supremum a genuine least upper bound. -/
theorem appendixDDiscNormSup_bounds (n : ℤ) (f : ℂ → ℂ) {K : ℝ}
    (hK : ∀ z ∈ refinedResonantDisk n, ‖f z‖ ≤ K) :
    0 ≤ appendixDDiscNormSup n f ∧
      (∀ z ∈ refinedResonantDisk n, ‖f z‖ ≤ appendixDDiscNormSup n f) ∧
      appendixDDiscNormSup n f ≤ K := by
  have hz : (Real.pi:ℂ)*n ∈ refinedResonantDisk n := by
    simp only [refinedResonantDisk,mem_ball,dist_self]
    positivity
  have hne : ((fun z => ‖f z‖) '' refinedResonantDisk n).Nonempty :=
    ⟨_,⟨_,hz,rfl⟩⟩
  have hb : BddAbove ((fun z => ‖f z‖) '' refinedResonantDisk n) :=
    ⟨K,by rintro _ ⟨z,hz,rfl⟩; exact hK z hz⟩
  exact ⟨(norm_nonneg _).trans (le_csSup hb ⟨_,hz,rfl⟩),
    fun z hz => le_csSup hb ⟨z,hz,rfl⟩,
    csSup_le hne (by rintro _ ⟨z,hz,rfl⟩; exact hK z hz)⟩

variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The source's sum of factor suprema and its square sum both converge. -/
theorem appendixDReciprocalTerm_discSup_summable (hp : p ≠ ⊤)
    (r : Coeff ⊤) (a : Coeff p) {c : ℝ} {N : ℕ}
    (hc : 0 < c) (hsep : AppendixDReferenceSeparated r c N)
    {n : ℤ} (hn : N ≤ n.natAbs) :
    (∀ m : ℤ, 0 ≤ appendixDDiscNormSup n (fun z => appendixDReciprocalTerm r a n z m)) ∧
    Summable (fun m : ℤ => appendixDDiscNormSup n (fun z => appendixDReciprocalTerm r a n z m)) ∧
    Summable (fun m : ℤ => (appendixDDiscNormSup n (fun z => appendixDReciprocalTerm r a n z m))^2) ∧
    ∀ m : ℤ, ∀ z ∈ refinedResonantDisk n,
      ‖appendixDReciprocalTerm r a n z m‖ ≤
        appendixDDiscNormSup n (fun w => appendixDReciprocalTerm r a n w m) := by
  let s := fun m : ℤ => appendixDDiscNormSup n (fun z => appendixDReciprocalTerm r a n z m)
  have hb (m : ℤ) := appendixDDiscNormSup_bounds n
    (fun z => appendixDReciprocalTerm r a n z m)
    (fun z hz => (appendixDReciprocalTerm_bounds hp r a hc hsep hn hz).2.2 m)
  have hs : Summable s := ((NLS.Fourier.summable_absoluteSampledRow hp a n).mul_left c).of_nonneg_of_le
    (fun m => (hb m).1) (fun m => (hb m).2.2)
  have hsq : Summable (fun m : ℤ => (s m)^2) := by
    apply (hs.mul_right (∑' m, s m)).of_nonneg_of_le (fun _ => sq_nonneg _)
    intro m
    have h := hs.le_tsum m (fun k _ => (hb k).1)
    nlinarith [(hb m).1]
  exact ⟨fun m => (hb m).1,hs,hsq,fun m => (hb m).2.1⟩

/-- The sum of factor suprema has the source's conjugate-kernel Holder bound. -/
theorem appendixDReciprocalTerm_discSup_sum_le (hp1 : 1 < p) (hp : p ≠ ⊤)
    (r : Coeff ⊤) (a : Coeff p) {c : ℝ} {N : ℕ}
    (hc : 0 < c) (hsep : AppendixDReferenceSeparated r c N)
    {n : ℤ} (hn : N ≤ n.natAbs) :
    (∑' m : ℤ, appendixDDiscNormSup n (fun z => appendixDReciprocalTerm r a n z m)) ≤
      c*‖NLS.Fourier.hilbertKernelCoeffs
        ((ENNReal.HolderConjugate.lt_top_iff_one_lt p p.conjExponent).mp hp.lt_top)‖*‖a‖ := by
  let : Fact (1 ≤ p.conjExponent) := ⟨ENNReal.HolderConjugate.one_le p.conjExponent p⟩
  have hq : p.conjExponent ≠ ⊤ :=
    ((ENNReal.HolderConjugate.lt_top_iff_one_lt p.conjExponent p).mpr hp1).ne
  have hq1 : 1 < p.conjExponent :=
    (ENNReal.HolderConjugate.lt_top_iff_one_lt p p.conjExponent).mp hp.lt_top
  let b := NLS.Fourier.hilbertKernelCoeffs hq1
  have hb : (∑' m : ℤ, ‖a m‖*‖NLS.Fourier.hilbertKernel (n-m)‖) ≤ ‖a‖*‖b‖ := by
    simpa only [Coeff.reindex_apply,Equiv.subLeft_apply,Coeff.norm_reindex,
      b,NLS.Fourier.hilbertKernelCoeffs] using
      (lp.tsum_mul_le_mul_norm (ENNReal.HolderConjugate.toReal_of_ne_top hp hq)
        a (Coeff.reindex (Equiv.subLeft n) b)).2
  have hs := (appendixDReciprocalTerm_discSup_summable hp r a hc hsep hn).2.1
  have hbound := hs.tsum_le_tsum
    (fun m => (appendixDDiscNormSup_bounds n (fun z => appendixDReciprocalTerm r a n z m)
      (fun z hz => (appendixDReciprocalTerm_bounds hp r a hc hsep hn hz).2.2 m)).2.2)
    ((NLS.Fourier.summable_absoluteSampledRow hp a n).mul_left c)
  rw [tsum_mul_left] at hbound
  exact (hbound.trans (mul_le_mul_of_nonneg_left hb hc.le)).trans_eq (by ring)

/-- D.1 yields the corrected inequality for the actual product supremum and three source sums. -/
theorem exists_appendixDRelativeProduct_discSup_signed_bound (hp : p ≠ ⊤)
    (r : Coeff ⊤) (a : Coeff p) {c : ℝ} {N : ℕ}
    (hc : 0 < c) (hsep : AppendixDReferenceSeparated r c N) :
    ∃ M : ℕ, N ≤ M ∧ 0 < M ∧ ∀ n : ℤ, M ≤ n.natAbs →
      let S := ∑' m : ℤ, appendixDDiscNormSup n (fun z => appendixDReciprocalTerm r a n z m)
      let A := appendixDDiscNormSup n (fun z => ∑' m : ℤ, appendixDReciprocalTerm r a n z m)
      let B := ∑' m : ℤ, (appendixDDiscNormSup n (fun z => appendixDReciprocalTerm r a n z m))^2
      appendixDDiscNormSup n (appendixDRelativeProductError r a n) ≤
        A*Real.exp S+B*Real.exp (S+S^2) := by
  obtain ⟨M,hNM,hM,hprod⟩ := exists_appendixDRelativeProduct_signed_bound hp r a hc hsep
  refine ⟨M,hNM,hM,?_⟩
  intro n hn
  let s := fun m : ℤ => appendixDDiscNormSup n (fun z => appendixDReciprocalTerm r a n z m)
  let S := ∑' m : ℤ, s m
  let A := appendixDDiscNormSup n (fun z => ∑' m : ℤ, appendixDReciprocalTerm r a n z m)
  let B := ∑' m : ℤ, (s m)^2
  obtain ⟨hs0,hs,hsq,hpoint⟩ := appendixDReciprocalTerm_discSup_summable hp r a hc hsep (hNM.trans hn)
  have hS0 : 0 ≤ S := tsum_nonneg hs0
  have hB0 : 0 ≤ B := tsum_nonneg (fun m => sq_nonneg _)
  have hsum (z : ℂ) (hz : z ∈ refinedResonantDisk n) :
      (∑' m, ‖appendixDReciprocalTerm r a n z m‖) ≤ S :=
    (appendixDReciprocalTerm_bounds hp r a hc hsep (hNM.trans hn) hz).1.tsum_le_tsum
      (fun m => hpoint m z hz) hs
  have hnorm (z : ℂ) (hz : z ∈ refinedResonantDisk n) :
      ‖∑' m, appendixDReciprocalTerm r a n z m‖ ≤ S :=
    (norm_tsum_le_tsum_norm (appendixDReciprocalTerm_bounds hp r a hc hsep (hNM.trans hn) hz).1).trans
      (hsum z hz)
  have hA := appendixDDiscNormSup_bounds n
    (fun z => ∑' m, appendixDReciprocalTerm r a n z m) hnorm
  apply (appendixDDiscNormSup_bounds n (appendixDRelativeProductError r a n) ?_).2.2
  intro z hz
  have hsz := (appendixDReciprocalTerm_bounds hp r a hc hsep (hNM.trans hn) hz).1
  have hsqz : (∑' m, ‖appendixDReciprocalTerm r a n z m‖^2) ≤ B := by
    apply (NLS.ComplexAnalysis.summable_sq_norm_of_summable_norm _ hsz).tsum_le_tsum _ hsq
    intro m
    exact pow_le_pow_left₀ (norm_nonneg _) (hpoint m z hz) 2
  have hSsz := hsum z hz
  have hsz0 : 0 ≤ ∑' m, ‖appendixDReciprocalTerm r a n z m‖ := tsum_nonneg (fun _ => norm_nonneg _)
  have hpow : (∑' m, ‖appendixDReciprocalTerm r a n z m‖)^2 ≤ S^2 :=
    pow_le_pow_left₀ hsz0 hSsz 2
  apply (hprod n hn z hz).trans
  apply add_le_add
  · exact mul_le_mul ((hA.2.1) z hz) (Real.exp_le_exp.mpr hSsz)
      (Real.exp_pos _).le hA.1
  · exact mul_le_mul hsqz (Real.exp_le_exp.mpr (add_le_add hSsz hpow))
      (Real.exp_pos _).le hB0

end NLS.ZakharovShabat
