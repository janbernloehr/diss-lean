import NLS.ZakharovShabat.DiagonalSummationExponent
import NLS.SequenceSpaces.ReciprocalTail

/-! # Exact diagonal frequency regions in Lemma 6.8

The far row retains the equality case |m-n|=|n|/2. The near row
uses the strict complementary inequality. Actual sequence norms identify
the literal reciprocal moments, prove summability and retain the boundary
of the potential tail. Powered Young is applied to genuine coefficient rows.
-/

noncomputable section
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p q r : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ q)] [Fact (1 ≤ r)]

/-- The source far row, retaining equality at half the outer frequency. -/
def diagonalFarRow (hq : 1 < q) (a : Coeff p) (n : ℤ) : Coeff q :=
  Coeff.fourierTail ((n.natAbs+1)/2)
    (Coeff.convolutionRow a (Coeff.puncturedLattice q hq) (2*n))

/-- The complementary source near row. Its zero denominator is already removed. -/
def diagonalNearRow (hq : 1 < q) (a : Coeff p) (n : ℤ) : Coeff q :=
  Coeff.truncate (Coeff.lowFrequencies ((n.natAbs+1)/2))
    (Coeff.convolutionRow a (Coeff.puncturedLattice q hq) (2*n))

omit [Fact (1 ≤ q)] in
theorem diagonalFarRow_apply (hq : 1 < q) (a : Coeff p) (n l : ℤ) :
    diagonalFarRow hq a n l =
      if n.natAbs ≤ 2*l.natAbs then a (2*n-l) * Coeff.puncturedLattice q hq l else 0 := by
  simp only [diagonalFarRow,Coeff.fourierTail_apply,Coeff.convolutionRow_apply]
  congr 1
  apply propext
  omega

omit [Fact (1 ≤ q)] in
theorem diagonalNearRow_apply (hq : 1 < q) (a : Coeff p) (n l : ℤ) :
    diagonalNearRow hq a n l =
      if 2*l.natAbs < n.natAbs then a (2*n-l) * Coeff.puncturedLattice q hq l else 0 := by
  simp only [diagonalNearRow,Coeff.truncate_apply,Coeff.mem_lowFrequencies,Coeff.convolutionRow_apply]
  congr 1
  apply propext
  omega

omit [Fact (1 ≤ q)] in
theorem diagonalFarRow_add_near (hq : 1 < q) (a : Coeff p) (n : ℤ) :
    diagonalFarRow hq a n + diagonalNearRow hq a n =
      Coeff.convolutionRow a (Coeff.puncturedLattice q hq) (2*n) := by
  simp [diagonalFarRow,diagonalNearRow,Coeff.fourierTail]

/-- Exact half-radius geometry leaves the boundary of the potential tail intact. -/
theorem diagonal_near_potential_tail (N : ℕ) (n l : ℤ) (hn : N ≤ n.natAbs)
    (hl : 2*l.natAbs < n.natAbs) : N ≤ (2*n-l).natAbs := by omega

/-- Every far row is dominated by the fixed half-cutoff kernel row. -/
theorem norm_diagonalFarRow_le (hr : 1 < r) (hrq : r ≤ q) (a : Coeff p)
    (N : ℕ) (n : ℤ) (hn : N ≤ n.natAbs) :
    ‖diagonalFarRow (hr.trans_le hrq) a n‖ ≤
      ‖Coeff.convolutionRow a (Coeff.fourierTail ((N+1)/2) (Coeff.puncturedLattice r hr)) (2*n)‖ := by
  let b := Coeff.convolutionRow a (Coeff.fourierTail ((N+1)/2) (Coeff.puncturedLattice r hr)) (2*n)
  calc
    _ ≤ ‖Coeff.exponentInclusion hrq b‖ := by
      apply lp.norm_mono (zero_lt_one.trans (hr.trans_le hrq)).ne'
      intro l
      rw [diagonalFarRow_apply]
      by_cases hl : n.natAbs ≤ 2*l.natAbs
      · have hN : (N+1)/2 ≤ l.natAbs := by omega
        simp only [if_pos hl,Coeff.exponentInclusion_apply,b,Coeff.convolutionRow_apply,
          Coeff.fourierTail_apply,if_pos hN,Coeff.puncturedLattice_apply]
        exact le_rfl
      · simp only [if_neg hl,norm_zero]
        exact norm_nonneg _
    _ ≤ _ := Coeff.norm_exponentInclusion_le hrq b

/-- Every near row sees only the actual retained-boundary potential tail. -/
theorem norm_diagonalNearRow_le (hr : 1 < r) (hrq : r ≤ q) (a : Coeff p)
    (N : ℕ) (n : ℤ) (hn : N ≤ n.natAbs) :
    ‖diagonalNearRow (hr.trans_le hrq) a n‖ ≤
      ‖Coeff.convolutionRow (Coeff.fourierTail N a) (Coeff.puncturedLattice r hr) (2*n)‖ := by
  let b := Coeff.convolutionRow (Coeff.fourierTail N a) (Coeff.puncturedLattice r hr) (2*n)
  calc
    _ ≤ ‖Coeff.exponentInclusion hrq b‖ := by
      apply lp.norm_mono (zero_lt_one.trans (hr.trans_le hrq)).ne'
      intro l
      rw [diagonalNearRow_apply]
      by_cases hl : 2*l.natAbs < n.natAbs
      · have hN := diagonal_near_potential_tail N n l hn hl
        simp only [if_pos hl,Coeff.exponentInclusion_apply,b,Coeff.convolutionRow_apply,
          Coeff.fourierTail_apply,if_pos hN,Coeff.puncturedLattice_apply]
        exact le_rfl
      · simp only [if_neg hl,norm_zero]
        exact norm_nonneg _
    _ ≤ _ := Coeff.norm_exponentInclusion_le hrq b

omit [Fact (1 ≤ r)] in
/-- The exact far kernel has the source N^(-1/s) decay, including odd cutoffs. -/
theorem norm_diagonalHalfKernel_le (hr : 1 < r) {s : ℝ}
    (hc : s.HolderConjugate r.toReal) (N : ℕ) (hN : 0 < N) :
    ‖Coeff.fourierTail ((N+1)/2) (Coeff.puncturedLattice r hr)‖ ≤
      8*s*(N : ℝ)^(-(1/s)) := by
  have hNr : 0 < (N : ℝ)/2 := by positivity
  have hs0 := hc.pos
  have hb : ‖Coeff.fourierTail ((N+1)/2) (Coeff.puncturedLattice r hr)‖ ≤
      4*s*((N : ℝ)/2)^(-(1/s)) := by
    apply Coeff.norm_punctured_reciprocal_le hc hNr
    · simp
    · intro k hk
      by_cases hcut : (N+1)/2 ≤ k.natAbs
      · simp only [Coeff.fourierTail_apply,if_pos hcut,Coeff.puncturedLattice_apply,
          if_neg hk,norm_inv,Complex.norm_intCast]
        have hkN : (N : ℝ)/2 ≤ |(k : ℝ)| := by
          have hh : N ≤ 2*k.natAbs := by omega
          have hh' : (N : ℝ) ≤ 2*(k.natAbs : ℝ) := by exact_mod_cast hh
          simp only [Nat.cast_natAbs,Int.cast_abs] at hh'
          linarith
        rw [inv_eq_one_div]
        apply (div_le_div_iff₀ (hNr.trans_le hkN) (by positivity)).mpr
        linarith
      · simp only [Coeff.fourierTail_apply,if_neg hcut,norm_zero]
        positivity
  calc
    _ ≤ 4*s*((N : ℝ)/2)^(-(1/s)) := hb
    _ ≤ 4*s*(2*(N : ℝ)^(-(1/s))) :=
      mul_le_mul_of_nonneg_left (Coeff.half_radius_rpow_le hc.lt.le (by positivity)) (by positivity)
    _ = _ := by ring

/-- A genuine outer sequence norm turns pointwise row domination into a summable power bound. -/
theorem diagonalRow_power_sum_le (hp : p ≠ ⊤) (F : ℤ → ℝ) (N : ℕ)
    (hF : ∀ n, 0 ≤ F n) (d : Coeff p) (hd : ∀ n, N ≤ n.natAbs → F n ≤ ‖d n‖)
    (B : ℝ) (hB : ‖d‖ ≤ B) :
    Summable (fun n : ℤ => if N ≤ n.natAbs then (F n)^p.toReal else 0) ∧
    (∑' n : ℤ, if N ≤ n.natAbs then (F n)^p.toReal else 0) ≤ B^p.toReal := by
  have hP : 0 < p.toReal := ENNReal.toReal_pos (zero_lt_one.trans_le (Fact.out : 1 ≤ p)).ne' hp
  have hs := (lp.memℓp d).summable hP
  have hnon (n : ℤ) : 0 ≤ (if N ≤ n.natAbs then (F n)^p.toReal else 0) := by
    split_ifs
    · exact Real.rpow_nonneg (hF n) _
    · exact le_rfl
  have hdom (n : ℤ) : (if N ≤ n.natAbs then (F n)^p.toReal else 0) ≤ ‖d n‖^p.toReal := by
    split_ifs with hn
    · exact Real.rpow_le_rpow (hF n) (hd n hn) hP.le
    · positivity
  have hsum := Summable.of_nonneg_of_le hnon hdom hs
  refine ⟨hsum,?_⟩
  calc
    _ ≤ ∑' n : ℤ, ‖d n‖^p.toReal := hsum.tsum_le_tsum hdom hs
    _ = ‖d‖^p.toReal := (lp.norm_rpow_eq_tsum hP d).symm
    _ ≤ _ := Real.rpow_le_rpow (norm_nonneg _) hB hP.le

/-- Powered Young bounds the exact far-region sum for every admissible inner exponent. -/
theorem diagonalFarRow_sum_le (hp : p ≠ ⊤) (hr : 1 < r) (hrp : r ≤ p) (hrq : r ≤ q)
    (a : Coeff p) (N : ℕ) :
    Summable (fun n : ℤ => if N ≤ n.natAbs then ‖diagonalFarRow (hr.trans_le hrq) a n‖^p.toReal else 0) ∧
    (∑' n : ℤ, if N ≤ n.natAbs then ‖diagonalFarRow (hr.trans_le hrq) a n‖^p.toReal else 0) ≤
      (‖a‖ * ‖Coeff.fourierTail ((N+1)/2) (Coeff.puncturedLattice r hr)‖)^p.toReal := by
  obtain ⟨d,hd,hb⟩ := Coeff.exists_evenConvolutionRowNorm hp hrp a
    (Coeff.fourierTail ((N+1)/2) (Coeff.puncturedLattice r hr))
  apply diagonalRow_power_sum_le hp _ N (fun _ => norm_nonneg _) d _ _ hb
  intro n hn
  rw [hd,Complex.norm_real,Real.norm_of_nonneg (norm_nonneg _)]
  exact norm_diagonalFarRow_le hr hrq a N n hn

/-- Powered Young bounds the exact near-region sum by the actual potential tail. -/
theorem diagonalNearRow_sum_le (hp : p ≠ ⊤) (hr : 1 < r) (hrp : r ≤ p) (hrq : r ≤ q)
    (a : Coeff p) (N : ℕ) :
    Summable (fun n : ℤ => if N ≤ n.natAbs then ‖diagonalNearRow (hr.trans_le hrq) a n‖^p.toReal else 0) ∧
    (∑' n : ℤ, if N ≤ n.natAbs then ‖diagonalNearRow (hr.trans_le hrq) a n‖^p.toReal else 0) ≤
      (‖Coeff.fourierTail N a‖ * ‖Coeff.puncturedLattice r hr‖)^p.toReal := by
  obtain ⟨d,hd,hb⟩ := Coeff.exists_evenConvolutionRowNorm hp hrp (Coeff.fourierTail N a)
    (Coeff.puncturedLattice r hr)
  apply diagonalRow_power_sum_le hp _ N (fun _ => norm_nonneg _) d _ _ hb
  intro n hn
  rw [hd,Complex.norm_real,Real.norm_of_nonneg (norm_nonneg _)]
  exact norm_diagonalNearRow_le hr hrq a N n hn

/-- The literal far reciprocal moment in the signed source index. -/
def diagonalFarMoment (q : ℝ≥0∞) (a : Coeff p) (n : ℤ) : ℝ :=
  ∑' m : ℤ, if n.natAbs ≤ 2*(m-n).natAbs then
    (‖a (n+m)‖ / |((m-n : ℤ) : ℝ)|)^q.toReal else 0

/-- The literal near reciprocal moment; the removed denominator contributes zero. -/
def diagonalNearMoment (q : ℝ≥0∞) (a : Coeff p) (n : ℤ) : ℝ :=
  ∑' m : ℤ, if 2*(m-n).natAbs < n.natAbs then
    (‖a (n+m)‖ / |((m-n : ℤ) : ℝ)|)^q.toReal else 0

omit [Fact (1 ≤ q)] in
theorem diagonalFarMoment_eq (hq : 1 < q) (hqt : q ≠ ⊤) (a : Coeff p) (n : ℤ) :
    diagonalFarMoment q a n = ‖diagonalFarRow hq a n‖^q.toReal := by
  have hQ := ENNReal.toReal_pos (zero_lt_one.trans hq).ne' hqt
  rw [lp.norm_rpow_eq_tsum hQ,← (Equiv.subLeft n).tsum_eq]
  apply tsum_congr
  intro m
  simp only [Equiv.subLeft_apply,diagonalFarRow_apply,
    show 2*n-(n-m) = n+m by ring,show (n-m).natAbs = (m-n).natAbs by omega]
  split_ifs with hcut
  · by_cases hm : m = n
    · simp [hm,Coeff.puncturedLattice_apply,Real.zero_rpow hQ.ne']
    · simp only [Coeff.puncturedLattice_apply,if_neg (sub_ne_zero.mpr (Ne.symm hm)),norm_mul,
        norm_inv,Complex.norm_intCast]
      rw [show n-m = -(m-n) by ring,Int.cast_neg,abs_neg,div_eq_mul_inv]
  · simp [Real.zero_rpow hQ.ne']

omit [Fact (1 ≤ q)] in
theorem diagonalNearMoment_eq (hq : 1 < q) (hqt : q ≠ ⊤) (a : Coeff p) (n : ℤ) :
    diagonalNearMoment q a n = ‖diagonalNearRow hq a n‖^q.toReal := by
  have hQ := ENNReal.toReal_pos (zero_lt_one.trans hq).ne' hqt
  rw [lp.norm_rpow_eq_tsum hQ,← (Equiv.subLeft n).tsum_eq]
  apply tsum_congr
  intro m
  simp only [Equiv.subLeft_apply,diagonalNearRow_apply,
    show 2*n-(n-m) = n+m by ring,show (n-m).natAbs = (m-n).natAbs by omega]
  split_ifs with hcut
  · by_cases hm : m = n
    · simp [hm,Coeff.puncturedLattice_apply,Real.zero_rpow hQ.ne']
    · simp only [Coeff.puncturedLattice_apply,if_neg (sub_ne_zero.mpr (Ne.symm hm)),norm_mul,
        norm_inv,Complex.norm_intCast]
      rw [show n-m = -(m-n) by ring,Int.cast_neg,abs_neg,div_eq_mul_inv]
  · simp [Real.zero_rpow hQ.ne']

theorem diagonalFarMoment_power_eq (hq : 1 < q) (hqt : q ≠ ⊤) (a : Coeff p) (n : ℤ) :
    (diagonalFarMoment q a n)^(p.toReal/q.toReal) = ‖diagonalFarRow hq a n‖^p.toReal := by
  rw [diagonalFarMoment_eq hq hqt,← Real.rpow_mul (norm_nonneg _)]
  congr 1
  field_simp [(ENNReal.toReal_pos (zero_lt_one.trans hq).ne' hqt).ne']

theorem diagonalNearMoment_power_eq (hq : 1 < q) (hqt : q ≠ ⊤) (a : Coeff p) (n : ℤ) :
    (diagonalNearMoment q a n)^(p.toReal/q.toReal) = ‖diagonalNearRow hq a n‖^p.toReal := by
  rw [diagonalNearMoment_eq hq hqt,← Real.rpow_mul (norm_nonneg _)]
  congr 1
  field_simp [(ENNReal.toReal_pos (zero_lt_one.trans hq).ne' hqt).ne']

omit [Fact (1 ≤ q)] in
/-- The full source reciprocal moment is an absolutely convergent sum. -/
theorem summable_diagonalMoment (hq : 1 < q) (hqt : q ≠ ⊤) (a : Coeff p) (n : ℤ) :
    Summable (fun m : ℤ => (‖a (n+m)‖ / |((m-n : ℤ) : ℝ)|)^q.toReal) := by
  have hQ := ENNReal.toReal_pos (zero_lt_one.trans hq).ne' hqt
  have hs := (Equiv.subLeft n).summable_iff.mpr
    ((lp.memℓp (Coeff.convolutionRow a (Coeff.puncturedLattice q hq) (2*n))).summable hQ)
  apply hs.congr
  intro m
  simp only [Function.comp_def,Equiv.subLeft_apply,Coeff.convolutionRow_apply,
    show 2*n-(n-m) = n+m by ring]
  by_cases hm : m = n
  · simp [hm,Coeff.puncturedLattice_apply,Real.zero_rpow hQ.ne']
  · simp only [Coeff.puncturedLattice_apply,if_neg (sub_ne_zero.mpr (Ne.symm hm)),norm_mul,
      norm_inv,Complex.norm_intCast]
    rw [show n-m = -(m-n) by ring,Int.cast_neg,abs_neg,div_eq_mul_inv]

omit [Fact (1 ≤ q)] in
/-- The two displayed inner sums form an exact, summable partition. -/
theorem diagonalMoment_split (hq : 1 < q) (hqt : q ≠ ⊤) (a : Coeff p) (n : ℤ) :
    (∑' m : ℤ, (‖a (n+m)‖ / |((m-n : ℤ) : ℝ)|)^q.toReal) =
      diagonalFarMoment q a n + diagonalNearMoment q a n := by
  let f : ℤ → ℝ := fun m => (‖a (n+m)‖ / |((m-n : ℤ) : ℝ)|)^q.toReal
  have hs : Summable f := summable_diagonalMoment hq hqt a n
  have hf0 (m : ℤ) : 0 ≤ f m := Real.rpow_nonneg (by positivity) _
  have hf : Summable (fun m : ℤ => if n.natAbs ≤ 2*(m-n).natAbs then f m else 0) :=
    Summable.of_nonneg_of_le (fun m => ite_nonneg (hf0 m) le_rfl)
      (fun m => by split_ifs <;> first | exact le_rfl | exact hf0 m) hs
  have hn : Summable (fun m : ℤ => if 2*(m-n).natAbs < n.natAbs then f m else 0) :=
    Summable.of_nonneg_of_le (fun m => ite_nonneg (hf0 m) le_rfl)
      (fun m => by split_ifs <;> first | exact le_rfl | exact hf0 m) hs
  change (∑' m, f m) = (∑' m, if n.natAbs ≤ 2*(m-n).natAbs then f m else 0) +
    (∑' m, if 2*(m-n).natAbs < n.natAbs then f m else 0)
  rw [← hf.tsum_add hn]
  apply tsum_congr
  intro m
  by_cases h : n.natAbs ≤ 2*(m-n).natAbs
  · simp only [if_pos h,if_neg (Nat.not_lt.mpr h),add_zero]
  · simp only [if_neg h,if_pos (Nat.lt_of_not_ge h),zero_add]

/-- The integer half-cutoff predicate is exactly the printed real inequality. -/
theorem diagonal_far_region_iff (n m : ℤ) :
    n.natAbs ≤ 2*(m-n).natAbs ↔ |(n : ℝ)|/2 ≤ |((m-n : ℤ) : ℝ)| := by
  have he : (n.natAbs : ℝ) = |(n : ℝ)| := by simp
  have hf : ((m-n).natAbs : ℝ) = |((m-n : ℤ) : ℝ)| := by simp
  rw [← he,← hf]
  constructor
  · intro h
    have hh : (n.natAbs : ℝ) ≤ 2*((m-n).natAbs : ℝ) := by exact_mod_cast h
    linarith
  · intro h
    have hh : (n.natAbs : ℝ) ≤ 2*((m-n).natAbs : ℝ) := by linarith
    exact_mod_cast hh

end NLS.ZakharovShabat
