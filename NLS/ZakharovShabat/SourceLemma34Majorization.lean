import NLS.ZakharovShabat.SourceSection3Setup
import NLS.ZakharovShabat.SourceLemma34Proof
import NLS.SequenceSpaces.SandwichAbsoluteSum
import Mathlib.Analysis.Real.Pi.Bounds

/-! # The absolute double-sum estimate in the proof of Lemma 3.4

The printed denominator bound yields the factor two. The infinite majorant
is summable for every finite Banach exponent, including p=1.
-/

noncomputable section
open scoped ENNReal
namespace NLS.ZakharovShabat

/-- The literal lower bound printed in the proof of Lemma 3.4. -/
theorem sourceLemma34_denominator_lower {n m : ℤ} {r : ℝ} {z : ℂ}
    (hr : 0 < r) (hrπ : r ≤ Real.pi / 4) (hz : z ∈ verticalStrip n r) :
    r / Real.sqrt 2 + |((n - m : ℤ) : ℝ)| ≤ ‖z - (Real.pi : ℂ) * m‖ := by
  have hs : (7 : ℝ) / 5 ≤ Real.sqrt 2 := by
    nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2), Real.sqrt_nonneg (2 : ℝ)]
  have hspos : 0 < Real.sqrt (2 : ℝ) := by positivity
  have hratio : r / Real.sqrt 2 ≤ 5 * r / 7 := by
    apply (div_le_iff₀ hspos).mpr
    nlinarith [mul_le_mul_of_nonneg_left hs hr.le]
  by_cases hmn : m = n
  · subst m
    simp only [sub_self, Int.cast_zero, abs_zero, add_zero]
    exact (hratio.trans (by linarith)).trans hz.2
  · have habs : 1 ≤ |((m - n : ℤ) : ℝ)| := by
      exact_mod_cast Int.one_le_abs (sub_ne_zero.mpr hmn)
    have htri : Real.pi * |((m - n : ℤ) : ℝ)| ≤
        |z.re - Real.pi * m| + |z.re - Real.pi * n| := by
      have h := norm_sub_le (z.re - Real.pi * m) (z.re - Real.pi * n)
      have he : (z.re - Real.pi * m) - (z.re - Real.pi * n) =
          -Real.pi * ((m - n : ℤ) : ℝ) := by push_cast; ring
      simpa only [he, norm_mul, norm_neg, Real.norm_eq_abs, abs_of_pos Real.pi_pos] using h
    have hre : |z.re - Real.pi * m| ≤ ‖z - (Real.pi : ℂ) * m‖ := by
      simpa using Complex.abs_re_le_norm (z - (Real.pi : ℂ) * m)
    have hmul := mul_nonneg (sub_nonneg.mpr Real.pi_gt_three.le)
      (sub_nonneg.mpr habs)
    have hsymm : |((n - m : ℤ) : ℝ)| = |((m - n : ℤ) : ℝ)| := by
      push_cast
      exact abs_sub_comm _ _
    rw [hsymm]
    nlinarith [hz.1, Real.pi_gt_d2]

/-- The product estimate giving the printed factor two in the double sum. -/
theorem sourceLemma34_denominator_product {n l m : ℤ} {r : ℝ} {z : ℂ}
    (hr : 0 < r) (hrπ : r ≤ Real.pi / 4) (hz : z ∈ verticalStrip n r) :
    (r + |((n - l : ℤ) : ℝ)|) * (r + |((n - m : ℤ) : ℝ)|) ≤
      2 * ‖z - (Real.pi : ℂ) * l‖ * ‖z - (Real.pi : ℂ) * m‖ := by
  have hs : 1 ≤ Real.sqrt (2 : ℝ) := by
    nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2), Real.sqrt_nonneg (2 : ℝ)]
  have hspos : 0 < Real.sqrt (2 : ℝ) := by positivity
  have hb (k : ℤ) : r + |((n-k : ℤ) : ℝ)| ≤
      Real.sqrt 2 * ‖z - (Real.pi : ℂ) * k‖ := by
    have h := sourceLemma34_denominator_lower (m := k) hr hrπ hz
    have h' : r / Real.sqrt 2 ≤ ‖z - (Real.pi : ℂ) * k‖ - |((n-k : ℤ) : ℝ)| := by
      linarith
    have hh := (div_le_iff₀ hspos).mp h'
    have ha := mul_le_mul_of_nonneg_right hs (abs_nonneg (((n-k : ℤ) : ℝ)))
    nlinarith
  have hmul := mul_le_mul (hb l) (hb m) (by positivity : 0 ≤ r + |((n-m : ℤ) : ℝ)|)
    (by positivity : 0 ≤ Real.sqrt 2 * ‖z - (Real.pi : ℂ) * l‖)
  have he : (Real.sqrt 2 * ‖z - (Real.pi : ℂ) * l‖) *
      (Real.sqrt 2 * ‖z - (Real.pi : ℂ) * m‖) =
      2 * ‖z - (Real.pi : ℂ) * l‖ * ‖z - (Real.pi : ℂ) * m‖ := by
    calc
      _ = (Real.sqrt 2)^2 * ‖z - (Real.pi : ℂ) * l‖ * ‖z - (Real.pi : ℂ) * m‖ := by ring
      _ = _ := by rw [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  rwa [he] at hmul

/-- The literal radius/strip reciprocal belongs to the conjugate sequence space. -/
theorem sourceLemma34_reciprocal_memlp {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (hp : p ≠ ⊤) (n : ℤ) {r : ℝ} (hr : 0 < r) (hr1 : r ≤ 1) :
    Memℓp (fun k : ℤ => ((r + |((n-k : ℤ) : ℝ)| : ℝ) : ℂ)⁻¹) p.conjExponent := by
  let : Fact (1 ≤ p.conjExponent) := ⟨ENNReal.HolderConjugate.one_le p.conjExponent p⟩
  let a : Coeff p.conjExponent := WeightedCoeff.inverseWeight (Weight.sobolev 1)
    (Weight.inverse_sobolev_one_memlp
      ((ENNReal.HolderConjugate.lt_top_iff_one_lt p p.conjExponent).mp hp.lt_top))
  let b : Coeff p.conjExponent := (r : ℂ)⁻¹ • Coeff.shift n a
  apply (lp.memℓp b).mono'
  intro k
  have hsymm : |((k-n : ℤ) : ℝ)| = |((n-k : ℤ) : ℝ)| := by
    push_cast
    exact abs_sub_comm _ _
  change ‖((r + |((n-k : ℤ) : ℝ)| : ℝ) : ℂ)⁻¹‖ ≤ ‖(r : ℂ)⁻¹ * a (k-n)‖
  have ha : ‖a (k-n)‖ = (1+|((n-k : ℤ) : ℝ)|)⁻¹ := by
    change ‖(Weight.sobolev 1 (k-n) : ℂ)⁻¹‖ = _
    simp only [Weight.sobolev_apply, Real.rpow_one, norm_inv, Complex.norm_real,
      Real.norm_eq_abs, hsymm]
    rw [abs_of_pos (by positivity : 0 < 1+|((n-k : ℤ) : ℝ)|)]
  rw [norm_mul, ha, norm_inv, norm_inv, Complex.norm_real, Complex.norm_real,
    Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos hr,
    abs_of_pos (by positivity : 0 < r+|((n-k : ℤ) : ℝ)|), ← mul_inv]
  apply inv_anti₀ (by positivity)
  nlinarith [mul_le_mul_of_nonneg_right hr1 (abs_nonneg (((n-k : ℤ) : ℝ)))]

variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The literal printed double sum converges absolutely. -/
theorem summable_lemma34ProofTerm (hp : p ≠ ⊤) (φ f : Coeff p) (n : ℤ)
    {r : ℝ} (hr : 0 < r) (hr1 : r ≤ 1) : Summable (lemma34ProofTerm φ f n r) := by
  let : Fact (1 ≤ p.conjExponent) := ⟨ENNReal.HolderConjugate.one_le p.conjExponent p⟩
  let a : Coeff p.conjExponent := ⟨_, sourceLemma34_reciprocal_memlp hp n hr hr1⟩
  have ha (k : ℤ) : ‖a k‖ = (r+|((n-k : ℤ) : ℝ)|)⁻¹ := by
    change ‖((r+|((n-k : ℤ) : ℝ)| : ℝ) : ℂ)⁻¹‖ = _
    simp only [norm_inv, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (by positivity : 0 < r+|((n-k : ℤ) : ℝ)|)]
  let e := Equiv.prodCongr (Equiv.refl ℤ) (Equiv.neg ℤ)
  have h := e.summable_iff.mpr (Coeff.summable_sandwich_terms a φ
    (Coeff.reindex (Equiv.neg ℤ) a) (Coeff.reindex (Equiv.neg ℤ) f))
  apply h.congr
  intro lm
  change ‖a lm.1‖ * (‖φ (lm.1-(-lm.2))‖ *
    (‖a (-(-lm.2))‖ * ‖f (-(-lm.2))‖)) = _
  simp only [neg_neg, sub_neg_eq_add, ha, lemma34ProofTerm, div_eq_mul_inv, mul_inv]
  ring

omit [Fact (1 ≤ p)] in
/-- The printed factor-two majorant bounds each actual signed scalar term. -/
theorem norm_lemma34_signedTerm_le (φ f : Coeff p) {n l m : ℤ} {r : ℝ} {z : ℂ}
    (hr : 0 < r) (hrπ : r ≤ Real.pi/4) (hz : z ∈ verticalStrip n r) :
    ‖φ (l+m)*f m / ((z-(Real.pi : ℂ)*l)*(z-(Real.pi : ℂ)*m))‖ ≤
      2 * lemma34ProofTerm φ f n r (l,m) := by
  have hprod := sourceLemma34_denominator_product (l := l) (m := m) hr hrπ hz
  have hpos : 0 < (r+|((n-l : ℤ) : ℝ)|)*(r+|((n-m : ℤ) : ℝ)|)/2 := by positivity
  rw [norm_div, norm_mul, norm_mul]
  calc
    _ ≤ (‖φ (l+m)‖*‖f m‖) /
        ((r+|((n-l : ℤ) : ℝ)|)*(r+|((n-m : ℤ) : ℝ)|)/2) :=
      div_le_div_of_nonneg_left (by positivity) hpos (by nlinarith)
    _ = _ := by simp only [lemma34ProofTerm, div_div_eq_mul_div]; ring

/-- A signed coefficient formula gives the literal l1 double-sum majorization. -/
theorem norm_le_lemma34_absolute_sum (hp : p ≠ ⊤) (φ f : Coeff p) (g : Coeff 1)
    {n : ℤ} {r : ℝ} {z : ℂ} (hr : 0 < r) (hrπ : r ≤ Real.pi/4)
    (hz : z ∈ verticalStrip n r)
    (hg : ∀ l : ℤ, g l = ∑' m : ℤ, φ (l+m)*f m /
      ((z-(Real.pi : ℂ)*l)*(z-(Real.pi : ℂ)*m))) :
    ‖g‖ ≤ 2 * ∑' lm : ℤ × ℤ, lemma34ProofTerm φ f n r lm := by
  have hr1 : r ≤ 1 := by linarith [Real.pi_lt_four]
  have hs := summable_lemma34ProofTerm hp φ f n hr hr1
  have hrow (l : ℤ) : ‖g l‖ ≤ 2 * ∑' m : ℤ, lemma34ProofTerm φ f n r (l,m) := by
    have hmajor := (hs.prod_factor l).mul_left 2
    have hnorm : Summable (fun m : ℤ =>
        ‖φ (l+m)*f m / ((z-(Real.pi : ℂ)*l)*(z-(Real.pi : ℂ)*m))‖) :=
      hmajor.of_nonneg_of_le (fun _ => norm_nonneg _)
        (fun _ => norm_lemma34_signedTerm_le φ f hr hrπ hz)
    rw [hg l]
    calc
      _ ≤ ∑' m : ℤ, ‖φ (l+m)*f m /
          ((z-(Real.pi : ℂ)*l)*(z-(Real.pi : ℂ)*m))‖ := norm_tsum_le_tsum_norm hnorm
      _ ≤ ∑' m : ℤ, 2 * lemma34ProofTerm φ f n r (l,m) :=
        hnorm.tsum_le_tsum (fun _ => norm_lemma34_signedTerm_le φ f hr hrπ hz) hmajor
      _ = _ := tsum_mul_left
  have hsum := ((lp.memℓp g).norm.summable_of_one).tsum_le_tsum hrow (hs.prod.mul_left 2)
  have hgnorm : ∑' l : ℤ, ‖g l‖ = ‖g‖ := by
    simpa using (lp.hasSum_norm (p := 1) (by simp) g).tsum_eq
  rwa [hgnorm, tsum_mul_left, ← hs.tsum_prod] at hsum

/-- The first original component, with the raw first potential reflected into signed coordinates. -/
theorem norm_sourceDoubleResolvent_fst_le_absolute_sum (hp : p ≠ ⊤) (φ f : CoeffPair p)
    (z : ℂ) (hz0 : z ∉ freeLattice) {n : ℤ} {r : ℝ}
    (hr : 0 < r) (hrπ : r ≤ Real.pi/4) (hz : z ∈ verticalStrip n r) :
    ‖(sourceDoubleResolvent hp φ z hz0 f).fst‖ ≤
      2 * ∑' lm : ℤ × ℤ, lemma34ProofTerm (Coeff.reindex (Equiv.neg ℤ) φ.fst) f.snd n r lm := by
  have h := norm_le_lemma34_absolute_sum hp (Coeff.reindex (Equiv.neg ℤ) φ.fst) f.snd
    (Coeff.reindex (Equiv.neg ℤ) (sourceDoubleResolvent hp φ z hz0 f).fst) hr hrπ hz
    (fun l => sourceDoubleResolvent_signed_fst_apply hp φ f z hz0 l)
  simpa only [Coeff.norm_reindex] using h

/-- The second original component retains the reflected first input coefficient. -/
theorem norm_sourceDoubleResolvent_snd_le_absolute_sum (hp : p ≠ ⊤) (φ f : CoeffPair p)
    (z : ℂ) (hz0 : z ∉ freeLattice) {n : ℤ} {r : ℝ}
    (hr : 0 < r) (hrπ : r ≤ Real.pi/4) (hz : z ∈ verticalStrip n r) :
    ‖(sourceDoubleResolvent hp φ z hz0 f).snd‖ ≤
      2 * ∑' lm : ℤ × ℤ, lemma34ProofTerm φ.snd (Coeff.reindex (Equiv.neg ℤ) f.fst) n r lm :=
  norm_le_lemma34_absolute_sum hp φ.snd (Coeff.reindex (Equiv.neg ℤ) f.fst)
    (sourceDoubleResolvent hp φ z hz0 f).snd hr hrπ hz
    (fun l => sourceDoubleResolvent_signed_snd_apply hp φ f z hz0 l)

/-- The actual original l1 pair norm is bounded by the sum of its two signed majorants. -/
theorem norm_sourceDoubleResolvent_le_absolute_sums (hp : p ≠ ⊤) (φ f : CoeffPair p)
    (z : ℂ) (hz0 : z ∉ freeLattice) {n : ℤ} {r : ℝ}
    (hr : 0 < r) (hrπ : r ≤ Real.pi/4) (hz : z ∈ verticalStrip n r) :
    ‖sourceDoubleResolvent hp φ z hz0 f‖ ≤ 2 *
      ((∑' lm : ℤ × ℤ, lemma34ProofTerm (Coeff.reindex (Equiv.neg ℤ) φ.fst) f.snd n r lm) +
       ∑' lm : ℤ × ℤ, lemma34ProofTerm φ.snd (Coeff.reindex (Equiv.neg ℤ) f.fst) n r lm) := by
  have he : ‖sourceDoubleResolvent hp φ z hz0 f‖ =
      ‖(sourceDoubleResolvent hp φ z hz0 f).fst‖ + ‖(sourceDoubleResolvent hp φ z hz0 f).snd‖ := by
    simpa using WithLp.prod_norm_eq_add (by norm_num : 0 < (1 : ℝ≥0∞).toReal)
      (sourceDoubleResolvent hp φ z hz0 f)
  rw [he, mul_add]
  exact add_le_add (norm_sourceDoubleResolvent_fst_le_absolute_sum hp φ f z hz0 hr hrπ hz)
    (norm_sourceDoubleResolvent_snd_le_absolute_sum hp φ f z hz0 hr hrπ hz)

/-- The complement of the near set is exactly the printed far set. -/
theorem not_lemma34ProofNear_iff (n l m : ℤ) :
    ¬ lemma34ProofNear n l m ↔
      |(n : ℝ)|/2 < |((m-n : ℤ) : ℝ)| ∨ |(n : ℝ)|/2 < |((l-n : ℤ) : ℝ)| := by
  simp only [lemma34ProofNear, not_and_or, not_le]

/-- The convergent nonnegative double series splits exactly into the printed far and near sums. -/
theorem lemma34Proof_absolute_sum_eq_far_add_near (hp : p ≠ ⊤) (φ f : Coeff p) (n : ℤ)
    {r : ℝ} (hr : 0 < r) (hr1 : r ≤ 1) :
    (∑' lm : ℤ × ℤ, lemma34ProofTerm φ f n r lm) =
      lemma34ProofFarSum φ f n r + lemma34ProofNearSum φ f n r := by
  classical
  have hs := summable_lemma34ProofTerm hp φ f n hr hr1
  have hn (lm : ℤ × ℤ) : 0 ≤ lemma34ProofTerm φ f n r lm := by
    unfold lemma34ProofTerm
    positivity
  have hf : Summable (fun lm : ℤ × ℤ => if ¬ lemma34ProofNear n lm.1 lm.2 then
      lemma34ProofTerm φ f n r lm else 0) := by
    apply hs.of_nonneg_of_le
    · intro lm; split_ifs <;> first | exact hn lm | exact le_rfl
    · intro lm; split_ifs <;> simp only [le_refl, hn]
  have hnear : Summable (fun lm : ℤ × ℤ => if lemma34ProofNear n lm.1 lm.2 then
      lemma34ProofTerm φ f n r lm else 0) := by
    apply hs.of_nonneg_of_le
    · intro lm; split_ifs <;> first | exact hn lm | exact le_rfl
    · intro lm; split_ifs <;> simp only [le_refl, hn]
  rw [lemma34ProofFarSum, lemma34ProofNearSum, ← hf.tsum_add hnear]
  apply tsum_congr
  intro lm
  by_cases h : lemma34ProofNear n lm.1 lm.2 <;> simp [h]

/-- Near pairs only see potential frequencies at or beyond the symmetric tail cutoff. -/
theorem lemma34ProofNear_frequency_lower {n l m : ℤ} (h : lemma34ProofNear n l m) :
    |(n : ℝ)| ≤ |((l+m : ℤ) : ℝ)| := by
  have ht : |(2 : ℝ)*(n : ℝ)| ≤ |((l+m : ℤ) : ℝ)| +
      |((m-n : ℤ) : ℝ)| + |((l-n : ℤ) : ℝ)| := by
    calc
      _ = |(((l+m : ℤ) : ℝ)-((m-n : ℤ) : ℝ))-((l-n : ℤ) : ℝ)| := by
        congr 1
        push_cast
        ring
      _ ≤ |((l+m : ℤ) : ℝ)-((m-n : ℤ) : ℝ)| + |((l-n : ℤ) : ℝ)| := abs_sub _ _
      _ ≤ _ := add_le_add (abs_sub _ _) le_rfl
  rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)] at ht
  have hm := h.1
  have hl := h.2
  linarith

omit [Fact (1 ≤ p)] in
/-- The near region sees the exact symmetric Fourier remainder, including the cutoff boundary. -/
theorem lemma34ProofNear_tail_apply (φ : Coeff p) {n l m : ℤ}
    (h : lemma34ProofNear n l m) :
    Coeff.fourierTail n.natAbs φ (l+m) = φ (l+m) := by
  have hreal : (n.natAbs : ℝ) ≤ ((l+m).natAbs : ℝ) := by
    simpa only [Nat.cast_natAbs, Int.cast_abs] using lemma34ProofNear_frequency_lower h
  have hnat : n.natAbs ≤ (l+m).natAbs := by exact_mod_cast hreal
  simp [Coeff.fourierTail_apply, Nat.not_lt.mpr hnat]

omit [Fact (1 ≤ p)] in
/-- Replacing the potential by its source remainder leaves the near subsum unchanged. -/
theorem lemma34ProofNearSum_fourierTail (φ f : Coeff p) (n : ℤ) (r : ℝ) :
    lemma34ProofNearSum (Coeff.fourierTail n.natAbs φ) f n r = lemma34ProofNearSum φ f n r := by
  classical
  unfold lemma34ProofNearSum
  apply tsum_congr
  intro lm
  by_cases h : lemma34ProofNear n lm.1 lm.2
  · simp only [h, if_true, lemma34ProofTerm, lemma34ProofNear_tail_apply φ h]
  · simp only [h, if_false]

end NLS.ZakharovShabat
