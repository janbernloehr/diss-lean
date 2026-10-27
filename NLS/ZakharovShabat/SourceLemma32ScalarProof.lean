import NLS.ZakharovShabat.SourceFreeResolvent
import Mathlib.Analysis.MeanInequalitiesPow
import Mathlib.Analysis.Real.Pi.Bounds

/-! # The scalar calculations in the proof of Lemma 3.2

The signed component formulas, conjugate-power moments, centered denominator
geometry and numerical height calculation retain the source scalar norms.
Combining the two components still requires the previously established
original pair-norm correction in `SourceFreeResolvent`.
-/

noncomputable section
namespace NLS.ZakharovShabat

/-- The first literal Euclidean inequality in the proof of Lemma 3.2(ii). -/
theorem complex_norm_ge_l1_div_sqrt_two (z : ℂ) :
    (|z.re|+|z.im|)/Real.sqrt 2 ≤ ‖z‖ := by
  have hs : (|z.re|+|z.im|)^2 ≤ (Real.sqrt 2*‖z‖)^2 := by
    rw [mul_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
    have he : ‖z‖^2 = z.re^2+z.im^2 := by
      rw [Complex.sq_norm, Complex.normSq_apply]
      ring
    nlinarith [sq_nonneg (|z.re|-|z.im|), sq_abs z.re, sq_abs z.im]
  have h := (sq_le_sq₀ (by positivity) (by positivity)).mp hs
  exact (div_le_iff₀ (by positivity : 0 < Real.sqrt (2 : ℝ))).mpr (by nlinarith)

/-- The centered real part dominates the signed integer gap with the exact sqrt(2) factor. -/
theorem centered_real_gap_sqrt_two {z : ℂ} {n m : ℤ}
    (hc : |z.re-Real.pi*n| ≤ Real.pi/2) :
    Real.sqrt 2*|((n-m : ℤ) : ℝ)| ≤ |z.re-Real.pi*m| := by
  have hs : Real.sqrt (2 : ℝ) ≤ 3/2 := by
    nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2), Real.sqrt_nonneg (2 : ℝ)]
  by_cases hmn : m=n
  · subst m
    simp only [sub_self, Int.cast_zero, abs_zero, mul_zero]
    exact abs_nonneg _
  · have hd : 1 ≤ |((m-n : ℤ) : ℝ)| := by
      exact_mod_cast Int.one_le_abs (sub_ne_zero.mpr hmn)
    have ht : Real.pi*|((m-n : ℤ) : ℝ)| ≤
        |z.re-Real.pi*m|+|z.re-Real.pi*n| := by
      have h := abs_sub (z.re-Real.pi*m) (z.re-Real.pi*n)
      have he : (z.re-Real.pi*m)-(z.re-Real.pi*n) = -Real.pi*((m-n : ℤ) : ℝ) := by
        push_cast
        ring
      simpa only [he, abs_mul, abs_neg, abs_of_pos Real.pi_pos] using h
    have he : |((n-m : ℤ) : ℝ)| = |((m-n : ℤ) : ℝ)| := by
      push_cast
      exact abs_sub_comm _ _
    rw [he]
    have hm := mul_nonneg (show 0 ≤ Real.pi-3/2 by linarith [Real.pi_gt_three])
      (sub_nonneg.mpr hd)
    have hsd := mul_le_mul_of_nonneg_right hs (abs_nonneg (((m-n : ℤ) : ℝ)))
    nlinarith [Real.pi_gt_three]

/-- The second literal denominator lower bound, including the central index. -/
theorem centered_denominator_sqrt_two {z : ℂ} {n m : ℤ}
    (hc : |z.re-Real.pi*n| ≤ Real.pi/2) :
    |((n-m : ℤ) : ℝ)|+|z.im|/Real.sqrt 2 ≤ ‖z-(Real.pi : ℂ)*m‖ := by
  have h := complex_norm_ge_l1_div_sqrt_two (z-(Real.pi : ℂ)*m)
  have hg := centered_real_gap_sqrt_two (m := m) hc
  have hsq : 0 < Real.sqrt (2 : ℝ) := by positivity
  have hgap : |((n-m : ℤ) : ℝ)| ≤ |z.re-Real.pi*m|/Real.sqrt 2 :=
    (le_div_iff₀ hsq).mpr (by nlinarith)
  simp only [Complex.sub_re, Complex.mul_re, Complex.ofReal_re, Complex.intCast_re,
    Complex.ofReal_im, Complex.intCast_im, mul_zero, sub_zero, Complex.sub_im,
    Complex.mul_im, zero_mul, add_zero] at h
  rw [add_div] at h
  exact (add_le_add hgap (le_refl (|z.im|/Real.sqrt 2))).trans h


open Classical
open scoped ENNReal

/-- The exact punctured lattice estimate invoked between the two displays in Lemma 3.2. -/
theorem punctured_centered_reciprocal_sum {p q α : ℝ}
    (hpq : p.HolderConjugate q) (hα : 0 < α) (n : ℤ) :
    (∑' m : ℤ, if m=n then 0 else 1/(α+|((m-n : ℤ) : ℝ)|)^q) ≤
      2*p/α^(q-1) := by
  have he := (Equiv.subRight n).tsum_eq
    (fun m : ℤ => if m=0 then (0 : ℝ) else (α+|(m : ℝ)|)^(-q))
  simp only [Equiv.subRight_apply, sub_eq_zero] at he
  have hseries := ReciprocalSeries.tsum_int_shifted_rpow_le_integral hα hpq.symm.lt
  have hcoeff : 2/(q-1) ≤ 2*p := by
    apply (div_le_iff₀ hpq.symm.sub_one_pos).mpr
    nlinarith [hpq.symm.sub_one_mul_conj, hpq.symm.lt]
  calc
    _ = ∑' m : ℤ, if m=n then 0 else (α+|((m-n : ℤ) : ℝ)|)^(-q) := by
      apply tsum_congr
      intro m
      by_cases hm : m=n
      · simp only [hm, if_true]
      · simp only [hm, if_false, Real.rpow_neg (by positivity : 0 ≤ α+|((m-n : ℤ) : ℝ)|), one_div]
    _ = ∑' m : ℤ, if m=0 then 0 else (α+|(m : ℝ)|)^(-q) := he
    _ ≤ 2/(q-1)*α^(1-q) := hseries
    _ ≤ (2*p)*α^(1-q) := mul_le_mul_of_nonneg_right hcoeff (by positivity)
    _ = _ := by rw [show 1-q=-(q-1) by ring, Real.rpow_neg hα.le, div_eq_mul_inv]

variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The scalar reciprocal-symbol norm is the literal conjugate-power expression. -/
theorem scalarFreeL1Bound_moment (hp : p ≠ ⊤) (hp1 : 1 < p)
    (z : ℂ) (hz : z ∉ freeLattice) :
    scalarFreeL1Bound p hp z hz =
      (∑' m : ℤ, 1/‖z-(Real.pi : ℂ)*m‖^p.conjExponent.toReal)^(1/p.conjExponent.toReal) := by
  have hq : p.conjExponent ≠ ⊤ := ne_of_lt
    ((ENNReal.HolderConjugate.lt_top_iff_one_lt p.conjExponent p).mpr hp1)
  have hpq := ENNReal.HolderConjugate.toReal_of_ne_top hp hq
  rw [scalarFreeL1Bound, lp.norm_eq_tsum_rpow hpq.symm.pos]
  congr 1
  apply tsum_congr
  intro m
  change ‖(z-(Real.pi : ℂ)*m)⁻¹‖^p.conjExponent.toReal = _
  rw [norm_inv, Real.inv_rpow (norm_nonneg _), one_div]

/-- The actual reciprocal moment satisfies the first numerical height display. -/
theorem scalarFreeL1Bound_height_moment (hp : p ≠ ⊤) (hp1 : 1 < p)
    (z : ℂ) (hz : z ∉ freeLattice) (him : z.im ≠ 0) :
    scalarFreeL1Bound p hp z hz ≤
      (2*p.toReal/(|z.im|/Real.sqrt 2)^(p.conjExponent.toReal-1) +
        1/|z.im|^p.conjExponent.toReal)^(1/p.conjExponent.toReal) := by
  have hq : p.conjExponent ≠ ⊤ := ne_of_lt
    ((ENNReal.HolderConjugate.lt_top_iff_one_lt p.conjExponent p).mpr hp1)
  have hpq := ENNReal.HolderConjugate.toReal_of_ne_top hp hq
  have hi : 0 < |z.im| := abs_pos.mpr him
  let α := |z.im|/Real.sqrt 2
  have hα : 0 < α := by dsimp [α]; positivity
  obtain ⟨n,hn⟩ := exists_centered_real_part z
  let B (m : ℤ) := if m=n then (0 : ℝ) else (α+|((m-n : ℤ) : ℝ)|)^(-p.conjExponent.toReal)
  have hb : Summable B := by
    have h := (Equiv.subRight n).summable_iff.mpr
      (ReciprocalSeries.summable_int_shifted_rpow hα.le hpq.symm.lt)
    apply h.congr
    intro m
    change (if m-n=0 then 0 else (α+|((m-n : ℤ) : ℝ)|)^(-p.conjExponent.toReal)) = B m
    simp only [B, sub_eq_zero]
  let a := conjugateInverseSymbol p hp z hz
  have ha := (lp.memℓp a).summable hpq.symm.pos
  have ht : Summable (fun m : ℤ => if m=n then 1/|z.im|^p.conjExponent.toReal else 0) :=
    (hasSum_ite_eq n (1/|z.im|^p.conjExponent.toReal)).summable
  have hle (m : ℤ) : ‖a m‖^p.conjExponent.toReal ≤
      B m + (if m=n then 1/|z.im|^p.conjExponent.toReal else 0) := by
    change ‖(z-(Real.pi : ℂ)*m)⁻¹‖^p.conjExponent.toReal ≤ _
    rw [norm_inv, Real.inv_rpow (norm_nonneg _)]
    by_cases hm : m=n
    · simp only [B, hm, if_true, zero_add, one_div]
      apply inv_anti₀ (Real.rpow_pos_of_pos hi _)
      apply Real.rpow_le_rpow hi.le _ hpq.symm.pos.le
      simpa using Complex.abs_im_le_norm (z-(Real.pi : ℂ)*n)
    · simp only [B, hm, if_false, add_zero, Real.rpow_neg (by positivity : 0 ≤ α+|((m-n : ℤ) : ℝ)|)]
      apply inv_anti₀ (Real.rpow_pos_of_pos (by positivity) _)
      apply Real.rpow_le_rpow (by positivity) _ hpq.symm.pos.le
      have h := centered_denominator_sqrt_two (m := m) hn
      have he : |((n-m : ℤ) : ℝ)| = |((m-n : ℤ) : ℝ)| := by
        push_cast
        exact abs_sub_comm _ _
      rw [he] at h
      simpa only [α, add_comm] using h
  have hsum := ha.tsum_le_tsum hle (hb.add ht)
  rw [hb.tsum_add ht, tsum_ite_eq] at hsum
  have hbound : (∑' m : ℤ, B m) ≤ 2*p.toReal/α^(p.conjExponent.toReal-1) := by
    have h := punctured_centered_reciprocal_sum hpq hα n
    convert h using 1
    apply tsum_congr
    intro m
    by_cases hm : m=n
    · simp only [B, hm, if_true]
    · simp only [B, hm, if_false,
        Real.rpow_neg (by positivity : 0 ≤ α+|((m-n : ℤ) : ℝ)|), one_div]
  have htotal := hsum.trans (add_le_add hbound (le_refl (1/|z.im|^p.conjExponent.toReal)))
  change ‖a‖ ≤ _
  rw [lp.norm_eq_tsum_rpow hpq.symm.pos]
  exact Real.rpow_le_rpow (tsum_nonneg (fun _ => by positivity)) htotal (by positivity)

omit [Fact (1 ≤ p)] in
/-- The last scalar numerical comparison in Lemma 3.2(ii), with the printed constants. -/
theorem height_moment_numerical {p q h : ℝ}
    (hpq : p.HolderConjugate q) (hh : 0 < h) :
    (2*p/(h/Real.sqrt 2)^(q-1)+1/h^q)^(1/q) ≤ 4*p/h^(1/p)+1/h := by
  have hp : 0 < p := hpq.pos
  have hq : 0 < q := hpq.symm.pos
  have hqp : 1/q ≤ 1 := (div_le_one hq).mpr hpq.symm.lt.le
  have hpp : 1/p ≤ 1 := (div_le_one hp).mpr hpq.lt.le
  have hs : 0 < Real.sqrt (2 : ℝ) := by positivity
  have hs1 : 1 ≤ Real.sqrt (2 : ℝ) := by
    nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2), Real.sqrt_nonneg (2 : ℝ)]
  have hs2 : Real.sqrt (2 : ℝ) ≤ 2 := by
    nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2), Real.sqrt_nonneg (2 : ℝ)]
  have hexp : (q-1)*(1/q) = 1/p := by
    rw [← hpq.symm.div_conj_eq_sub_one]
    field_simp
  have hc : (2*p)^(1/q) ≤ 2*p := by
    simpa using Real.rpow_le_rpow_of_exponent_le (by linarith [hpq.lt] : 1 ≤ 2*p) hqp
  have hsroot : (Real.sqrt 2)^(1/p) ≤ 2 := by
    have h := Real.rpow_le_rpow_of_exponent_le hs1 hpp
    exact (by simpa using h : (Real.sqrt 2)^(1/p) ≤ Real.sqrt 2).trans hs2
  have hfirst : (2*p/(h/Real.sqrt 2)^(q-1))^(1/q) ≤ 4*p/h^(1/p) := by
    rw [Real.div_rpow (by positivity) (by positivity),
      ← Real.rpow_mul (by positivity : 0 ≤ h/Real.sqrt 2), hexp,
      Real.div_rpow hh.le hs.le, div_div_eq_mul_div]
    calc
      _ ≤ ((2*p)*2)/h^(1/p) := by
        gcongr
      _ = _ := by ring
  have hsecond : (1/h^q)^(1/q) = 1/h := by
    rw [one_div, Real.inv_rpow (by positivity), ← Real.rpow_mul hh.le,
      mul_one_div_cancel hq.ne', Real.rpow_one, one_div]
  calc
    _ ≤ (2*p/(h/Real.sqrt 2)^(q-1))^(1/q)+(1/h^q)^(1/q) :=
      Real.rpow_add_le_add_rpow (by positivity) (by positivity) (by positivity) hqp
    _ ≤ _ := by rw [hsecond]; exact add_le_add hfirst le_rfl

variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The first actual output in the signed coordinates used in Lemma 3.2. -/
theorem sourceFreeResolvent_signed_fst (hp : p ≠ ⊤)
    (z : ℂ) (hz : z ∉ freeLattice) (a : CoeffPair p) :
    Coeff.reindex (Equiv.neg ℤ) (sourceFreeResolventToL1 hp z hz a).fst =
      scalarResolventToL1 hp z hz (Coeff.reindex (Equiv.neg ℤ) a.fst) := by
  ext m
  simp only [Coeff.reindex_apply, Equiv.neg_apply,
    sourceFreeResolventToL1_fst_apply, scalarResolventToL1_apply,
    Int.cast_neg, mul_neg, sub_eq_add_neg]

/-- The second actual output already has the source denominator sign. -/
theorem sourceFreeResolvent_snd_scalar (hp : p ≠ ⊤)
    (z : ℂ) (hz : z ∉ freeLattice) (a : CoeffPair p) :
    (sourceFreeResolventToL1 hp z hz a).snd = scalarResolventToL1 hp z hz a.snd := by
  ext m
  rw [sourceFreeResolventToL1_snd_apply, scalarResolventToL1_apply]

/-- The literal absolute scalar sum is the actual l1 norm. -/
theorem scalarResolventToL1_norm_sum (hp : p ≠ ⊤)
    (z : ℂ) (hz : z ∉ freeLattice) (a : Coeff p) :
    ‖scalarResolventToL1 hp z hz a‖ = ∑' m : ℤ, ‖a m‖/‖z-(Real.pi : ℂ)*m‖ := by
  have h := (lp.hasSum_norm (p := 1) (by simp) (scalarResolventToL1 hp z hz a)).tsum_eq
  simp only [ENNReal.toReal_one, Real.rpow_one] at h
  rw [← h]
  apply tsum_congr
  intro m
  rw [scalarResolventToL1_apply, norm_div]

/-- Original first-component Holder bound after the signed reindexing. -/
theorem sourceFreeResolvent_fst_scalar_bound (hp : p ≠ ⊤)
    (z : ℂ) (hz : z ∉ freeLattice) (a : CoeffPair p) :
    ‖(sourceFreeResolventToL1 hp z hz a).fst‖ ≤ scalarFreeL1Bound p hp z hz * ‖a.fst‖ := by
  have h := norm_scalarResolventToL1_le hp z hz (Coeff.reindex (Equiv.neg ℤ) a.fst)
  rw [← sourceFreeResolvent_signed_fst hp z hz a] at h
  simpa only [Coeff.norm_reindex] using h

/-- Original second-component Holder bound. -/
theorem sourceFreeResolvent_snd_scalar_bound (hp : p ≠ ⊤)
    (z : ℂ) (hz : z ∉ freeLattice) (a : CoeffPair p) :
    ‖(sourceFreeResolventToL1 hp z hz a).snd‖ ≤ scalarFreeL1Bound p hp z hz * ‖a.snd‖ := by
  rw [sourceFreeResolvent_snd_scalar]
  exact norm_scalarResolventToL1_le hp z hz a.snd

/-- The conjugate-power reciprocal series in the source display converges. -/
theorem summable_scalarFreeL1Bound_moment (hp : p ≠ ⊤) (hp1 : 1 < p)
    (z : ℂ) (hz : z ∉ freeLattice) :
    Summable (fun m : ℤ => 1/‖z-(Real.pi : ℂ)*m‖^p.conjExponent.toReal) := by
  have hq : p.conjExponent ≠ ⊤ := ne_of_lt
    ((ENNReal.HolderConjugate.lt_top_iff_one_lt p.conjExponent p).mpr hp1)
  have hpq := ENNReal.HolderConjugate.toReal_of_ne_top hp hq
  apply ((lp.memℓp (conjugateInverseSymbol p hp z hz)).summable hpq.symm.pos).congr
  intro m
  change ‖(z-(Real.pi : ℂ)*m)⁻¹‖^p.conjExponent.toReal = _
  rw [norm_inv, Real.inv_rpow (norm_nonneg _), one_div]

/-- The first component's exact l1 sum uses the reflected input frequencies. -/
theorem sourceFreeResolvent_fst_norm_sum (hp : p ≠ ⊤)
    (z : ℂ) (hz : z ∉ freeLattice) (a : CoeffPair p) :
    ‖(sourceFreeResolventToL1 hp z hz a).fst‖ =
      ∑' m : ℤ, ‖a.fst (-m)‖/‖z-(Real.pi : ℂ)*m‖ := by
  have h := scalarResolventToL1_norm_sum hp z hz (Coeff.reindex (Equiv.neg ℤ) a.fst)
  rw [← sourceFreeResolvent_signed_fst hp z hz a] at h
  simpa only [Coeff.norm_reindex, Coeff.reindex_apply, Equiv.neg_apply] using h

/-- The second component's exact l1 sum retains the input frequencies. -/
theorem sourceFreeResolvent_snd_norm_sum (hp : p ≠ ⊤)
    (z : ℂ) (hz : z ∉ freeLattice) (a : CoeffPair p) :
    ‖(sourceFreeResolventToL1 hp z hz a).snd‖ =
      ∑' m : ℤ, ‖a.snd m‖/‖z-(Real.pi : ℂ)*m‖ := by
  rw [sourceFreeResolvent_snd_scalar]
  exact scalarResolventToL1_norm_sum hp z hz a.snd

/-- The literal first-component Holder display in the original scalar norms. -/
theorem sourceFreeResolvent_fst_le_moment (hp : p ≠ ⊤) (hp1 : 1 < p)
    (z : ℂ) (hz : z ∉ freeLattice) (a : CoeffPair p) :
    ‖(sourceFreeResolventToL1 hp z hz a).fst‖ ≤
      (∑' m : ℤ, 1/‖z-(Real.pi : ℂ)*m‖^p.conjExponent.toReal)^(1/p.conjExponent.toReal) * ‖a.fst‖ := by
  rw [← scalarFreeL1Bound_moment hp hp1 z hz]
  exact sourceFreeResolvent_fst_scalar_bound hp z hz a

/-- The literal second-component Holder display in the original scalar norms. -/
theorem sourceFreeResolvent_snd_le_moment (hp : p ≠ ⊤) (hp1 : 1 < p)
    (z : ℂ) (hz : z ∉ freeLattice) (a : CoeffPair p) :
    ‖(sourceFreeResolventToL1 hp z hz a).snd‖ ≤
      (∑' m : ℤ, 1/‖z-(Real.pi : ℂ)*m‖^p.conjExponent.toReal)^(1/p.conjExponent.toReal) * ‖a.snd‖ := by
  rw [← scalarFreeL1Bound_moment hp hp1 z hz]
  exact sourceFreeResolvent_snd_scalar_bound hp z hz a

/-- The two literal height comparisons, as one chain for the actual scalar symbol. -/
theorem scalarFreeL1Bound_height_moment_chain (hp : p ≠ ⊤) (hp1 : 1 < p)
    (z : ℂ) (hz : z ∉ freeLattice) (him : z.im ≠ 0) :
    scalarFreeL1Bound p hp z hz ≤
      (2*p.toReal/(|z.im|/Real.sqrt 2)^(p.conjExponent.toReal-1) +
        1/|z.im|^p.conjExponent.toReal)^(1/p.conjExponent.toReal) ∧
    (2*p.toReal/(|z.im|/Real.sqrt 2)^(p.conjExponent.toReal-1) +
        1/|z.im|^p.conjExponent.toReal)^(1/p.conjExponent.toReal) ≤
      4*p.toReal/|z.im|^(1/p.toReal)+1/|z.im| := by
  have hq : p.conjExponent ≠ ⊤ := ne_of_lt
    ((ENNReal.HolderConjugate.lt_top_iff_one_lt p.conjExponent p).mpr hp1)
  exact ⟨scalarFreeL1Bound_height_moment hp hp1 z hz him,
    height_moment_numerical (ENNReal.HolderConjugate.toReal_of_ne_top hp hq) (abs_pos.mpr him)⟩

/-- The printed scalar strip moment bound, with its exact constant four. -/
theorem scalarFreeL1Bound_moment_le_verticalStrip (hp : p ≠ ⊤) (hp1 : 1 < p)
    (z : ℂ) (hz0 : z ∉ freeLattice) {n : ℤ} {r : ℝ}
    (hr : 0 < r) (hrπ : r ≤ Real.pi/4) (hz : z ∈ verticalStrip n r) :
    (∑' m : ℤ, 1/‖z-(Real.pi : ℂ)*m‖^p.conjExponent.toReal)^(1/p.conjExponent.toReal) ≤
      4*p.toReal/r := by
  rw [← scalarFreeL1Bound_moment hp hp1 z hz0]
  have h := (scalarFreeL1Bound_le_verticalStrip hp z hz0 hr hrπ hz).trans
    (div_le_div_of_nonneg_right (WeightedCoeff.sobolevEmbeddingConstant_le_two_mul p hp) hr.le)
  apply h.trans
  gcongr
  norm_num

end NLS.ZakharovShabat
