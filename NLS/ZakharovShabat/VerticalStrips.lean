import NLS.ZakharovShabat.ResolventAnalytic
import NLS.SequenceSpaces.SobolevConstant
import NLS.ZakharovShabat.PeriodicSpectrum
import Mathlib.Algebra.Order.Round

/-!
# Resolvent bounds in punctured vertical strips

The regions `Vertₙ(r)` from Chapter 1, Section 3 have half-width `π/2`
and omit the open disk of radius `r` around `πn`. Reciprocal-denominator
geometry and Appendix B.1 yield the numerical bound of Lemma 3.2(iii).
All pair-operator norms here use the library's maximum norm.
-/

noncomputable section
open Complex
open scoped ENNReal

namespace NLS.ZakharovShabat

/-- A vertical strip with an open disk removed around its free spectral value. -/
def verticalStrip (n : ℤ) (r : ℝ) : Set ℂ :=
  {z | |z.re - Real.pi * n| ≤ Real.pi / 2 ∧ r ≤ ‖z - (Real.pi : ℂ) * n‖}

/-- Within a punctured strip, all free denominators dominate the reciprocal-weight scale. -/
theorem verticalStrip_denominator_lower {n m : ℤ} {r : ℝ} {z : ℂ}
    (hr : 0 < r) (hrπ : r ≤ Real.pi / 4) (hz : z ∈ verticalStrip n r) :
    r * (1 + |((m - n : ℤ) : ℝ)|) ≤ ‖z - (Real.pi : ℂ) * m‖ := by
  by_cases hmn : m = n
  · subst m
    simpa using hz.2
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
    have hmul := mul_le_mul_of_nonneg_right hrπ
      (by positivity : 0 ≤ 1 + |((m - n : ℤ) : ℝ)|)
    nlinarith [hz.1, Real.pi_pos]

/-- Positive-radius strips of the stated width avoid the entire free lattice. -/
theorem notMem_freeLattice_of_mem_verticalStrip {n : ℤ} {r : ℝ} {z : ℂ}
    (hr : 0 < r) (hrπ : r ≤ Real.pi / 4) (hz : z ∈ verticalStrip n r) :
    z ∉ freeLattice := by
  rintro ⟨m, rfl⟩
  have h := verticalStrip_denominator_lower (m := m) hr hrπ hz
  simp only [sub_self, norm_zero] at h
  have : 0 < r * (1 + |((m - n : ℤ) : ℝ)|) := by positivity
  linarith

/-- Pointwise reciprocal bounds uniform throughout a punctured strip. -/
theorem verticalStrip_inverse_bound {n m : ℤ} {r : ℝ} {z : ℂ}
    (hr : 0 < r) (hrπ : r ≤ Real.pi / 4) (hz : z ∈ verticalStrip n r) :
    ‖(z - (Real.pi : ℂ) * m)⁻¹‖ ≤ r⁻¹ * (1 + |((m - n : ℤ) : ℝ)|)⁻¹ := by
  rw [norm_inv, ← mul_inv]
  exact inv_anti₀ (by positivity) (verticalStrip_denominator_lower hr hrπ hz)

/-- Reflection sends the strip around `n` to the strip around `-n`. -/
theorem neg_mem_verticalStrip {n : ℤ} {r : ℝ} {z : ℂ}
    (hz : z ∈ verticalStrip n r) : -z ∈ verticalStrip (-n) r := by
  constructor
  · have he : (-z).re - Real.pi * (-n : ℤ) = -(z.re - Real.pi * n) := by
      simp only [neg_re, Int.cast_neg]
      ring
    simpa only [he, abs_neg] using hz.1
  · have he : -z - (Real.pi : ℂ) * (-n : ℤ) = -(z - (Real.pi : ℂ) * n) := by
      push_cast
      ring
    simpa only [he, norm_neg] using hz.2

variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The scalar reciprocal-symbol norm on a strip is controlled by the inverse Sobolev weight. -/
theorem scalarFreeL1Bound_le_verticalStrip (hp : p ≠ ⊤) (z : ℂ) (hz0 : z ∉ freeLattice)
    {n : ℤ} {r : ℝ} (hr : 0 < r) (hrπ : r ≤ Real.pi / 4) (hz : z ∈ verticalStrip n r) :
    scalarFreeL1Bound p hp z hz0 ≤ WeightedCoeff.sobolevEmbeddingConstant p hp / r := by
  let : Fact (1 ≤ p.conjExponent) := ⟨ENNReal.HolderConjugate.one_le p.conjExponent p⟩
  let b : Coeff p.conjExponent := WeightedCoeff.inverseWeight (Weight.sobolev 1)
    (Weight.inverse_sobolev_one_memlp
      ((ENNReal.HolderConjugate.lt_top_iff_one_lt p p.conjExponent).mp hp.lt_top))
  have hnorm (k : ℤ) : ‖b k‖ = (1 + |(k : ℝ)|)⁻¹ := by
    change ‖(Weight.sobolev 1 k : ℂ)⁻¹‖ = _
    simp only [Weight.sobolev_apply, Real.rpow_one, norm_inv, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos (by positivity : 0 < 1 + |(k : ℝ)|)]
  have hcmp : ‖Coeff.reindex (Equiv.addRight n) (conjugateInverseSymbol p hp z hz0)‖ ≤
      ‖((r : ℂ)⁻¹) • b‖ := by
    apply lp.norm_mono (ne_of_gt (zero_lt_one.trans_le
      (ENNReal.HolderConjugate.one_le p.conjExponent p)))
    intro k
    change ‖(z - (Real.pi : ℂ) * (k + n : ℤ))⁻¹‖ ≤ ‖(r : ℂ)⁻¹ * b k‖
    rw [norm_mul, norm_inv, norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr, hnorm]
    simpa only [add_sub_cancel_right, norm_inv] using
      (verticalStrip_inverse_bound (m := k + n) hr hrπ hz)
  rw [Coeff.norm_reindex, norm_smul, norm_inv, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos hr] at hcmp
  change scalarFreeL1Bound p hp z hz0 ≤
    r⁻¹ * WeightedCoeff.sobolevEmbeddingConstant p hp at hcmp
  simpa only [div_eq_mul_inv, mul_comm] using hcmp

/-- Uniform `2p/r` bound for the pair reciprocal-symbol norm, with the maximum pair norm. -/
theorem freeL1Bound_le_verticalStrip (hp : p ≠ ⊤) (z : ℂ) (hz0 : z ∉ freeLattice)
    {n : ℤ} {r : ℝ} (hr : 0 < r) (hrπ : r ≤ Real.pi / 4) (hz : z ∈ verticalStrip n r) :
    freeL1Bound p hp z hz0 ≤ 2 * p.toReal / r := by
  have hs : freeL1Bound p hp z hz0 ≤ WeightedCoeff.sobolevEmbeddingConstant p hp / r := by
    apply max_le
    · exact scalarFreeL1Bound_le_verticalStrip hp (-z) (neg_notMem_freeLattice hz0)
        hr hrπ (neg_mem_verticalStrip hz)
    · exact scalarFreeL1Bound_le_verticalStrip hp z hz0 hr hrπ hz
  exact hs.trans (div_le_div_of_nonneg_right
    (WeightedCoeff.sobolevEmbeddingConstant_le_two_mul p hp) hr.le)

/-- Chapter 1, Lemma 3.2(iii): the `8p/r` operator bound on punctured vertical strips. -/
theorem norm_freeResolventToL1_le_verticalStrip (hp : p ≠ ⊤) (z : ℂ) (hz0 : z ∉ freeLattice)
    {n : ℤ} {r : ℝ} (hr : 0 < r) (hrπ : r ≤ Real.pi / 4) (hz : z ∈ verticalStrip n r) :
    ‖freeResolventToL1 hp z hz0‖ ≤ 8 * p.toReal / r := by
  apply (norm_freeResolventToL1_le hp z hz0).trans
  apply (freeL1Bound_le_verticalStrip hp z hz0 hr hrπ hz).trans
  apply div_le_div_of_nonneg_right _ hr.le
  nlinarith [ENNReal.toReal_nonneg (a := p)]

/-- The quantitative strip estimate supplies a sufficient Neumann condition. -/
theorem neumannCondition_of_mem_verticalStrip (hp : p ≠ ⊤) (φ : PairSpace p)
    (z : ℂ) (hz0 : z ∉ freeLattice) {n : ℤ} {r : ℝ}
    (hr : 0 < r) (hrπ : r ≤ Real.pi / 4) (hz : z ∈ verticalStrip n r)
    (hφ : 2 * p.toReal * ‖φ‖ < r) : NeumannCondition hp φ z hz0 := by
  apply (mul_le_mul_of_nonneg_right (freeL1Bound_le_verticalStrip hp z hz0 hr hrπ hz)
    (norm_nonneg φ)).trans_lt
  change 2 * p.toReal / r * ‖φ‖ < 1
  rw [div_mul_eq_mul_div, div_lt_one hr]
  exact hφ

/-- Small potentials have no spectrum anywhere in a punctured strip. -/
theorem mem_resolventSet_of_mem_verticalStrip (hp : p ≠ ⊤) (φ : PairSpace p)
    {n : ℤ} {r : ℝ} {z : ℂ} (hr : 0 < r) (hrπ : r ≤ Real.pi / 4)
    (hz : z ∈ verticalStrip n r) (hφ : 2 * p.toReal * ‖φ‖ < r) : z ∈ resolventSet hp φ := by
  have hz0 := notMem_freeLattice_of_mem_verticalStrip hr hrπ hz
  exact mem_resolventSet_of_neumannCondition hp φ z hz0
    (neumannCondition_of_mem_verticalStrip hp φ z hz0 hr hrπ hz hφ)

/-- The boundary circle of the omitted disk lies in its vertical strip. -/
theorem sphere_subset_verticalStrip (n : ℤ) {r : ℝ} (hrπ : r ≤ Real.pi / 4) :
    Metric.sphere ((Real.pi : ℂ) * n) r ⊆ verticalStrip n r := by
  intro z hz
  have hd : ‖z - (Real.pi : ℂ) * n‖ = r := by
    simpa only [Metric.mem_sphere, dist_eq_norm] using hz
  constructor
  · have hre : |z.re - Real.pi * n| ≤ ‖z - (Real.pi : ℂ) * n‖ := by
      simpa using Complex.abs_re_le_norm (z - (Real.pi : ℂ) * n)
    nlinarith [Real.pi_pos]
  · exact hd.ge

/-- The spectral circles around every free eigenvalue are valid for a common small-potential ball. -/
theorem sphere_subset_resolventSet_of_smallPotential (hp : p ≠ ⊤) (φ : PairSpace p)
    (n : ℤ) {r : ℝ} (hr : 0 < r) (hrπ : r ≤ Real.pi / 4)
    (hφ : 2 * p.toReal * ‖φ‖ < r) :
    Metric.sphere ((Real.pi : ℂ) * n) r ⊆ resolventSet hp φ := by
  intro z hz
  exact mem_resolventSet_of_mem_verticalStrip hp φ hr hrπ
    (sphere_subset_verticalStrip n hrπ hz) hφ

/-- Every spectral parameter lies over a nearest free Fourier frequency. -/
theorem exists_centered_real_part (z : ℂ) :
    ∃ n : ℤ, |z.re - Real.pi * n| ≤ Real.pi / 2 := by
  refine ⟨round (z.re / Real.pi), ?_⟩
  calc
    |z.re - Real.pi * (round (z.re / Real.pi) : ℝ)| =
        |Real.pi * (z.re / Real.pi - (round (z.re / Real.pi) : ℝ))| := by
      congr 1
      field_simp
    _ = Real.pi * |z.re / Real.pi - (round (z.re / Real.pi) : ℝ)| := by
      rw [abs_mul, abs_of_pos Real.pi_pos]
    _ ≤ Real.pi * (1 / 2) := mul_le_mul_of_nonneg_left (abs_sub_round _) Real.pi_pos.le
    _ = Real.pi / 2 := by ring

/-- For small potentials the entire spectrum lies in the union of disks around the free lattice. -/
theorem periodicSpectrum_subset_disks_of_smallPotential (hp : p ≠ ⊤) (φ : PairSpace p)
    {r : ℝ} (hr : 0 < r) (hrπ : r ≤ Real.pi / 4) (hφ : 2 * p.toReal * ‖φ‖ < r) :
    periodicSpectrum hp φ ⊆ ⋃ n : ℤ, Metric.ball ((Real.pi : ℂ) * n) r := by
  intro z hz
  obtain ⟨n, hn⟩ := exists_centered_real_part z
  by_contra hnot
  have hnball : z ∉ Metric.ball ((Real.pi : ℂ) * n) r := by
    intro h
    exact hnot (Set.mem_iUnion.mpr ⟨n, h⟩)
  have hdist : r ≤ ‖z - (Real.pi : ℂ) * n‖ := by
    simpa only [Metric.mem_ball, dist_eq_norm, not_lt] using hnball
  exact hz (mem_resolventSet_of_mem_verticalStrip hp φ hr hrπ ⟨hn, hdist⟩ hφ)

end NLS.ZakharovShabat
