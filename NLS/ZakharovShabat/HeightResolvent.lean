import NLS.ZakharovShabat.VerticalStrips
import NLS.SequenceSpaces.ReciprocalNorm

/-!
# Numerical high-imaginary-part resolvent estimates

Chapter 1, Lemma 3.2(ii) bounds the free `FL^p → FL^1` resolvent by
`4p / |Im z|^(1/p) + 1 / |Im z|`. The imaginary part is explicitly nonzero,
so the divisions in this finite bound are meaningful. The resulting numerical
Neumann region gives the compact analytic resolvent of Corollary 3.3.
-/

noncomputable section
open Complex Filter Topology
open scoped ENNReal

namespace NLS.ZakharovShabat

/-- Away from the central frequency, a centered free denominator dominates the frequency gap. -/
theorem centered_denominator_ge_frequency {z : ℂ} {n m : ℤ}
    (hc : |z.re - Real.pi * n| ≤ Real.pi / 2) (hmn : m ≠ n) :
    |((m - n : ℤ) : ℝ)| ≤ ‖z - (Real.pi : ℂ) * m‖ := by
  have habs : 1 ≤ |((m - n : ℤ) : ℝ)| := by
    exact_mod_cast Int.one_le_abs (sub_ne_zero.mpr hmn)
  have htri : Real.pi * |((m - n : ℤ) : ℝ)| ≤
      |z.re - Real.pi * m| + |z.re - Real.pi * n| := by
    have h := norm_sub_le (z.re - Real.pi * m) (z.re - Real.pi * n)
    have he : (z.re - Real.pi * m) - (z.re - Real.pi * n) =
        -Real.pi * ((m - n : ℤ) : ℝ) := by push_cast; ring
    simpa only [he, norm_mul, norm_neg, Real.norm_eq_abs, abs_of_pos Real.pi_pos] using h
  have hre : |z.re - Real.pi * m| ≤ ‖z - (Real.pi : ℂ) * m‖ := by
    simpa using Complex.abs_re_le_norm (z - (Real.pi : ℂ) * m)
  have hπ : 2 ≤ Real.pi := by linarith [Real.one_le_pi_div_two]
  have hprod : 0 ≤ (Real.pi - 1) * (|((m - n : ℤ) : ℝ)| - 1) :=
    mul_nonneg (by linarith) (by linarith)
  nlinarith

/-- A pointwise reciprocal bound combining the height and frequency separation. -/
theorem centered_inverse_height_bound {z : ℂ} {n m : ℤ} (him : z.im ≠ 0)
    (hc : |z.re - Real.pi * n| ≤ Real.pi / 2) (hmn : m ≠ n) :
    ‖(z - (Real.pi : ℂ) * m)⁻¹‖ ≤ 2 / (|z.im| + |((m - n : ℤ) : ℝ)|) := by
  have hi : |z.im| ≤ ‖z - (Real.pi : ℂ) * m‖ := by
    simpa using Complex.abs_im_le_norm (z - (Real.pi : ℂ) * m)
  have hf := centered_denominator_ge_frequency hc hmn
  have hh := abs_pos.mpr him
  rw [norm_inv, inv_eq_one_div]
  apply (div_le_div_iff₀ (hh.trans_le hi) (by positivity)).mpr
  linarith

variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- Explicit height decay of the scalar reciprocal-symbol norm. -/
theorem scalarFreeL1Bound_le_height (hp : p ≠ ⊤) (z : ℂ) (hz : z ∉ freeLattice)
    (him : z.im ≠ 0) :
    scalarFreeL1Bound p hp z hz ≤ 4 * p.toReal / |z.im| ^ (1 / p.toReal) + |z.im|⁻¹ := by
  by_cases hp1 : p = 1
  · subst p
    have h := scalarFreeL1Bound_one_le z hz him
    simp only [ENNReal.toReal_one, mul_one, div_one, Real.rpow_one]
    have hpos : 0 ≤ 4 / |z.im| := by positivity
    linarith
  · let : Fact (1 ≤ p.conjExponent) := ⟨ENNReal.HolderConjugate.one_le p.conjExponent p⟩
    have hpg : 1 < p := lt_of_le_of_ne Fact.out (Ne.symm hp1)
    have hq : p.conjExponent ≠ ⊤ := ne_of_lt
      ((ENNReal.HolderConjugate.lt_top_iff_one_lt p.conjExponent p).mpr hpg)
    have hpq := ENNReal.HolderConjugate.toReal_of_ne_top hp hq
    obtain ⟨n, hn⟩ := exists_centered_real_part z
    let a : Coeff p.conjExponent := Coeff.reindex (Equiv.addRight n) (conjugateInverseSymbol p hp z hz)
    have ha0 : ‖a 0‖ ≤ |z.im|⁻¹ := by
      change ‖(z - (Real.pi : ℂ) * (0 + n : ℤ))⁻¹‖ ≤ _
      rw [norm_inv]
      apply inv_anti₀ (abs_pos.mpr him)
      simpa using Complex.abs_im_le_norm (z - (Real.pi : ℂ) * (0 + n : ℤ))
    have ha : ∀ k : ℤ, k ≠ 0 → ‖a k‖ ≤ 2 / (|z.im| + |(k : ℝ)|) := by
      intro k hk
      change ‖(z - (Real.pi : ℂ) * (k + n : ℤ))⁻¹‖ ≤ _
      simpa only [add_sub_cancel_right] using
        (centered_inverse_height_bound (m := k + n) him hn (by omega))
    have h := Coeff.norm_reciprocal_le hpq (abs_pos.mpr him) a ha0 ha
    change ‖Coeff.reindex (Equiv.addRight n) (conjugateInverseSymbol p hp z hz)‖ ≤ _ at h
    rwa [Coeff.norm_reindex] at h

/-- The pair reciprocal-symbol bound has the same height-decay rate. -/
theorem freeL1Bound_le_height (hp : p ≠ ⊤) (z : ℂ) (hz : z ∉ freeLattice)
    (him : z.im ≠ 0) :
    freeL1Bound p hp z hz ≤ 4 * p.toReal / |z.im| ^ (1 / p.toReal) + |z.im|⁻¹ := by
  apply max_le
  · simpa only [neg_im, abs_neg] using
      scalarFreeL1Bound_le_height hp (-z) (neg_notMem_freeLattice hz) (by simpa using him)
  · exact scalarFreeL1Bound_le_height hp z hz him

/-- Chapter 1, Lemma 3.2(ii), in the library's maximum norm on pairs. -/
theorem norm_freeResolventToL1_le_height (hp : p ≠ ⊤) (z : ℂ) (hz : z ∉ freeLattice)
    (him : z.im ≠ 0) :
    ‖freeResolventToL1 hp z hz‖ ≤ 4 * p.toReal / |z.im| ^ (1 / p.toReal) + 1 / |z.im| := by
  simpa only [one_div] using (norm_freeResolventToL1_le hp z hz).trans
    (freeL1Bound_le_height hp z hz him)

/-- The numerical Neumann region in Chapter 1, Corollary 3.3. -/
def heightNeumannRegion (φ : PairSpace p) : Set ℂ :=
  {z | z.im ≠ 0 ∧ (4 * p.toReal / |z.im| ^ (1 / p.toReal) + 1 / |z.im|) * ‖φ‖ < 1}

/-- One numerical height condition controls all larger imaginary parts, of either sign. -/
theorem mem_heightNeumannRegion_of_height_le (hp : p ≠ ⊤) (φ : PairSpace p)
    {H : ℝ} (hH : 0 < H)
    (hφ : (4 * p.toReal / H ^ (1 / p.toReal) + 1 / H) * ‖φ‖ < 1)
    {z : ℂ} (hz : H ≤ |z.im|) : z ∈ heightNeumannRegion φ := by
  have hpos : 0 < p.toReal := ENNReal.toReal_pos
    (ne_of_gt (zero_lt_one.trans_le (show 1 ≤ p from Fact.out))) hp
  refine ⟨abs_pos.mp (hH.trans_le hz), ?_⟩
  apply lt_of_le_of_lt _ hφ
  gcongr

/-- The numerical height bound tends to zero for every finite Banach exponent. -/
theorem tendsto_freeL1_heightBound_zero (hp : p ≠ ⊤) :
    Tendsto (fun H : ℝ => 4 * p.toReal / H ^ (1 / p.toReal) + 1 / H) atTop (𝓝 0) := by
  have hpos : 0 < p.toReal := ENNReal.toReal_pos
    (ne_of_gt (zero_lt_one.trans_le (show 1 ≤ p from Fact.out))) hp
  have hr := tendsto_rpow_atTop (by positivity : 0 < 1 / p.toReal)
  have hfirst : Tendsto (fun H : ℝ => 4 * p.toReal / H ^ (1 / p.toReal)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop hr
  simpa only [one_div, zero_add] using hfirst.add tendsto_inv_atTop_zero

/-- A common numerical height works on any fixed norm ball of potentials. -/
theorem exists_uniform_heightNeumannRegion (hp : p ≠ ⊤) (M : ℝ) :
    ∃ H : ℝ, 0 < H ∧ ∀ φ : PairSpace p, ‖φ‖ ≤ M →
      ∀ z : ℂ, H ≤ |z.im| → z ∈ heightNeumannRegion φ := by
  have ht : Tendsto (fun H : ℝ =>
      (4 * p.toReal / H ^ (1 / p.toReal) + 1 / H) * M) atTop (𝓝 0) := by
    simpa only [zero_mul] using (tendsto_freeL1_heightBound_zero hp).mul_const M
  obtain ⟨H, hH, hsmall⟩ := ((eventually_gt_atTop (0 : ℝ)).and
    (ht.eventually_lt_const zero_lt_one)).exists
  refine ⟨H, hH, fun φ hφ z hz => mem_heightNeumannRegion_of_height_le hp φ hH ?_ hz⟩
  exact (mul_le_mul_of_nonneg_left hφ (by positivity)).trans_lt hsmall

/-- In particular the quantitative region is nonempty for every potential. -/
theorem heightNeumannRegion_nonempty (hp : p ≠ ⊤) (φ : PairSpace p) :
    (heightNeumannRegion φ).Nonempty := by
  obtain ⟨H, hH, h⟩ := exists_uniform_heightNeumannRegion hp ‖φ‖
  refine ⟨(H : ℂ) * I, h φ le_rfl _ ?_⟩
  simp [abs_of_pos hH]

/-- The height-decay bound implies the constructive Neumann condition. -/
theorem neumannCondition_of_heightBound (hp : p ≠ ⊤) (φ : PairSpace p)
    (z : ℂ) (hz : z ∉ freeLattice) (him : z.im ≠ 0)
    (hφ : (4 * p.toReal / |z.im| ^ (1 / p.toReal) + 1 / |z.im|) * ‖φ‖ < 1) :
    NeumannCondition hp φ z hz := by
  apply (mul_le_mul_of_nonneg_right (freeL1Bound_le_height hp z hz him) (norm_nonneg φ)).trans_lt
  simpa only [one_div] using hφ

/-- Every parameter in the explicit numerical region lies in the full resolvent set. -/
theorem heightNeumannRegion_subset_resolventSet (hp : p ≠ ⊤) (φ : PairSpace p) :
    heightNeumannRegion φ ⊆ resolventSet hp φ := by
  intro z hz
  have hz0 := notMem_freeLattice_of_im_ne_zero hz.1
  exact mem_resolventSet_of_neumannCondition hp φ z hz0
    (neumannCondition_of_heightBound hp φ z hz0 hz.1 hz.2)

/-- Corollary 3.3: the resolvent is analytic on the quantitative high-height region. -/
theorem analyticOnNhd_resolvent_heightRegion (hp : p ≠ ⊤) (φ : PairSpace p) :
    AnalyticOnNhd ℂ (resolvent hp φ) (heightNeumannRegion φ) :=
  (analyticOnNhd_resolvent hp φ).mono (heightNeumannRegion_subset_resolventSet hp φ)

/-- The full resolvent agrees with the constructed Neumann inverse on the numerical region. -/
theorem resolvent_eq_perturbed_of_heightBound (hp : p ≠ ⊤) (φ : PairSpace p)
    (z : ℂ) (hz : z ∈ heightNeumannRegion φ) :
    resolvent hp φ z = perturbedResolvent hp φ z (notMem_freeLattice_of_im_ne_zero hz.1)
      (neumannCondition_of_heightBound hp φ z _ hz.1 hz.2) :=
  resolvent_eq_perturbed hp φ z _ _

end NLS.ZakharovShabat
