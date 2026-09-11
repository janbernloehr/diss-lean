import NLS.ZakharovShabat.PerturbedResolvent
import NLS.SequenceSpaces.DominatedConvergence
import Mathlib.Algebra.Order.Floor.Ring

/-!
# Uniform high-imaginary-part resolvent bounds

After shifting the real part into a fundamental interval, reciprocal symbols
are bounded by `min (1 / (N + 1)) (3 / (1 + |n|))` when `|Im z| ≥ N + 1`.
The majorant tends to zero in every conjugate space relevant to finite `p`.
These qualitative uniform estimates give nonempty Neumann regions for all
potentials; the sharper numerical rates of Lemma 3.2(ii–iii) remain separate.
-/

open scoped ENNReal
open Filter
noncomputable section

namespace NLS.ZakharovShabat

private def envelope (N : ℕ) (n : ℤ) : ℝ :=
  min ((N + 1 : ℝ)⁻¹) (3 / (1 + |(n : ℝ)|))

private theorem envelope_nonneg (N : ℕ) (n : ℤ) : 0 ≤ envelope N n := by
  unfold envelope
  positivity

private theorem norm_inverse_weight (n : ℤ) :
    ‖(Weight.sobolev 1 n : ℂ)⁻¹‖ = (1 + |(n : ℝ)|)⁻¹ := by
  simp only [norm_inv, Complex.norm_real, Real.norm_eq_abs, Weight.sobolev_apply,
    Real.rpow_one, abs_of_pos (by positivity : 0 < 1 + |(n : ℝ)|)]

/-- An `lq` envelope for centered reciprocal symbols above height `N + 1`, for `q > 1`. -/
def resolventMajorant {q : ℝ≥0∞} (hq : 1 < q) (N : ℕ) : Coeff q :=
  ⟨fun n => (envelope N n : ℂ), by
    apply ((Weight.inverse_sobolev_one_memlp hq).norm.const_mul (3 : ℝ)).mono
    intro n
    simp only [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (envelope_nonneg N n)]
    rw [norm_inverse_weight]
    exact min_le_right _ _⟩

@[simp] theorem norm_resolventMajorant_apply {q : ℝ≥0∞} (hq : 1 < q) (N : ℕ) (n : ℤ) :
    ‖resolventMajorant hq N n‖ = min ((N + 1 : ℝ)⁻¹) (3 / (1 + |(n : ℝ)|)) := by
  change ‖(envelope N n : ℂ)‖ = envelope N n
  simp only [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (envelope_nonneg N n)]

/-- The envelope tends to zero even at infinity, where its uniform cap suffices. -/
theorem tendsto_resolventMajorant_zero {q : ℝ≥0∞} [Fact (1 ≤ q)] (hq : 1 < q) :
    Tendsto (fun N : ℕ => resolventMajorant hq N) atTop (nhds 0) := by
  have hcap : Tendsto (fun N : ℕ => (N + 1 : ℝ)⁻¹) atTop (nhds 0) := by
    exact tendsto_inv_atTop_zero.comp (tendsto_atTop_add_const_right atTop 1 tendsto_natCast_atTop_atTop)
  by_cases htop : q = ⊤
  · subst q
    apply tendsto_zero_iff_norm_tendsto_zero.mpr
    apply squeeze_zero (fun _ => norm_nonneg _) (fun N => ?_) hcap
    exact lp.norm_le_of_forall_le (by positivity)
      (fun n => by rw [norm_resolventMajorant_apply]; exact min_le_left _ _)
  · let g : Coeff q := (3 : ℂ) •
      (⟨fun n => (Weight.sobolev 1 n : ℂ)⁻¹, Weight.inverse_sobolev_one_memlp hq⟩ : Coeff q)
    apply Coeff.tendsto_zero_of_dominated htop _ g
    · apply Eventually.of_forall
      intro N n
      rw [norm_resolventMajorant_apply]
      change min _ _ ≤ ‖(3 : ℂ) * (Weight.sobolev 1 n : ℂ)⁻¹‖
      rw [norm_mul, norm_inverse_weight]
      norm_num only [Complex.norm_ofNat]
      exact min_le_right _ _

    · intro n
      apply tendsto_zero_iff_norm_tendsto_zero.mpr
      exact squeeze_zero (fun _ => norm_nonneg _) (fun N => by
        rw [norm_resolventMajorant_apply]; exact min_le_left _ _) hcap

/-- A centered reciprocal denominator obeys both the height cap and the decaying tail bound. -/
theorem centered_inverse_bound (z : ℂ) (N : ℕ) (hre : |z.re| ≤ Real.pi)
    (him : (N + 1 : ℝ) ≤ |z.im|) (n : ℤ) :
    ‖(z - (Real.pi : ℂ) * n)⁻¹‖ ≤
      min ((N + 1 : ℝ)⁻¹) (3 / (1 + |(n : ℝ)|)) := by
  have hi : |z.im| ≤ ‖z - (Real.pi : ℂ) * n‖ := by
    simpa using Complex.abs_im_le_norm (z - (Real.pi : ℂ) * n)
  have hr : |z.re - Real.pi * (n : ℝ)| ≤ ‖z - (Real.pi : ℂ) * n‖ := by
    simpa using Complex.abs_re_le_norm (z - (Real.pi : ℂ) * n)
  have hd : 1 ≤ ‖z - (Real.pi : ℂ) * n‖ := by
    have hN : 0 ≤ (N : ℝ) := Nat.cast_nonneg N
    linarith
  have hπ : 1 ≤ Real.pi := by linarith [Real.one_le_pi_div_two]
  have htri : Real.pi * |(n : ℝ)| ≤ |z.re - Real.pi * (n : ℝ)| + |z.re| := by
    have h := norm_sub_le (z.re - Real.pi * (n : ℝ)) z.re
    simpa only [sub_sub_cancel_left, norm_neg, Real.norm_eq_abs, abs_mul,
      abs_of_pos Real.pi_pos] using h
  have hmul : ‖z - (Real.pi : ℂ) * n‖ ≤ Real.pi * ‖z - (Real.pi : ℂ) * n‖ :=
    le_mul_of_one_le_left (norm_nonneg _) hπ
  have hn : |(n : ℝ)| ≤ ‖z - (Real.pi : ℂ) * n‖ + 1 := by
    apply (mul_le_mul_iff_right₀ Real.pi_pos).mp
    nlinarith
  rw [norm_inv]
  apply le_min
  · exact inv_anti₀ (by positivity) (him.trans hi)
  · rw [inv_eq_one_div]
    apply (div_le_div_iff₀ (zero_lt_one.trans_le hd) (by positivity)).mpr
    linarith

private def centerFrequency (z : ℂ) : ℤ := ⌊z.re / Real.pi⌋

private theorem centered_re (z : ℂ) :
    |(z - (Real.pi : ℂ) * centerFrequency z).re| ≤ Real.pi := by
  have h0 := Int.sub_floor_div_mul_nonneg z.re Real.pi_pos
  have h1 := Int.sub_floor_div_mul_lt z.re Real.pi_pos
  have he : (z - (Real.pi : ℂ) * centerFrequency z).re =
      z.re - (⌊z.re / Real.pi⌋ : ℝ) * Real.pi := by simp [centerFrequency, mul_comm]
  rw [he, abs_of_nonneg h0]
  exact h1.le

variable (p : ℝ≥0∞) [Fact (1 ≤ p)]

/-- A uniform bound at height `N + 1`, expressed by a concrete reciprocal majorant. -/
def uniformFreeL1Bound (hp : p ≠ ⊤) (N : ℕ) : ℝ :=
  ‖resolventMajorant ((ENNReal.HolderConjugate.lt_top_iff_one_lt p p.conjExponent).mp hp.lt_top) N‖

theorem uniformFreeL1Bound_nonneg (hp : p ≠ ⊤) (N : ℕ) :
    0 ≤ uniformFreeL1Bound p hp N := lp.norm_nonneg' _

/-- The uniform bounds vanish at high imaginary part for every finite Banach exponent. -/
theorem tendsto_uniformFreeL1Bound_zero (hp : p ≠ ⊤) :
    Tendsto (uniformFreeL1Bound p hp) atTop (nhds 0) := by
  let : Fact (1 ≤ p.conjExponent) := ⟨ENNReal.HolderConjugate.one_le p.conjExponent p⟩
  have h := (tendsto_resolventMajorant_zero
    ((ENNReal.HolderConjugate.lt_top_iff_one_lt p p.conjExponent).mp hp.lt_top)).norm
  change Tendsto (fun N => uniformFreeL1Bound p hp N) atTop (nhds 0)
  simpa only [norm_zero, uniformFreeL1Bound] using h

variable {p}

/-- The scalar Hölder bound is uniform in the real part, by reindexing the Fourier lattice. -/
theorem scalarFreeL1Bound_le_uniform (hp : p ≠ ⊤) (N : ℕ) (z : ℂ) (hz : z ∉ freeLattice)
    (him : (N + 1 : ℝ) ≤ |z.im|) : scalarFreeL1Bound p hp z hz ≤ uniformFreeL1Bound p hp N := by
  let : Fact (1 ≤ p.conjExponent) := ⟨ENNReal.HolderConjugate.one_le p.conjExponent p⟩
  unfold scalarFreeL1Bound uniformFreeL1Bound
  rw [← Coeff.norm_reindex (Equiv.addRight (centerFrequency z)) (conjugateInverseSymbol p hp z hz)]
  apply lp.norm_mono (ne_of_gt (zero_lt_one.trans_le (ENNReal.HolderConjugate.one_le p.conjExponent p)))
  intro n
  rw [norm_resolventMajorant_apply]
  change ‖(z - (Real.pi : ℂ) * (n + centerFrequency z : ℤ))⁻¹‖ ≤ _
  have he : z - (Real.pi : ℂ) * (n + centerFrequency z : ℤ) =
      (z - (Real.pi : ℂ) * centerFrequency z) - (Real.pi : ℂ) * n := by
    push_cast
    ring
  rw [he]
  exact centered_inverse_bound _ N (centered_re z) (by simpa using him) n

/-- A uniform `FL^p → FL^1` bound above a height independent of the real part. -/
theorem freeL1Bound_le_uniform (hp : p ≠ ⊤) (N : ℕ) (z : ℂ) (hz : z ∉ freeLattice)
    (him : (N + 1 : ℝ) ≤ |z.im|) : freeL1Bound p hp z hz ≤ uniformFreeL1Bound p hp N := by
  apply max_le
  · exact scalarFreeL1Bound_le_uniform hp N (-z) (neg_notMem_freeLattice hz) (by simpa using him)
  · exact scalarFreeL1Bound_le_uniform hp N z hz him

/-- The free `FL^p → FL^1` bound becomes arbitrarily small, uniformly over real parts. -/
theorem exists_uniform_freeL1_height (hp : p ≠ ⊤) {ε : ℝ} (hε : 0 < ε) :
    ∃ N : ℕ, ∀ (z : ℂ) (hz : z ∉ freeLattice),
      (N + 1 : ℝ) ≤ |z.im| → freeL1Bound p hp z hz < ε := by
  obtain ⟨N, hN⟩ := ((tendsto_uniformFreeL1Bound_zero p hp).eventually_lt_const hε).exists
  exact ⟨N, fun z hz him => (freeL1Bound_le_uniform hp N z hz him).trans_lt hN⟩

/-- A single height works for every potential in a fixed norm ball. -/
theorem exists_uniform_neumann_height (hp : p ≠ ⊤) (M : ℝ) :
    ∃ N : ℕ, ∀ (φ : PairSpace p), ‖φ‖ ≤ M → ∀ (z : ℂ) (hz : z ∉ freeLattice),
      (N + 1 : ℝ) ≤ |z.im| → NeumannCondition hp φ z hz := by
  have ht : Tendsto (fun N => uniformFreeL1Bound p hp N * M) atTop (nhds 0) := by
    simpa only [zero_mul] using (tendsto_uniformFreeL1Bound_zero p hp).mul_const M
  obtain ⟨N, hN⟩ := (ht.eventually_lt_const zero_lt_one).exists
  refine ⟨N, fun φ hφ z hz him => ?_⟩
  exact (mul_le_mul (freeL1Bound_le_uniform hp N z hz him) hφ (norm_nonneg φ)
    (uniformFreeL1Bound_nonneg p hp N)).trans_lt hN

/-- Every potential at every finite Banach exponent has an admissible Neumann parameter. -/
theorem exists_neumannParameter (hp : p ≠ ⊤) (φ : PairSpace p) :
    ∃ z : ℂ, ∃ hz : z ∉ freeLattice, NeumannCondition hp φ z hz := by
  obtain ⟨N, hN⟩ := exists_uniform_neumann_height hp ‖φ‖
  let z : ℂ := (N + 1 : ℂ) * Complex.I
  have him : z.im = N + 1 := by simp [z]
  have hpos : (0 : ℝ) < N + 1 := by positivity
  have hz : z ∉ freeLattice := notMem_freeLattice_of_im_ne_zero (by rw [him]; exact hpos.ne')
  exact ⟨z, hz, hN φ le_rfl z hz (by rw [him, abs_of_pos hpos])⟩

/-- Existence of a two-sided spectral inverse whose base-space realization is compact. -/
theorem exists_compact_inverse (hp : p ≠ ⊤) (φ : PairSpace p) :
    ∃ (z : ℂ) (R : PairSpace p →L[ℂ] Domain p),
      (∀ a, spectralPencil hp φ z (R a) = a) ∧
      (∀ f, R (spectralPencil hp φ z f) = f) ∧
      IsCompactOperator (domainInclusion.comp R) := by
  obtain ⟨z, hz, h⟩ := exists_neumannParameter hp φ
  refine ⟨z, perturbedResolventToDomain hp φ z hz h,
    spectralPencil_perturbedResolventToDomain hp φ z hz h,
    perturbedResolventToDomain_spectralPencil hp φ z hz h, ?_⟩
  rw [← perturbedResolvent_eq_inclusion]
  exact isCompactOperator_perturbedResolvent hp φ z hz h

end NLS.ZakharovShabat
