import NLS.ZakharovShabat.Operator
import NLS.SequenceSpaces.Multiplier
import Mathlib.Topology.MetricSpace.HausdorffDistance

/-!
# The free resolvent

The free spectral lattice is `πℤ`. The inverse first maps the base space to the
one-derivative domain; composing with the inclusion gives the usual resolvent.
This is the coefficient-space construction underlying Chapter 1, Lemma 3.2.
-/

open scoped ENNReal
noncomputable section

namespace NLS.ZakharovShabat

/-- The free spectral lattice on a circle of period two. -/
def freeLattice : Set ℂ := Set.range (fun n : ℤ => (Real.pi : ℂ) * n)

theorem isClosed_freeLattice : IsClosed freeLattice := by
  have he : freeLattice = (fun z : ℂ => z / (Real.pi : ℂ)) ⁻¹'
      Set.range (fun n : ℤ => (n : ℂ)) := by
    ext z
    simp only [freeLattice, Set.mem_range, Set.mem_preimage]
    constructor
    · rintro ⟨n, rfl⟩
      exact ⟨n, (mul_div_cancel_left₀ _ (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)).symm⟩
    · rintro ⟨n, hn⟩
      refine ⟨n, ?_⟩
      rw [hn, mul_div_cancel₀ _ (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)]
  rw [he]
  exact Complex.isClosed_range_intCast.preimage (by fun_prop)

theorem notMem_freeLattice_of_im_ne_zero {z : ℂ} (hz : z.im ≠ 0) : z ∉ freeLattice := by
  rintro ⟨n, hn⟩
  apply hz
  rw [← hn]
  simp

theorem neg_notMem_freeLattice {z : ℂ} (hz : z ∉ freeLattice) : -z ∉ freeLattice := by
  rintro ⟨n, hn⟩
  apply hz
  refine ⟨-n, ?_⟩
  simpa using congrArg Neg.neg hn

/-- Distance to the entire free lattice, rather than a chosen eigenvalue. -/
def freeGap (z : ℂ) : ℝ := Metric.infDist z freeLattice

theorem freeGap_pos {z : ℂ} (hz : z ∉ freeLattice) : 0 < freeGap z :=
  (isClosed_freeLattice.notMem_iff_infDist_pos ⟨0, ⟨0, by simp⟩⟩).mp hz

theorem freeGap_le (z : ℂ) (n : ℤ) : freeGap z ≤ ‖z - (Real.pi : ℂ) * n‖ :=
  by simpa only [freeGap, dist_eq_norm] using
    (Metric.infDist_le_dist_of_mem (s := freeLattice) (x := z) ⟨n, rfl⟩)

@[simp] theorem freeGap_neg (z : ℂ) : freeGap (-z) = freeGap z := by
  have h (w : ℂ) : freeGap w ≤ freeGap (-w) := by
    apply (Metric.le_infDist (s := freeLattice) ⟨0, ⟨0, by simp⟩⟩).mpr
    rintro _ ⟨n, rfl⟩
    rw [dist_eq_norm]
    have he : -w - (Real.pi : ℂ) * n = -(w - (Real.pi : ℂ) * (-n : ℤ)) := by
      push_cast
      ring
    rw [he, norm_neg]
    exact freeGap_le w (-n)
  exact le_antisymm (by simpa using h (-z)) (h z)

theorem free_denominator_ne_zero {z : ℂ} (hz : z ∉ freeLattice) (n : ℤ) :
    z - (Real.pi : ℂ) * n ≠ 0 := by
  intro h
  exact hz ⟨n, (sub_eq_zero.mp h).symm⟩

/-- A bound for the inverse taking values in the one-derivative domain. -/
def freeDomainBound (z : ℂ) : ℝ :=
  (freeGap z)⁻¹ + (1 + ‖z‖ / freeGap z) / Real.pi

theorem freeDomainBound_nonneg {z : ℂ} (hz : z ∉ freeLattice) : 0 ≤ freeDomainBound z := by
  unfold freeDomainBound
  have := freeGap_pos hz
  positivity

@[simp] theorem freeDomainBound_neg (z : ℂ) : freeDomainBound (-z) = freeDomainBound z := by
  simp [freeDomainBound]

private theorem weighted_inverse_bound {z : ℂ} (hz : z ∉ freeLattice) (n : ℤ) :
    ‖(Weight.sobolev 1 n : ℂ) / (z - (Real.pi : ℂ) * n)‖ ≤ freeDomainBound z := by
  have hd := norm_pos_iff.mpr (free_denominator_ne_zero hz n)
  have hg := freeGap_pos hz
  have hgap := freeGap_le z n
  have hn : Real.pi * |(n : ℝ)| ≤ ‖z - (Real.pi : ℂ) * n‖ + ‖z‖ := by
    have h := norm_sub_le (z - (Real.pi : ℂ) * n) z
    simpa [sub_sub_cancel_left, norm_mul, abs_of_pos Real.pi_pos] using h
  rw [norm_div]
  simp only [Complex.norm_real, Real.norm_eq_abs, Weight.sobolev_apply, Real.rpow_one,
    abs_of_nonneg (by positivity : 0 ≤ 1 + |(n : ℝ)|)]
  apply (div_le_iff₀ hd).mpr
  have hi : 1 ≤ ‖z - (Real.pi : ℂ) * n‖ / freeGap z := (one_le_div hg).mpr hgap
  have hr : ‖z‖ ≤ ‖z‖ / freeGap z * ‖z - (Real.pi : ℂ) * n‖ := by
    have := mul_le_mul_of_nonneg_left hi (norm_nonneg z)
    simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using this
  calc
    1 + |(n : ℝ)| ≤ ‖z - (Real.pi : ℂ) * n‖ / freeGap z +
        (‖z - (Real.pi : ℂ) * n‖ + ‖z‖) / Real.pi :=
      add_le_add hi ((le_div_iff₀ Real.pi_pos).mpr (by nlinarith [hn]))
    _ ≤ ‖z - (Real.pi : ℂ) * n‖ / freeGap z +
        (‖z - (Real.pi : ℂ) * n‖ + ‖z‖ / freeGap z * ‖z - (Real.pi : ℂ) * n‖) /
          Real.pi := by gcongr
    _ = freeDomainBound z * ‖z - (Real.pi : ℂ) * n‖ := by
      unfold freeDomainBound
      ring

private def weightedInverseSymbol (z : ℂ) (hz : z ∉ freeLattice) : Coeff ⊤ :=
  ⟨fun n => (Weight.sobolev 1 n : ℂ) / (z - (Real.pi : ℂ) * n),
    memℓp_infty ⟨freeDomainBound z, by
      rintro _ ⟨n, rfl⟩
      exact weighted_inverse_bound hz n⟩⟩

/-- Reciprocal free denominators belong to every conjugate space with exponent greater than one. -/
theorem inverse_denominator_memlp {q : ℝ≥0∞} (hq : 1 < q)
    (z : ℂ) (hz : z ∉ freeLattice) :
    Memℓp (fun n : ℤ => (z - (Real.pi : ℂ) * n)⁻¹) q := by
  let b : Coeff q := ⟨fun n => (Weight.sobolev 1 n : ℂ)⁻¹,
    Weight.inverse_sobolev_one_memlp hq⟩
  have h := lp.memℓp (Coeff.multiplier (weightedInverseSymbol z hz) b)
  convert h using 1
  funext n
  change (z - (Real.pi : ℂ) * n)⁻¹ =
    ((Weight.sobolev 1 n : ℂ) / (z - (Real.pi : ℂ) * n)) * (Weight.sobolev 1 n : ℂ)⁻¹
  field_simp [(Weight.sobolev 1).complex_ne_zero n, free_denominator_ne_zero hz n]
  exact (div_self ((Weight.sobolev 1).complex_ne_zero n)).symm

variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- Inverse of the scalar free equation with symbol `z - π n`. -/
def scalarFreeResolvent (z : ℂ) (hz : z ∉ freeLattice) : Coeff p →L[ℂ] ScalarDomain p :=
  (WeightedCoeff.weightIsometry _ p).symm.toLinearIsometry.toContinuousLinearMap.comp
    (Coeff.multiplierCLM (weightedInverseSymbol z hz))

@[simp] theorem scalarFreeResolvent_apply (z : ℂ) (hz : z ∉ freeLattice)
    (a : Coeff p) (n : ℤ) :
    (scalarFreeResolvent z hz a).val n = a n / (z - (Real.pi : ℂ) * n) := by
  change (((Weight.sobolev 1 n : ℂ) / (z - (Real.pi : ℂ) * n)) * a n) /
    (Weight.sobolev 1 n : ℂ) = _
  calc
    _ = ((Weight.sobolev 1 n : ℂ) * a n / (Weight.sobolev 1 n : ℂ)) /
        (z - (Real.pi : ℂ) * n) := by ring
    _ = _ := by rw [mul_div_cancel_left₀ _ ((Weight.sobolev 1).complex_ne_zero n)]

theorem norm_scalarFreeResolvent_le (z : ℂ) (hz : z ∉ freeLattice) (a : Coeff p) :
    ‖scalarFreeResolvent z hz a‖ ≤ freeDomainBound z * ‖a‖ := by
  change ‖(WeightedCoeff.weightIsometry _ p).symm
    (Coeff.multiplier (weightedInverseSymbol z hz) a)‖ ≤ _
  rw [LinearIsometryEquiv.norm_map]
  exact (Coeff.norm_multiplier_le _ _).trans
    (mul_le_mul_of_nonneg_right
      (lp.norm_le_of_forall_le (freeDomainBound_nonneg hz) (weighted_inverse_bound hz))
      (norm_nonneg _))

/-- The free spectral equation, with the domain inclusion explicit. -/
def freePencil (z : ℂ) : Domain p →L[ℂ] PairSpace p :=
  z • domainInclusion - freeOperator

@[simp] theorem freePencil_fst_apply (z : ℂ) (f : Domain p) (n : ℤ) :
    (freePencil z f).1 n = (z + (Real.pi : ℂ) * n) * f.1.val n := by
  change z * scalarInclusion f.1 n - (freeOperator f).1 n = _
  rw [scalarInclusion_apply, freeOperator_fst_apply]
  ring

@[simp] theorem freePencil_snd_apply (z : ℂ) (f : Domain p) (n : ℤ) :
    (freePencil z f).2 n = (z - (Real.pi : ℂ) * n) * f.2.val n := by
  change z * scalarInclusion f.2 n - (freeOperator f).2 n = _
  rw [scalarInclusion_apply, freeOperator_snd_apply]
  ring

/-- The inverse of the free equation takes values in the one-derivative domain. -/
def freeResolventToDomain (z : ℂ) (hz : z ∉ freeLattice) :
    PairSpace p →L[ℂ] Domain p :=
  (-scalarFreeResolvent (-z) (neg_notMem_freeLattice hz)).prodMap (scalarFreeResolvent z hz)

@[simp] theorem freeResolventToDomain_fst_apply (z : ℂ) (hz : z ∉ freeLattice)
    (a : PairSpace p) (n : ℤ) :
    (freeResolventToDomain z hz a).1.val n = a.1 n / (z + (Real.pi : ℂ) * n) := by
  change -(scalarFreeResolvent (-z) (neg_notMem_freeLattice hz) a.1).val n = _
  rw [scalarFreeResolvent_apply]
  have he : -z - (Real.pi : ℂ) * n = -(z + (Real.pi : ℂ) * n) := by ring
  rw [he, div_neg, neg_neg]

@[simp] theorem freeResolventToDomain_snd_apply (z : ℂ) (hz : z ∉ freeLattice)
    (a : PairSpace p) (n : ℤ) :
    (freeResolventToDomain z hz a).2.val n = a.2 n / (z - (Real.pi : ℂ) * n) :=
  scalarFreeResolvent_apply z hz a.2 n

private theorem free_denominator_add_ne_zero {z : ℂ} (hz : z ∉ freeLattice) (n : ℤ) :
    z + (Real.pi : ℂ) * n ≠ 0 := by
  simpa using free_denominator_ne_zero hz (-n)

/-- Applying the free equation to its inverse recovers every base-space vector. -/
@[simp] theorem freePencil_freeResolventToDomain (z : ℂ) (hz : z ∉ freeLattice)
    (a : PairSpace p) : freePencil z (freeResolventToDomain z hz a) = a := by
  apply Prod.ext <;> ext n
  · simp [free_denominator_add_ne_zero hz, mul_div_cancel₀]
  · simp [free_denominator_ne_zero hz, mul_div_cancel₀]

/-- The inverse also recovers every vector in the operator domain. -/
@[simp] theorem freeResolventToDomain_freePencil (z : ℂ) (hz : z ∉ freeLattice)
    (f : Domain p) : freeResolventToDomain z hz (freePencil z f) = f := by
  apply Prod.ext <;> apply Subtype.ext <;> funext n
  · simp [free_denominator_add_ne_zero hz]
  · simp [free_denominator_ne_zero hz]

/-- The free equation is a continuous linear equivalence between the domain and base space. -/
def freePencilEquiv (z : ℂ) (hz : z ∉ freeLattice) : Domain p ≃L[ℂ] PairSpace p :=
  { freePencil z with
    invFun := freeResolventToDomain z hz
    left_inv := freeResolventToDomain_freePencil z hz
    right_inv := freePencil_freeResolventToDomain z hz
    continuous_invFun := (freeResolventToDomain z hz).continuous }

/-- The usual free resolvent as an operator on the base space. -/
def freeResolvent (z : ℂ) (hz : z ∉ freeLattice) : PairSpace p →L[ℂ] PairSpace p :=
  domainInclusion.comp (freeResolventToDomain z hz)

@[simp] theorem freeResolvent_fst_apply (z : ℂ) (hz : z ∉ freeLattice)
    (a : PairSpace p) (n : ℤ) :
    (freeResolvent z hz a).1 n = a.1 n / (z + (Real.pi : ℂ) * n) := by
  simp [freeResolvent]

@[simp] theorem freeResolvent_snd_apply (z : ℂ) (hz : z ∉ freeLattice)
    (a : PairSpace p) (n : ℤ) :
    (freeResolvent z hz a).2 n = a.2 n / (z - (Real.pi : ℂ) * n) := by
  simp [freeResolvent]

/-- The inverse gains one derivative, with an explicit spectral-gap bound. -/
theorem norm_freeResolventToDomain_apply_le (z : ℂ) (hz : z ∉ freeLattice) (a : PairSpace p) :
    ‖freeResolventToDomain z hz a‖ ≤ freeDomainBound z * ‖a‖ := by
  apply norm_prod_le_iff.mpr
  constructor
  · change ‖-scalarFreeResolvent (-z) (neg_notMem_freeLattice hz) a.1‖ ≤ _
    rw [norm_neg]
    have h := norm_scalarFreeResolvent_le (-z) (neg_notMem_freeLattice hz) a.1
    rw [freeDomainBound_neg] at h
    exact h.trans
      (mul_le_mul_of_nonneg_left (norm_fst_le a) (freeDomainBound_nonneg hz))
  · exact (norm_scalarFreeResolvent_le z hz a.2).trans
      (mul_le_mul_of_nonneg_left (norm_snd_le a) (freeDomainBound_nonneg hz))

theorem norm_freeResolventToDomain_le (z : ℂ) (hz : z ∉ freeLattice) :
    ‖freeResolventToDomain (p := p) z hz‖ ≤ freeDomainBound z :=
  ContinuousLinearMap.opNorm_le_bound _ (freeDomainBound_nonneg hz)
    (norm_freeResolventToDomain_apply_le z hz)

private theorem inverse_bound {z : ℂ} (hz : z ∉ freeLattice) (n : ℤ) :
    ‖(z - (Real.pi : ℂ) * n)⁻¹‖ ≤ (freeGap z)⁻¹ := by
  rw [norm_inv]
  exact inv_anti₀ (freeGap_pos hz) (freeGap_le z n)

/-- The bounded reciprocal symbol of the scalar free equation. -/
def inverseSymbol (z : ℂ) (hz : z ∉ freeLattice) : Coeff ⊤ :=
  ⟨fun n => (z - (Real.pi : ℂ) * n)⁻¹,
    memℓp_infty ⟨(freeGap z)⁻¹, by rintro _ ⟨n, rfl⟩; exact inverse_bound hz n⟩⟩

/-- The scalar resolvent, viewed as an operator on the base coefficient space. -/
def scalarResolvent (z : ℂ) (hz : z ∉ freeLattice) : Coeff p →L[ℂ] Coeff p :=
  scalarInclusion.comp (scalarFreeResolvent z hz)

@[simp] theorem scalarResolvent_apply (z : ℂ) (hz : z ∉ freeLattice) (a : Coeff p) (n : ℤ) :
    scalarResolvent z hz a n = a n / (z - (Real.pi : ℂ) * n) := by
  simp [scalarResolvent]

theorem scalarResolvent_eq_multiplier (z : ℂ) (hz : z ∉ freeLattice) :
    scalarResolvent (p := p) z hz = Coeff.multiplierCLM (inverseSymbol z hz) := by
  apply ContinuousLinearMap.ext
  intro a
  ext n
  simp [inverseSymbol, div_eq_mul_inv, mul_comm]

theorem norm_scalarResolvent_apply_le (z : ℂ) (hz : z ∉ freeLattice) (a : Coeff p) :
    ‖scalarResolvent z hz a‖ ≤ (freeGap z)⁻¹ * ‖a‖ := by
  rw [scalarResolvent_eq_multiplier, Coeff.multiplierCLM_apply]
  exact (Coeff.norm_multiplier_le _ _).trans
    (mul_le_mul_of_nonneg_right
      (lp.norm_le_of_forall_le (inv_nonneg.mpr (freeGap_pos hz).le) (inverse_bound hz))
      (norm_nonneg _))

theorem freeResolvent_eq_prodMap (z : ℂ) (hz : z ∉ freeLattice) :
    freeResolvent (p := p) z hz =
      (-scalarResolvent (-z) (neg_notMem_freeLattice hz)).prodMap (scalarResolvent z hz) := by
  apply ContinuousLinearMap.ext
  intro a
  change (scalarInclusion (-scalarFreeResolvent (-z) (neg_notMem_freeLattice hz) a.1),
    scalarInclusion (scalarFreeResolvent z hz a.2)) =
      (-scalarInclusion (scalarFreeResolvent (-z) (neg_notMem_freeLattice hz) a.1),
        scalarInclusion (scalarFreeResolvent z hz a.2))
  rw [map_neg]

/-- The base-space resolvent bound is the inverse distance to the free spectrum. -/
theorem norm_freeResolvent_apply_le (z : ℂ) (hz : z ∉ freeLattice) (a : PairSpace p) :
    ‖freeResolvent z hz a‖ ≤ (freeGap z)⁻¹ * ‖a‖ := by
  rw [freeResolvent_eq_prodMap]
  apply norm_prod_le_iff.mpr
  constructor
  · change ‖-scalarResolvent (-z) (neg_notMem_freeLattice hz) a.1‖ ≤ _
    rw [norm_neg]
    have h := norm_scalarResolvent_apply_le (-z) (neg_notMem_freeLattice hz) a.1
    rw [freeGap_neg] at h
    exact h.trans
      (mul_le_mul_of_nonneg_left (norm_fst_le a) (inv_nonneg.mpr (freeGap_pos hz).le))
  · exact (norm_scalarResolvent_apply_le z hz a.2).trans
      (mul_le_mul_of_nonneg_left (norm_snd_le a) (inv_nonneg.mpr (freeGap_pos hz).le))

theorem norm_freeResolvent_le (z : ℂ) (hz : z ∉ freeLattice) :
    ‖freeResolvent (p := p) z hz‖ ≤ (freeGap z)⁻¹ :=
  ContinuousLinearMap.opNorm_le_bound _ (inv_nonneg.mpr (freeGap_pos hz).le)
    (norm_freeResolvent_apply_le z hz)

/-- In the signed negative mode, the resolvent denominator is `z - π n`. -/
theorem freeResolvent_negativeMode (z : ℂ) (hz : z ∉ freeLattice) (n : ℤ) :
    freeResolvent z hz (domainInclusion (negativeMode (p := p) n)) =
      (z - (Real.pi : ℂ) * n)⁻¹ • domainInclusion (negativeMode n) := by
  apply Prod.ext <;> ext k
  · by_cases h : k = -n <;> simp [negativeMode, h, sub_eq_add_neg]
  · simp [negativeMode]

/-- In the signed positive mode, the resolvent has the same denominator. -/
theorem freeResolvent_positiveMode (z : ℂ) (hz : z ∉ freeLattice) (n : ℤ) :
    freeResolvent z hz (domainInclusion (positiveMode (p := p) n)) =
      (z - (Real.pi : ℂ) * n)⁻¹ • domainInclusion (positiveMode n) := by
  apply Prod.ext <;> ext k
  · simp [positiveMode]
  · by_cases h : k = n <;> simp [positiveMode, h]

/-- The standard resolvent identity, for the convention `R(z) = (z - L₀)⁻¹`. -/
theorem freeResolvent_identity (z w : ℂ) (hz : z ∉ freeLattice) (hw : w ∉ freeLattice) :
    freeResolvent (p := p) z hz - freeResolvent w hw =
      (w - z) • (freeResolvent z hz).comp (freeResolvent w hw) := by
  apply ContinuousLinearMap.ext
  intro a
  apply Prod.ext <;> ext n
  · change (freeResolvent z hz a).1 n - (freeResolvent w hw a).1 n =
      (w - z) * (freeResolvent z hz (freeResolvent w hw a)).1 n
    simp only [freeResolvent_fst_apply]
    field_simp [free_denominator_add_ne_zero hz n, free_denominator_add_ne_zero hw n]
    ring
  · change (freeResolvent z hz a).2 n - (freeResolvent w hw a).2 n =
      (w - z) * (freeResolvent z hz (freeResolvent w hw a)).2 n
    simp only [freeResolvent_snd_apply]
    field_simp [free_denominator_ne_zero hz n, free_denominator_ne_zero hw n]
    ring

end NLS.ZakharovShabat
