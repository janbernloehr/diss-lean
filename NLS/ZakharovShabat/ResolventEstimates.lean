import NLS.ZakharovShabat.FreeResolvent

/-!
# The free resolvent into absolutely summable coefficients

Hölder's inequality bounds `FL^p → FL^1` by the conjugate-space norm of the
reciprocal symbol. These are the estimates underlying Chapter 1, Lemma 3.2;
the explicit numerical bounds in parts (ii–iii) are separate results.
-/

open scoped ENNReal
noncomputable section

namespace NLS.ZakharovShabat

variable (p : ℝ≥0∞) [Fact (1 ≤ p)]

/-- The reciprocal symbol in the Hölder conjugate space. -/
def conjugateInverseSymbol (hp : p ≠ ⊤) (z : ℂ) (hz : z ∉ freeLattice) :
    Coeff p.conjExponent :=
  ⟨fun n => (z - (Real.pi : ℂ) * n)⁻¹, inverse_denominator_memlp
    ((ENNReal.HolderConjugate.lt_top_iff_one_lt p p.conjExponent).mp hp.lt_top) z hz⟩

/-- The scalar Hölder bound, with the reciprocal-symbol norm kept explicit. -/
def scalarFreeL1Bound (hp : p ≠ ⊤) (z : ℂ) (hz : z ∉ freeLattice) : ℝ :=
  ‖conjugateInverseSymbol p hp z hz‖

theorem scalarFreeL1Bound_nonneg (hp : p ≠ ⊤) (z : ℂ) (hz : z ∉ freeLattice) :
    0 ≤ scalarFreeL1Bound p hp z hz := lp.norm_nonneg' _

/-- A bound for both components, using the maximum pair norm. -/
def freeL1Bound (hp : p ≠ ⊤) (z : ℂ) (hz : z ∉ freeLattice) : ℝ :=
  max (scalarFreeL1Bound p hp (-z) (neg_notMem_freeLattice hz)) (scalarFreeL1Bound p hp z hz)

theorem freeL1Bound_nonneg (hp : p ≠ ⊤) (z : ℂ) (hz : z ∉ freeLattice) :
    0 ≤ freeL1Bound p hp z hz := (scalarFreeL1Bound_nonneg p hp z hz).trans (le_max_right _ _)

variable {p}

/-- The scalar resolvent with absolutely summable output. -/
def scalarResolventToL1 (hp : p ≠ ⊤) (z : ℂ) (hz : z ∉ freeLattice) :
    Coeff p →L[ℂ] Coeff 1 :=
  (WeightedCoeff.sobolevToL1CLM p hp).comp (scalarFreeResolvent z hz)

@[simp] theorem scalarResolventToL1_apply (hp : p ≠ ⊤) (z : ℂ) (hz : z ∉ freeLattice)
    (a : Coeff p) (n : ℤ) :
    scalarResolventToL1 hp z hz a n = a n / (z - (Real.pi : ℂ) * n) := by
  simp [scalarResolventToL1]

theorem norm_scalarResolventToL1_le (hp : p ≠ ⊤) (z : ℂ) (hz : z ∉ freeLattice)
    (a : Coeff p) : ‖scalarResolventToL1 hp z hz a‖ ≤ scalarFreeL1Bound p hp z hz * ‖a‖ := by
  let : Fact (1 ≤ p.conjExponent) := ⟨ENNReal.HolderConjugate.one_le p.conjExponent p⟩
  let b := conjugateInverseSymbol p hp z hz
  have he : scalarResolventToL1 hp z hz a = WeightedCoeff.holderProduct a b := by
    ext n
    rw [scalarResolventToL1_apply]
    change a n / (z - (Real.pi : ℂ) * n) = a n * (z - (Real.pi : ℂ) * n)⁻¹
    rfl
  rw [he]
  calc
    _ ≤ ‖WeightedCoeff.holderProduct (p := p) (q := p.conjExponent)‖ * ‖a‖ * ‖b‖ :=
      (WeightedCoeff.holderProduct (p := p) (q := p.conjExponent)).le_opNorm₂ _ _
    _ ≤ 1 * ‖a‖ * ‖b‖ := by gcongr; exact WeightedCoeff.norm_holderProduct_le
    _ = _ := by change 1 * ‖a‖ * ‖b‖ = ‖b‖ * ‖a‖; ring

/-- The pair resolvent with output in `l1 × l1`. -/
def freeResolventToL1 (hp : p ≠ ⊤) (z : ℂ) (hz : z ∉ freeLattice) :
    PairSpace p →L[ℂ] PairSpace 1 :=
  (-scalarResolventToL1 hp (-z) (neg_notMem_freeLattice hz)).prodMap (scalarResolventToL1 hp z hz)

@[simp] theorem freeResolventToL1_fst_apply (hp : p ≠ ⊤) (z : ℂ) (hz : z ∉ freeLattice)
    (a : PairSpace p) (n : ℤ) :
    (freeResolventToL1 hp z hz a).1 n = a.1 n / (z + (Real.pi : ℂ) * n) := by
  change -scalarResolventToL1 hp (-z) (neg_notMem_freeLattice hz) a.1 n = _
  rw [scalarResolventToL1_apply]
  have he : -z - (Real.pi : ℂ) * n = -(z + (Real.pi : ℂ) * n) := by ring
  rw [he, div_neg, neg_neg]

@[simp] theorem freeResolventToL1_snd_apply (hp : p ≠ ⊤) (z : ℂ) (hz : z ∉ freeLattice)
    (a : PairSpace p) (n : ℤ) :
    (freeResolventToL1 hp z hz a).2 n = a.2 n / (z - (Real.pi : ℂ) * n) :=
  scalarResolventToL1_apply hp z hz a.2 n

/-- Hölder's free resolvent estimate for both components. -/
theorem norm_freeResolventToL1_apply_le (hp : p ≠ ⊤) (z : ℂ) (hz : z ∉ freeLattice)
    (a : PairSpace p) : ‖freeResolventToL1 hp z hz a‖ ≤ freeL1Bound p hp z hz * ‖a‖ := by
  apply norm_prod_le_iff.mpr
  constructor
  · change ‖-scalarResolventToL1 hp (-z) (neg_notMem_freeLattice hz) a.1‖ ≤ _
    rw [norm_neg]
    exact (norm_scalarResolventToL1_le hp (-z) (neg_notMem_freeLattice hz) a.1).trans
      (mul_le_mul (le_max_left _ _) (norm_fst_le a) (norm_nonneg _)
        (freeL1Bound_nonneg p hp z hz))
  · exact (norm_scalarResolventToL1_le hp z hz a.2).trans
      (mul_le_mul (le_max_right _ _) (norm_snd_le a) (norm_nonneg _)
        (freeL1Bound_nonneg p hp z hz))

theorem norm_freeResolventToL1_le (hp : p ≠ ⊤) (z : ℂ) (hz : z ∉ freeLattice) :
    ‖freeResolventToL1 (p := p) hp z hz‖ ≤ freeL1Bound p hp z hz :=
  ContinuousLinearMap.opNorm_le_bound _ (freeL1Bound_nonneg p hp z hz)
    (norm_freeResolventToL1_apply_le hp z hz)

/-- At the `p=1` endpoint the bound decays as `1 / |Im z|`. -/
theorem scalarFreeL1Bound_one_le (z : ℂ) (hz : z ∉ freeLattice) (him : z.im ≠ 0) :
    scalarFreeL1Bound 1 (by simp) z hz ≤ |z.im|⁻¹ := by
  have hb {q : ℝ≥0∞} (hq : q = ⊤) (a : Coeff q)
      (ha : ∀ n, ‖a n‖ ≤ |z.im|⁻¹) : ‖a‖ ≤ |z.im|⁻¹ := by
    subst q
    exact lp.norm_le_of_forall_le (inv_nonneg.mpr (abs_nonneg _)) ha
  apply hb (by simp [ENNReal.conjExponent]) (conjugateInverseSymbol 1 (by simp) z hz)
  intro n
  change ‖(z - (Real.pi : ℂ) * n)⁻¹‖ ≤ _
  rw [norm_inv]
  apply inv_anti₀ (abs_pos.mpr him)
  simpa using Complex.abs_im_le_norm (z - (Real.pi : ℂ) * n)

theorem freeL1Bound_one_le (z : ℂ) (hz : z ∉ freeLattice) (him : z.im ≠ 0) :
    freeL1Bound 1 (by simp) z hz ≤ |z.im|⁻¹ := by
  apply max_le
  · simpa using scalarFreeL1Bound_one_le (-z) (neg_notMem_freeLattice hz) (by simpa using him)
  · exact scalarFreeL1Bound_one_le z hz him

end NLS.ZakharovShabat
