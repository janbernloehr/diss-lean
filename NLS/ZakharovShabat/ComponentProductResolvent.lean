import NLS.ZakharovShabat.DoubleResolvent
import NLS.ZakharovShabat.ExplicitHeight
import NLS.ZakharovShabat.PeriodOneEmbedding

/-! # Resolvent bounds retaining both potential components

The square of the off-diagonal perturbation is controlled by the product
of the component norms. This gives a geometric-mean height at every finite
exponent and recovers the printed source height under an explicit imbalance
condition. It does not prove the unrestricted printed height above four.
-/

noncomputable section
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The first perturbation component only uses the second input component. -/
theorem norm_potentialFreeResolvent_fst_le (hp : p ≠ ⊤) (φ : PairSpace p)
    (z : ℂ) (hz : z ∉ freeLattice) (a : PairSpace p) :
    ‖(potentialFreeResolvent hp φ z hz a).1‖ ≤
      ‖φ.1‖ * freeL1Bound p hp z hz * ‖a.2‖ := by
  rw [potentialFreeResolvent_apply]
  calc
    _ ≤ ‖φ.1‖ * ‖scalarResolventToL1 hp z hz a.2‖ := Coeff.norm_convolution_le _ _
    _ ≤ ‖φ.1‖ * (scalarFreeL1Bound p hp z hz * ‖a.2‖) :=
      mul_le_mul_of_nonneg_left (norm_scalarResolventToL1_le hp z hz a.2) (norm_nonneg _)
    _ ≤ ‖φ.1‖ * (freeL1Bound p hp z hz * ‖a.2‖) := by
      gcongr
      exact le_max_right _ _
    _ = _ := by ring

/-- The second perturbation component only uses the first input component. -/
theorem norm_potentialFreeResolvent_snd_le (hp : p ≠ ⊤) (φ : PairSpace p)
    (z : ℂ) (hz : z ∉ freeLattice) (a : PairSpace p) :
    ‖(potentialFreeResolvent hp φ z hz a).2‖ ≤
      ‖φ.2‖ * freeL1Bound p hp z hz * ‖a.1‖ := by
  rw [potentialFreeResolvent_apply]
  calc
    _ ≤ ‖φ.2‖ * ‖-scalarResolventToL1 hp (-z) (neg_notMem_freeLattice hz) a.1‖ :=
      Coeff.norm_convolution_le _ _
    _ = ‖φ.2‖ * ‖scalarResolventToL1 hp (-z) (neg_notMem_freeLattice hz) a.1‖ := by rw [norm_neg]
    _ ≤ ‖φ.2‖ * (scalarFreeL1Bound p hp (-z) (neg_notMem_freeLattice hz) * ‖a.1‖) :=
      mul_le_mul_of_nonneg_left (norm_scalarResolventToL1_le hp (-z)
        (neg_notMem_freeLattice hz) a.1) (norm_nonneg _)
    _ ≤ ‖φ.2‖ * (freeL1Bound p hp z hz * ‖a.1‖) := by
      gcongr
      exact le_max_left _ _
    _ = _ := by ring

/-- Squaring retains the product, rather than the square of the maximum component norm. -/
theorem norm_potentialFreeResolvent_sq_le_component_product (hp : p ≠ ⊤)
    (φ : PairSpace p) (z : ℂ) (hz : z ∉ freeLattice) :
    ‖potentialFreeResolvent hp φ z hz ^ 2‖ ≤
      freeL1Bound p hp z hz ^ 2 * (‖φ.1‖ * ‖φ.2‖) := by
  let B := freeL1Bound p hp z hz
  have hB : 0 ≤ B := freeL1Bound_nonneg p hp z hz
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro a
  rw [pow_two]
  change ‖potentialFreeResolvent hp φ z hz (potentialFreeResolvent hp φ z hz a)‖ ≤ _
  apply norm_prod_le_iff.mpr
  constructor
  · calc
      _ ≤ ‖φ.1‖*B*‖(potentialFreeResolvent hp φ z hz a).2‖ :=
        norm_potentialFreeResolvent_fst_le hp φ z hz _
      _ ≤ ‖φ.1‖*B*(‖φ.2‖*B*‖a.1‖) :=
        mul_le_mul_of_nonneg_left (norm_potentialFreeResolvent_snd_le hp φ z hz a) (by positivity)
      _ ≤ ‖φ.1‖*B*(‖φ.2‖*B*‖a‖) := by gcongr; exact norm_fst_le a
      _ = _ := by dsimp [B]; ring
  · calc
      _ ≤ ‖φ.2‖*B*‖(potentialFreeResolvent hp φ z hz a).1‖ :=
        norm_potentialFreeResolvent_snd_le hp φ z hz _
      _ ≤ ‖φ.2‖*B*(‖φ.1‖*B*‖a.2‖) :=
        mul_le_mul_of_nonneg_left (norm_potentialFreeResolvent_fst_le hp φ z hz a) (by positivity)
      _ ≤ ‖φ.2‖*B*(‖φ.1‖*B*‖a‖) := by gcongr; exact norm_snd_le a
      _ = _ := by dsimp [B]; ring

/-- A component-product condition yields the existing two-sided squared inverse. -/
theorem squaredNeumannCondition_of_component_product (hp : p ≠ ⊤)
    (φ : PairSpace p) (z : ℂ) (hz : z ∉ freeLattice)
    (h : freeL1Bound p hp z hz ^ 2 * (‖φ.1‖ * ‖φ.2‖) < 1) :
    SquaredNeumannCondition hp φ z hz :=
  (norm_potentialFreeResolvent_sq_le_component_product hp φ z hz).trans_lt h

/-- The geometric mean measures the two-way coupling of a potential. -/
def potentialComponentMean (φ : PairSpace p) : ℝ := Real.sqrt (‖φ.1‖ * ‖φ.2‖)

omit [Fact (1 ≤ p)] in
@[simp] theorem potentialComponentMean_nonneg (φ : PairSpace p) :
    0 ≤ potentialComponentMean φ := Real.sqrt_nonneg _

@[simp] theorem potentialComponentMean_sq (φ : PairSpace p) :
    potentialComponentMean φ ^ 2 = ‖φ.1‖ * ‖φ.2‖ := Real.sq_sqrt (by positivity)

/-- The geometric mean never exceeds the maximum pair norm. -/
theorem potentialComponentMean_le_norm (φ : PairSpace p) :
    potentialComponentMean φ ≤ ‖φ‖ := by
  apply (Real.sqrt_le_iff).mpr
  exact ⟨norm_nonneg _, by simpa only [pow_two] using
    (mul_le_mul (norm_fst_le φ) (norm_snd_le φ) (norm_nonneg _) (norm_nonneg _))⟩

/-- A bound for the geometric mean suffices even when either component is large. -/
theorem mem_resolventSet_of_componentMean_bound (hp : p ≠ ⊤) (φ : PairSpace p)
    (z : ℂ) (hz : z ∉ freeLattice) {M : ℝ}
    (hφ : potentialComponentMean φ ≤ M) (h : freeL1Bound p hp z hz * M < 1) :
    z ∈ resolventSet hp φ := by
  apply mem_resolventSet_of_squaredNeumannCondition hp φ z hz
  apply squaredNeumannCondition_of_component_product
  have hB := freeL1Bound_nonneg p hp z hz
  have hsmall := (mul_le_mul_of_nonneg_left hφ hB).trans_lt h
  have hn : 0 ≤ freeL1Bound p hp z hz * potentialComponentMean φ :=
    mul_nonneg hB (potentialComponentMean_nonneg φ)
  rw [← potentialComponentMean_sq]
  nlinarith

/-- The explicit height uses the geometric mean at every finite Banach exponent. -/
theorem mem_resolventSet_of_componentMean_height (hp : p ≠ ⊤) (φ : PairSpace p)
    {M : ℝ} (hM : 0 ≤ M) (hφ : potentialComponentMean φ ≤ M) {z : ℂ}
    (hz : (1+8*p.toReal*M)^p.toReal ≤ |z.im|) : z ∈ resolventSet hp φ := by
  have hp1 : (1 : ℝ) ≤ p.toReal := by exact_mod_cast ENNReal.toReal_mono hp (show 1 ≤ p from Fact.out)
  have hH : 0 < (1+8*p.toReal*M)^p.toReal := by positivity
  have him := abs_pos.mp (hH.trans_le hz)
  have hz0 := notMem_freeLattice_of_im_ne_zero him
  apply mem_resolventSet_of_componentMean_bound hp φ z hz0 hφ
  apply (mul_le_mul_of_nonneg_right (freeL1Bound_le_height hp z hz0 him) hM).trans_lt
  have hb : (4*p.toReal/|z.im|^(1/p.toReal)+|z.im|⁻¹)*M ≤
      (4*p.toReal/((1+8*p.toReal*M)^p.toReal)^(1/p.toReal)+
        ((1+8*p.toReal*M)^p.toReal)⁻¹)*M := by gcongr
  exact hb.trans_lt (by simpa only [one_div] using explicit_height_neumann_bound hp1 hM)

/-- Every actual periodic eigenvalue obeys the geometric-mean height. -/
theorem periodicSpectrum_abs_im_lt_componentMean_height (hp : p ≠ ⊤) (φ : PairSpace p)
    {z : ℂ} (hz : z ∈ periodicSpectrum hp φ) :
    |z.im| < (1+8*p.toReal*potentialComponentMean φ)^p.toReal := by
  by_contra h
  exact hz (mem_resolventSet_of_componentMean_height hp φ
    (potentialComponentMean_nonneg φ) le_rfl (le_of_not_gt h))

/-- Period doubling preserves both component norms and hence their geometric mean. -/
@[simp] theorem potentialComponentMean_periodOnePotential (φ : CoeffPair p) :
    potentialComponentMean (periodOnePotential φ) = Real.sqrt (‖φ.fst‖*‖φ.snd‖) := by
  simp [potentialComponentMean, periodOnePotential_apply]

/-- An explicit imbalance condition suffices for the original source-norm height at all p. -/
theorem source_mem_resolventSet_of_printed_height_component_product (hp : p ≠ ⊤)
    (φ : CoeffPair p) (hφ : p.toReal*Real.sqrt (‖φ.fst‖*‖φ.snd‖) ≤ ‖φ‖)
    {z : ℂ} (hz : (1+8*‖φ‖)^p.toReal ≤ |z.im|) :
    z ∈ resolventSet hp (periodOnePotential φ) := by
  apply mem_resolventSet_of_componentMean_height hp _ (potentialComponentMean_nonneg _) le_rfl
  apply le_trans _ hz
  rw [potentialComponentMean_periodOnePotential]
  apply Real.rpow_le_rpow (by positivity) _ ENNReal.toReal_nonneg
  nlinarith

/-- The corresponding exclusion concerns the actual source spectrum, not a sufficient test alone. -/
theorem sourceSpectrum_abs_im_lt_printed_height_component_product (hp : p ≠ ⊤)
    (φ : CoeffPair p) (hφ : p.toReal*Real.sqrt (‖φ.fst‖*‖φ.snd‖) ≤ ‖φ‖)
    {z : ℂ} (hz : z ∈ periodicSpectrum hp (periodOnePotential φ)) :
    |z.im| < (1+8*‖φ‖)^p.toReal := by
  by_contra h
  exact hz (source_mem_resolventSet_of_printed_height_component_product hp φ hφ (le_of_not_gt h))

/-- A directly checkable norm imbalance implies the source-height coupling condition. -/
theorem source_componentMean_condition_of_imbalance (φ : CoeffPair p)
    (hφ : p.toReal ^ 2 * ‖φ.snd‖ ≤ ‖φ.fst‖) :
    p.toReal * Real.sqrt (‖φ.fst‖ * ‖φ.snd‖) ≤ ‖φ‖ := by
  have hs : (p.toReal * Real.sqrt (‖φ.fst‖ * ‖φ.snd‖)) ^ 2 ≤ ‖φ.fst‖ ^ 2 := by
    rw [mul_pow, Real.sq_sqrt (by positivity)]
    calc
      _ = ‖φ.fst‖ * (p.toReal ^ 2 * ‖φ.snd‖) := by ring
      _ ≤ ‖φ.fst‖ * ‖φ.fst‖ := mul_le_mul_of_nonneg_left hφ (norm_nonneg _)
      _ = _ := by ring
  have hmean : p.toReal * Real.sqrt (‖φ.fst‖ * ‖φ.snd‖) ≤ ‖φ.fst‖ := by
    nlinarith [norm_nonneg φ.fst]
  exact hmean.trans (WithLp.norm_fst_le (Coeff p) φ)

/-- At fixed spectral parameter the quantitative product condition is open in the potential. -/
def componentProductNeumannRegion (hp : p ≠ ⊤) (z : ℂ) (hz : z ∉ freeLattice) :
    Set (PairSpace p) := {φ | freeL1Bound p hp z hz ^ 2 * (‖φ.1‖ * ‖φ.2‖) < 1}

theorem isOpen_componentProductNeumannRegion (hp : p ≠ ⊤) (z : ℂ) (hz : z ∉ freeLattice) :
    IsOpen (componentProductNeumannRegion hp z hz) :=
  isOpen_lt (continuous_const.mul (continuous_fst.norm.mul continuous_snd.norm)) continuous_const

/-- Every triangular potential is interior to this explicit resolvent region off the free lattice. -/
theorem mem_componentProductNeumannRegion_of_oneSided (hp : p ≠ ⊤) (φ : PairSpace p)
    (z : ℂ) (hz : z ∉ freeLattice) (hφ : φ.1 = 0 ∨ φ.2 = 0) :
    φ ∈ componentProductNeumannRegion hp z hz := by
  rcases hφ with hφ | hφ <;> simp [componentProductNeumannRegion, hφ]

/-- The complete resolvent is analytic throughout the explicit potential region. -/
theorem analyticOnNhd_resolvent_componentProductRegion (hp : p ≠ ⊤)
    (z : ℂ) (hz : z ∉ freeLattice) :
    AnalyticOnNhd ℂ (fun φ => resolvent hp φ z) (componentProductNeumannRegion hp z hz) := by
  intro φ hφ
  exact analyticAt_resolvent_potential hp φ z
    (mem_resolventSet_of_squaredNeumannCondition hp φ z hz
      (squaredNeumannCondition_of_component_product hp φ z hz hφ))

end NLS.ZakharovShabat

