import NLS.SequenceSpaces.PairComponentHolder
import NLS.ZakharovShabat.FreeResolventCompact
import NLS.ZakharovShabat.HeightResolvent

/-! # The actual free resolvent in the source component-sum norms

The source exponent is finite. The maximum-product operator is transported
through the coefficient-preserving equivalences, including the l1 target.
-/
noncomputable section
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The free resolvent on the original finite-exponent pair space. -/
def sourceFreeResolvent (_hp : p ≠ ⊤) (z : ℂ) (hz : z ∉ freeLattice) : CoeffPair p →L[ℂ] CoeffPair p :=
  (CoeffPair.toMax p).symm.toContinuousLinearMap.comp
    ((freeResolvent z hz).comp (CoeffPair.toMax p).toContinuousLinearMap)

/-- The free resolvent with the original component-sum l1 target norm. -/
def sourceFreeResolventToL1 (hp : p ≠ ⊤) (z : ℂ) (hz : z ∉ freeLattice) : CoeffPair p →L[ℂ] CoeffPair 1 :=
  (CoeffPair.toMax 1).symm.toContinuousLinearMap.comp
    ((freeResolventToL1 hp z hz).comp (CoeffPair.toMax p).toContinuousLinearMap)

@[simp] theorem sourceFreeResolventToL1_fst_apply (hp : p ≠ ⊤) (z : ℂ) (hz : z ∉ freeLattice)
    (a : CoeffPair p) (n : ℤ) :
    (sourceFreeResolventToL1 hp z hz a).fst n = a.fst n/(z+(Real.pi : ℂ)*n) :=
  freeResolventToL1_fst_apply hp z hz _ n

@[simp] theorem sourceFreeResolventToL1_snd_apply (hp : p ≠ ⊤) (z : ℂ) (hz : z ∉ freeLattice)
    (a : CoeffPair p) (n : ℤ) :
    (sourceFreeResolventToL1 hp z hz a).snd n = a.snd n/(z-(Real.pi : ℂ)*n) :=
  freeResolventToL1_snd_apply hp z hz _ n

/-- Lemma 3.2(i) in the original norm, with the same conclusion at every finite exponent. -/
theorem isCompactOperator_sourceFreeResolvent (hp : p ≠ ⊤) (z : ℂ) (hz : z ∉ freeLattice) :
    IsCompactOperator (sourceFreeResolvent hp z hz) :=
  ((isCompactOperator_freeResolvent (p := p) z hz).comp_clm (CoeffPair.toMax p).toContinuousLinearMap).clm_comp
    (CoeffPair.toMax p).symm.toContinuousLinearMap

/-- The l1-target and base-space free resolvents agree at exponent one. -/
theorem sourceFreeResolventToL1_one (z : ℂ) (hz : z ∉ freeLattice) :
    sourceFreeResolventToL1 (by norm_num : (1 : ℝ≥0∞) ≠ ⊤) z hz = sourceFreeResolvent (by norm_num) z hz := by
  ext a : 1
  apply WithLp.ofLp_injective
  apply Prod.ext <;> ext n
  · exact (freeResolventToL1_fst_apply _ z hz _ n).trans (freeResolvent_fst_apply z hz _ n).symm
  · exact (freeResolventToL1_snd_apply _ z hz _ n).trans (freeResolvent_snd_apply z hz _ n).symm

/-- The precise two-component factor in the original p-to-one operator bound. -/
theorem norm_sourceFreeResolventToL1_le (hp : p ≠ ⊤) (z : ℂ) (hz : z ∉ freeLattice) :
    ‖sourceFreeResolventToL1 hp z hz‖ ≤ CoeffPair.l1Factor p * freeL1Bound p hp z hz := by
  apply ContinuousLinearMap.opNorm_le_bound _
    (mul_nonneg (CoeffPair.l1Factor_pos p).le (freeL1Bound_nonneg p hp z hz))
  intro a
  rw [CoeffPair.norm_one_eq_sum]
  have hf : ‖(sourceFreeResolventToL1 hp z hz a).fst‖ ≤ freeL1Bound p hp z hz * ‖a.fst‖ := by
    change ‖-scalarResolventToL1 hp (-z) (neg_notMem_freeLattice hz) a.fst‖ ≤ _
    rw [norm_neg]
    exact (norm_scalarResolventToL1_le hp (-z) (neg_notMem_freeLattice hz) a.fst).trans
      (mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg _))
  have hs : ‖(sourceFreeResolventToL1 hp z hz a).snd‖ ≤ freeL1Bound p hp z hz * ‖a.snd‖ :=
    (norm_scalarResolventToL1_le hp z hz a.snd).trans
      (mul_le_mul_of_nonneg_right (le_max_right _ _) (norm_nonneg _))
  calc
    _ ≤ freeL1Bound p hp z hz * (‖a.fst‖+‖a.snd‖) := by simpa only [mul_add] using add_le_add hf hs
    _ ≤ freeL1Bound p hp z hz * (CoeffPair.l1Factor p*‖a‖) :=
      mul_le_mul_of_nonneg_left (CoeffPair.componentNormSum_le hp a) (freeL1Bound_nonneg p hp z hz)
    _ = _ := by ring

/-- Both zero modes are exact free eigenvectors with denominator z. -/
theorem sourceFreeResolventToL1_diagonal_zero (hp : p ≠ ⊤) (z : ℂ) (hz : z ∉ freeLattice) :
    sourceFreeResolventToL1 hp z hz
      ((CoeffPair.toMax p).symm (lp.single p 0 1, lp.single p 0 1)) =
        (CoeffPair.toMax 1).symm (lp.single 1 0 (1/z), lp.single 1 0 (1/z)) := by
  apply WithLp.ofLp_injective
  apply Prod.ext <;> ext n
  · change (freeResolventToL1 hp z hz _).1 n = _
    rw [freeResolventToL1_fst_apply]
    by_cases hn : n = 0 <;> simp [hn, lp.single_apply]
  · change (freeResolventToL1 hp z hz _).2 n = _
    rw [freeResolventToL1_snd_apply]
    by_cases hn : n = 0 <;> simp [hn, lp.single_apply]

/-- The pole term necessarily includes the two-component factor in the original norms. -/
theorem l1Factor_div_norm_le_sourceFreeResolventToL1 (hp : p ≠ ⊤) (z : ℂ) (hz : z ∉ freeLattice) :
    CoeffPair.l1Factor p / ‖z‖ ≤ ‖sourceFreeResolventToL1 hp z hz‖ := by
  have h := (sourceFreeResolventToL1 hp z hz).le_opNorm
    ((CoeffPair.toMax p).symm (lp.single p 0 1, lp.single p 0 1))
  rw [sourceFreeResolventToL1_diagonal_zero, CoeffPair.norm_diagonal hp,
    CoeffPair.norm_diagonal (by norm_num : (1 : ℝ≥0∞) ≠ ⊤)] at h
  rw [lp.norm_single (zero_lt_one.trans_le (show 1 ≤ p from Fact.out))] at h
  norm_num only [ENNReal.toReal_one, div_one, Real.rpow_one, lp.norm_single,
    norm_one, mul_one, norm_div] at h
  apply (mul_le_mul_iff_left₀ (Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 2) (1/p.toReal))).mp
  calc
    _ = 2/‖z‖ := by rw [div_mul_eq_mul_div, CoeffPair.l1Factor_mul_rpow]
    _ ≤ _ := by simpa only [div_eq_mul_inv, one_mul] using h

/-- A proved corrected height estimate; it is not the printed factor-one assertion. -/
theorem norm_sourceFreeResolventToL1_le_height (hp : p ≠ ⊤) (z : ℂ) (hz : z ∉ freeLattice)
    (him : z.im ≠ 0) :
    ‖sourceFreeResolventToL1 hp z hz‖ ≤ CoeffPair.l1Factor p *
      (4*p.toReal/|z.im|^(1/p.toReal) + 1/|z.im|) := by
  exact (norm_sourceFreeResolventToL1_le hp z hz).trans
    (mul_le_mul_of_nonneg_left (by simpa only [one_div] using freeL1Bound_le_height hp z hz him)
      (CoeffPair.l1Factor_pos p).le)

/-- At p=1 the printed height bound is unchanged. -/
theorem norm_sourceFreeResolventToL1_one_le_height (z : ℂ) (hz : z ∉ freeLattice)
    (him : z.im ≠ 0) :
    ‖sourceFreeResolventToL1 (by norm_num : (1 : ℝ≥0∞) ≠ ⊤) z hz‖ ≤ 4/|z.im| + 1/|z.im| := by
  simpa only [CoeffPair.l1Factor_one, one_mul, ENNReal.toReal_one, mul_one, div_one, Real.rpow_one] using
    norm_sourceFreeResolventToL1_le_height (p := 1) (by norm_num) z hz him

/-- Lemma 3.2(iii) holds in the original norms, even with the stronger constant four. -/
theorem norm_sourceFreeResolventToL1_le_verticalStrip_four (hp : p ≠ ⊤) (z : ℂ) (hz0 : z ∉ freeLattice)
    {n : ℤ} {r : ℝ} (hr : 0 < r) (hrπ : r ≤ Real.pi/4) (hz : z ∈ verticalStrip n r) :
    ‖sourceFreeResolventToL1 hp z hz0‖ ≤ 4*p.toReal/r := by
  apply (norm_sourceFreeResolventToL1_le hp z hz0).trans
  calc
    _ ≤ 2*(2*p.toReal/r) := mul_le_mul (CoeffPair.l1Factor_le_two p)
      (freeL1Bound_le_verticalStrip hp z hz0 hr hrπ hz)
      (freeL1Bound_nonneg p hp z hz0) (by norm_num)
    _ = _ := by ring

/-- The printed strip bound, with precisely the source pair norms. -/
theorem norm_sourceFreeResolventToL1_le_verticalStrip (hp : p ≠ ⊤) (z : ℂ) (hz0 : z ∉ freeLattice)
    {n : ℤ} {r : ℝ} (hr : 0 < r) (hrπ : r ≤ Real.pi/4) (hz : z ∈ verticalStrip n r) :
    ‖sourceFreeResolventToL1 hp z hz0‖ ≤ 8*p.toReal/r := by
  apply (norm_sourceFreeResolventToL1_le_verticalStrip_four hp z hz0 hr hrπ hz).trans
  gcongr
  norm_num

end NLS.ZakharovShabat
