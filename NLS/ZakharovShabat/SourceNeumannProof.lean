import NLS.ZakharovShabat.SourceFreeResolventCutoff
import NLS.ZakharovShabat.SourceFreeResolventCounterexample
import NLS.ZakharovShabat.SourceSection3Setup
import NLS.ZakharovShabat.SourceLemma32ScalarProof

/-! # The original-norm Neumann proof of Corollary 3.3

Componentwise Young and Holder estimates give the printed factor-one bound
for the potential/free-resolvent composition in the original finite-p pair
norm. The actual resolvent is its convergent operator-valued Neumann series.
Compactness follows from the free resolvent's finite-rank approximations.
The separate p-to-l1 pair-norm counterexample remains valid.
-/

noncomputable section
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The off-diagonal potential composition preserves the scalar factor in the original p norm. -/
theorem norm_sourcePotentialFreeResolvent_le_scalar (hp : p ≠ ⊤)
    (φ : CoeffPair p) (z : ℂ) (hz : z ∉ freeLattice) :
    ‖(sourcePotentialFromL1 φ).comp (sourceFreeResolventToL1 hp z hz)‖ ≤
      scalarFreeL1Bound p hp z hz * ‖φ‖ := by
  let C := scalarFreeL1Bound p hp z hz
  have hC : 0 ≤ C := scalarFreeL1Bound_nonneg p hp z hz
  have hp0 : 0 < p.toReal := ENNReal.toReal_pos
    (zero_lt_one.trans_le (show 1 ≤ p from Fact.out)).ne' hp
  apply ContinuousLinearMap.opNorm_le_bound _ (mul_nonneg hC (norm_nonneg φ))
  intro a
  let b := sourcePotentialFromL1 φ (sourceFreeResolventToL1 hp z hz a)
  have hfst : ‖b.fst‖ ≤ C*‖φ‖*‖a.snd‖ := by
    change ‖Coeff.convolution φ.fst (sourceFreeResolventToL1 hp z hz a).snd‖ ≤ _
    calc
      _ ≤ ‖φ.fst‖*‖(sourceFreeResolventToL1 hp z hz a).snd‖ := Coeff.norm_convolution_le _ _
      _ ≤ ‖φ‖*(C*‖a.snd‖) := mul_le_mul (WithLp.norm_fst_le _ _)
        (sourceFreeResolvent_snd_scalar_bound hp z hz a) (norm_nonneg _) (norm_nonneg _)
      _ = _ := by ring
  have hsnd : ‖b.snd‖ ≤ C*‖φ‖*‖a.fst‖ := by
    change ‖Coeff.convolution φ.snd (sourceFreeResolventToL1 hp z hz a).fst‖ ≤ _
    calc
      _ ≤ ‖φ.snd‖*‖(sourceFreeResolventToL1 hp z hz a).fst‖ := Coeff.norm_convolution_le _ _
      _ ≤ ‖φ‖*(C*‖a.fst‖) := mul_le_mul (WithLp.norm_snd_le _ _)
        (sourceFreeResolvent_fst_scalar_bound hp z hz a) (norm_nonneg _) (norm_nonneg _)
      _ = _ := by ring
  change ‖b‖ ≤ C*‖φ‖*‖a‖
  apply (Real.rpow_le_rpow_iff (norm_nonneg _) (by positivity) hp0).mp
  calc
    _ = ‖b.fst‖^p.toReal+‖b.snd‖^p.toReal := norm_withLp_prod_rpow hp b
    _ ≤ (C*‖φ‖*‖a.snd‖)^p.toReal+(C*‖φ‖*‖a.fst‖)^p.toReal := by gcongr
    _ = (C*‖φ‖*‖a‖)^p.toReal := by
      rw [Real.mul_rpow (mul_nonneg hC (norm_nonneg φ)) (norm_nonneg _),
        Real.mul_rpow (mul_nonneg hC (norm_nonneg φ)) (norm_nonneg _),
        Real.mul_rpow (mul_nonneg hC (norm_nonneg φ)) (norm_nonneg _),
        norm_withLp_prod_rpow hp a]
      ring

/-- The literal norm bound in the proof of Corollary 3.3 holds in the original norm. -/
theorem norm_sourcePotentialFreeResolvent_le_height (hp : p ≠ ⊤)
    (φ : CoeffPair p) (z : ℂ) (hz : z ∉ freeLattice) (him : z.im ≠ 0) :
    ‖(sourcePotentialFromL1 φ).comp (sourceFreeResolventToL1 hp z hz)‖ ≤
      (4*p.toReal/|z.im|^(1/p.toReal)+1/|z.im|)*‖φ‖ := by
  apply (norm_sourcePotentialFreeResolvent_le_scalar hp φ z hz).trans
  simpa only [one_div] using
    mul_le_mul_of_nonneg_right (scalarFreeL1Bound_le_height hp z hz him) (norm_nonneg φ)

/-- Thus the printed source region gives a genuine Neumann smallness estimate in that norm. -/
theorem norm_sourcePotentialFreeResolvent_lt_one (hp : p ≠ ⊤)
    (φ : CoeffPair p) (z : ℂ) (hz : z ∈ sourceHeightNeumannRegion φ) :
    ‖(sourcePotentialFromL1 φ).comp (sourceFreeResolventToL1 hp z
      (notMem_freeLattice_of_im_ne_zero hz.1))‖ < 1 :=
  (norm_sourcePotentialFreeResolvent_le_height hp φ z _ hz.1).trans_lt hz.2

/-- The actual original-norm resolvent equals the source Neumann inverse formula. -/
theorem sourceResolvent_neumann_formula (hp : p ≠ ⊤)
    (φ : CoeffPair p) (z : ℂ) (hz : z ∈ sourceHeightNeumannRegion φ) :
    let hz0 := notMem_freeLattice_of_im_ne_zero hz.1
    let T := (sourcePotentialFromL1 φ).comp (sourceFreeResolventToL1 hp z hz0)
    sourceResolvent hp φ z = sourceFreeResolvent hp z hz0 *
      ↑(Units.oneSub T (norm_sourcePotentialFreeResolvent_lt_one hp φ z hz))⁻¹ := by
  dsimp only
  let hz0 := notMem_freeLattice_of_im_ne_zero hz.1
  let T := (sourcePotentialFromL1 φ).comp (sourceFreeResolventToL1 hp z hz0)
  let u := Units.oneSub T (norm_sourcePotentialFreeResolvent_lt_one hp φ z hz)
  have h := sourceResolvent_comp_one_sub_potentialFreeResolvent hp φ z hz0
    (sourceHeightNeumannRegion_subset_resolventSet hp φ hz)
  change sourceResolvent hp φ z * (1-T) = sourceFreeResolvent hp z hz0 at h
  change sourceResolvent hp φ z = sourceFreeResolvent hp z hz0 * ↑u⁻¹
  calc
    _ = sourceResolvent hp φ z * (↑u * ↑u⁻¹) := by simp
    _ = (sourceResolvent hp φ z * ↑u) * ↑u⁻¹ := by rw [mul_assoc]
    _ = _ := by change (sourceResolvent hp φ z * (1-T)) * ↑u⁻¹ = _; rw [h]

/-- The original-norm operator-valued Neumann series converges to the actual resolvent. -/
theorem hasSum_sourceResolvent_neumann (hp : p ≠ ⊤)
    (φ : CoeffPair p) (z : ℂ) (hz : z ∈ sourceHeightNeumannRegion φ) :
    let hz0 := notMem_freeLattice_of_im_ne_zero hz.1
    let T := (sourcePotentialFromL1 φ).comp (sourceFreeResolventToL1 hp z hz0)
    HasSum (fun n : ℕ => sourceFreeResolvent hp z hz0 * T^n) (sourceResolvent hp φ z) := by
  dsimp only
  rw [sourceResolvent_neumann_formula hp φ z hz]
  exact (summable_geometric_of_norm_lt_one
    (norm_sourcePotentialFreeResolvent_lt_one hp φ z hz)).hasSum.mul_left _

/-- The source Neumann bound survives at the exact counterexample to the standalone pair bound. -/
theorem sourceNeumann_survives_pairCounterexample :
    10800 < ‖sourceFreeResolventToL1 (by norm_num : (2 : ℝ≥0∞) ≠ ⊤)
      lemma3_2CounterexampleParameter lemma3_2Counterexample_off_lattice‖ ∧
    ∀ φ : CoeffPair 2,
      ‖(sourcePotentialFromL1 (p := 2) φ).comp (sourceFreeResolventToL1 (p := 2) (by norm_num)
        lemma3_2CounterexampleParameter lemma3_2Counterexample_off_lattice)‖ ≤ 10800*‖φ‖ := by
  constructor
  · simpa only [lemma3_2Counterexample_printed_rhs] using lemma3_2_printed_height_bound_false
  · intro φ
    have h := norm_sourcePotentialFreeResolvent_le_height (p := 2) (by norm_num)
      φ lemma3_2CounterexampleParameter lemma3_2Counterexample_off_lattice
      (by norm_num [lemma3_2CounterexampleParameter])
    have he := lemma3_2Counterexample_printed_rhs
    norm_num at h he
    rw [he] at h
    exact h

/-- The compactness sentence in Corollary 3.3 follows from the actual Neumann formula. -/
theorem isCompactOperator_sourceResolvent_from_neumann (hp : p ≠ ⊤)
    (φ : CoeffPair p) (z : ℂ) (hz : z ∈ sourceHeightNeumannRegion φ) :
    IsCompactOperator (sourceResolvent hp φ z) := by
  rw [sourceResolvent_neumann_formula hp φ z hz]
  exact (isCompactOperator_sourceFreeResolvent_from_cutoffs hp z
    (notMem_freeLattice_of_im_ne_zero hz.1)).comp_clm _

end NLS.ZakharovShabat
