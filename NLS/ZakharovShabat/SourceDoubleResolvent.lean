import NLS.ZakharovShabat.SourceFreeResolvent
import NLS.ZakharovShabat.SourceFourierTail
import NLS.ZakharovShabat.DoubleResolventEstimates

/-! # Lemma 3.4 in the original component-sum pair norms

The actual sandwich R₀ Φ R₀ has the original p-norm on its input and
the original l1 norm on its output. The maximum-product estimate
transfers with an explicit factor two, giving the admissible constant
c_p = 64 p². No optimality of this constant is asserted.
-/
noncomputable section
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The actual sandwich R₀ Φ R₀ with original p input and l1 output. -/
def sourceDoubleResolvent (hp : p ≠ ⊤) (φ : CoeffPair p) (z : ℂ) (hz : z ∉ freeLattice) :
    CoeffPair p →L[ℂ] CoeffPair 1 :=
  (CoeffPair.toMax 1).symm.toContinuousLinearMap.comp
    ((doubleResolvent hp (CoeffPair.toMax p φ) z hz).comp (CoeffPair.toMax p).toContinuousLinearMap)

/-- Changing the l1 output from maximum to sum norm costs at most two. -/
theorem norm_sourceDoubleResolvent_le_max (hp : p ≠ ⊤) (φ : CoeffPair p) (z : ℂ) (hz : z ∉ freeLattice) :
    ‖sourceDoubleResolvent hp φ z hz‖ ≤ 2*‖doubleResolvent hp (CoeffPair.toMax p φ) z hz‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro a
  change ‖(CoeffPair.toMax 1).symm (doubleResolvent hp (CoeffPair.toMax p φ) z hz (CoeffPair.toMax p a))‖ ≤ _
  calc
    _ ≤ 2*‖doubleResolvent hp (CoeffPair.toMax p φ) z hz (CoeffPair.toMax p a)‖ := by
      simpa using CoeffPair.norm_toMax_symm_le (by norm_num : (1 : ℝ≥0∞) ≠ ⊤) _
    _ ≤ 2*(‖doubleResolvent hp (CoeffPair.toMax p φ) z hz‖*‖CoeffPair.toMax p a‖) :=
      mul_le_mul_of_nonneg_left (ContinuousLinearMap.le_opNorm _ _) (by norm_num)
    _ ≤ 2*(‖doubleResolvent hp (CoeffPair.toMax p φ) z hz‖*‖a‖) := by
      gcongr
      exact CoeffPair.norm_toMax_le a
    _ = _ := by ring

/-- Lemma 3.4 with the explicit original-norm constant c_p=64p². -/
theorem norm_sourceDoubleResolvent_le_verticalStrip (hp : p ≠ ⊤) (φ : CoeffPair p) (z : ℂ)
    (hz0 : z ∉ freeLattice) {n : ℤ} {r : ℝ}
    (hr : 0 < r) (hrπ : r ≤ Real.pi/4) (hz : z ∈ verticalStrip n r) :
    ‖sourceDoubleResolvent hp φ z hz0‖ ≤ (64*p.toReal^2/r^2)*
      (‖φ‖/|(n : ℝ)|^(1/p.toReal)+‖sourceFourierTail n.natAbs φ‖) := by
  have ht : ‖pairFourierTail n.natAbs (CoeffPair.toMax p φ)‖ ≤ ‖sourceFourierTail n.natAbs φ‖ := by
    exact CoeffPair.norm_toMax_le (sourceFourierTail n.natAbs φ)
  calc
    _ ≤ 2*‖doubleResolvent hp (CoeffPair.toMax p φ) z hz0‖ := norm_sourceDoubleResolvent_le_max hp φ z hz0
    _ ≤ 2*((32*p.toReal^2/r^2)*
        (‖CoeffPair.toMax p φ‖/|(n : ℝ)|^(1/p.toReal)+‖pairFourierTail n.natAbs (CoeffPair.toMax p φ)‖)) :=
      mul_le_mul_of_nonneg_left (norm_doubleResolvent_le_verticalStrip hp _ z hz0 hr hrπ hz) (by norm_num)
    _ ≤ 2*((32*p.toReal^2/r^2)*
        (‖φ‖/|(n : ℝ)|^(1/p.toReal)+‖sourceFourierTail n.natAbs φ‖)) := by
      gcongr
      exact CoeffPair.norm_toMax_le φ
    _ = _ := by ring

theorem sourceFourierTail_zero (φ : CoeffPair p) : sourceFourierTail 0 φ = φ := by
  apply WithLp.ofLp_injective
  ext j <;> simp [sourceFourierTail]

/-- Potential multiplication, with original l1 input and p output norms. -/
def sourcePotentialFromL1 (φ : CoeffPair p) : CoeffPair 1 →L[ℂ] CoeffPair p :=
  (CoeffPair.toMax p).symm.toContinuousLinearMap.comp
    ((potentialFromL1 (CoeffPair.toMax p φ)).comp (CoeffPair.toMax 1).toContinuousLinearMap)

@[simp] theorem sourcePotentialFromL1_fst (φ : CoeffPair p) (a : CoeffPair 1) :
    (sourcePotentialFromL1 φ a).fst = Coeff.convolution φ.fst a.snd := rfl

@[simp] theorem sourcePotentialFromL1_snd (φ : CoeffPair p) (a : CoeffPair 1) :
    (sourcePotentialFromL1 φ a).snd = Coeff.convolution φ.snd a.fst := rfl

/-- The transported map is exactly the composition R₀ Φ R₀ in the original norms. -/
theorem sourceDoubleResolvent_eq_comp (hp : p ≠ ⊤) (φ : CoeffPair p) (z : ℂ)
    (hz : z ∉ freeLattice) :
    sourceDoubleResolvent hp φ z hz = (sourceFreeResolventToL1 hp z hz).comp
      ((sourcePotentialFromL1 φ).comp (sourceFreeResolventToL1 hp z hz)) := by
  ext a : 1
  change (CoeffPair.toMax 1).symm
      (freeResolventToL1 hp z hz
        (potentialFreeResolvent hp (CoeffPair.toMax p φ) z hz (CoeffPair.toMax p a))) =
    (CoeffPair.toMax 1).symm (freeResolventToL1 hp z hz
      ((CoeffPair.toMax p) ((CoeffPair.toMax p).symm
        (potentialFromL1 (CoeffPair.toMax p φ)
          ((CoeffPair.toMax 1) ((CoeffPair.toMax 1).symm
            (freeResolventToL1 hp z hz (CoeffPair.toMax p a))))))))
  simp only [ContinuousLinearEquiv.apply_symm_apply]
  rw [potentialFreeResolvent_eq_comp_L1]
  rfl

/-- First coefficient formula in the raw scalar Fourier convention. -/
theorem sourceDoubleResolvent_fst_apply (hp : p ≠ ⊤) (φ : CoeffPair p) (z : ℂ)
    (hz : z ∉ freeLattice) (a : CoeffPair p) (j : ℤ) :
    (sourceDoubleResolvent hp φ z hz a).fst j =
      ∑' k : ℤ, φ.fst (j-k)*a.snd k /
        ((z+(Real.pi : ℂ)*j)*(z-(Real.pi : ℂ)*k)) :=
  doubleResolvent_fst_apply hp (CoeffPair.toMax p φ) z hz (CoeffPair.toMax p a) j

/-- Second coefficient formula, with the opposite free Fourier symbol. -/
theorem sourceDoubleResolvent_snd_apply (hp : p ≠ ⊤) (φ : CoeffPair p) (z : ℂ)
    (hz : z ∉ freeLattice) (a : CoeffPair p) (j : ℤ) :
    (sourceDoubleResolvent hp φ z hz a).snd j =
      ∑' k : ℤ, φ.snd (j-k)*a.fst k /
        ((z-(Real.pi : ℂ)*j)*(z+(Real.pi : ℂ)*k)) :=
  doubleResolvent_snd_apply hp (CoeffPair.toMax p φ) z hz (CoeffPair.toMax p a) j

/-- Fourier remainders are contractive in the original finite pair norm. -/
theorem norm_sourceFourierTail_le (hp : p ≠ ⊤) (N : ℕ) (φ : CoeffPair p) :
    ‖sourceFourierTail N φ‖ ≤ ‖φ‖ := by
  have hp0 : p ≠ 0 := (zero_lt_one.trans_le (show 1 ≤ p from Fact.out)).ne'
  have hpp : 0 < p.toReal := ENNReal.toReal_pos hp0 hp
  rw [WithLp.prod_norm_eq_add hpp, WithLp.prod_norm_eq_add hpp]
  change (‖Coeff.fourierTail N φ.fst‖^p.toReal + ‖Coeff.fourierTail N φ.snd‖^p.toReal)^(1/p.toReal) ≤ _
  gcongr
  · exact Coeff.norm_fourierTail_le hp0 N φ.fst
  · exact Coeff.norm_fourierTail_le hp0 N φ.snd

end NLS.ZakharovShabat
