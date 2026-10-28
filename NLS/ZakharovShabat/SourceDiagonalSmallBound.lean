import NLS.ZakharovShabat.SourceLemma6_8DiagonalProof
import NLS.ZakharovShabat.ResonantCauchyGap

/-! # Quadratic bounds for the original diagonal and Cauchy estimates

Supporting estimates for the unresolved final weighted gap sum on p.44.
The actual counted-root gap still needs comparison with the coefficient sum.
-/
noncomputable section
open Filter Topology
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]
local instance sourceSmallDiagonalConjFact : Fact (1 ≤ p.conjExponent) :=
  ⟨ENNReal.HolderConjugate.one_le p.conjExponent p⟩

/-- An exponent-only quadratic majorant for the original diagonal. -/
def sourceDiagonalNormConstant (hp : p ≠ ⊤) : ℝ :=
  2*‖Coeff.puncturedLattice p.conjExponent
    ((ENNReal.HolderConjugate.lt_top_iff_one_lt p p.conjExponent).mp hp.lt_top)‖

/-- The original diagonal majorant is nonnegative. -/
theorem sourceDiagonalNormConstant_nonneg (hp : p ≠ ⊤) : 0 ≤ sourceDiagonalNormConstant hp := by
  unfold sourceDiagonalNormConstant
  positivity

/-- Half-contraction gives a quadratic original-norm bound on the entire strip, for every finite Banach exponent. -/
theorem norm_sourceResonantA_le_norm_sq (hp : p ≠ ⊤) (φ : CoeffPair p) (n : ℤ) (z : ℂ)
    (hz : z ∈ resonantStrip n)
    (hh : ‖weightedPotentialSquareInShift hp SpectralWeight.one (unitWeightedPairEquiv φ) n z hz‖ ≤ 1/2) :
    ‖sourceResonantAFunction hp φ n z‖ ≤ sourceDiagonalNormConstant hp*‖φ‖^2 := by
  have hq := (ENNReal.HolderConjugate.lt_top_iff_one_lt p p.conjExponent).mp hp.lt_top
  have h := hh.trans_lt (by norm_num : (1/2 : ℝ) < 1)
  rw [sourceResonantA_physical_series hp φ n z hz h]
  have hb := norm_tsum_complementaryRow_le (q := p.conjExponent) hq φ.snd
    (sourceResonantEvenVector hp φ n z hz h 1).fst n z hz
  have he := ((WithLp.norm_fst_le _ (sourceResonantEvenVector hp φ n z hz h 1)).trans
    (norm_sourceResonantEvenVector_one_le hp φ n z hz h hh)).trans
      (mul_le_mul_of_nonneg_left (WithLp.norm_fst_le _ φ) (by norm_num : (0 : ℝ) ≤ 2))
  have hr := (norm_complementaryRowEnvelope_le hq φ.snd n).trans
    (mul_le_mul_of_nonneg_right (WithLp.norm_snd_le _ φ) (norm_nonneg _))
  apply hb.trans
  calc
    _ ≤ (2*‖φ‖)*(‖φ‖*‖Coeff.puncturedLattice p.conjExponent hq‖) :=
      mul_le_mul he hr (norm_nonneg _) (by positivity)
    _ = _ := by unfold sourceDiagonalNormConstant; ring

/-- Cauchy gives a derivative bound proportional to an arbitrary full-strip majorant. -/
theorem norm_deriv_le_on_refined_disk_of_bound (n : ℤ) (a : ℂ → ℂ) (B : ℝ)
    (ha : AnalyticOnNhd ℂ a (resonantStrip n))
    (hb : ∀ z ∈ resonantStrip n, ‖a z‖ ≤ B) (x : ℂ) (hx : x ∈ refinedResonantDisk n) :
    ‖deriv a x‖ ≤ B/(Real.pi/4) := by
  have hball := closedBall_refined_point_subset_strip n x hx
  exact Complex.norm_deriv_le_of_forall_mem_sphere_norm_le (by positivity : 0 < Real.pi/4)
    (ha.differentiableOn.diffContOnCl_ball hball)
    (fun z hz => hb z (hball (Metric.sphere_subset_closedBall hz)))

/-- The same majorant gives a Lipschitz estimate between any two points of the refined disk. -/
theorem norm_diagonal_sub_le_on_refined_disk_of_bound (n : ℤ) (a : ℂ → ℂ) (B : ℝ)
    (ha : AnalyticOnNhd ℂ a (resonantStrip n))
    (hb : ∀ z ∈ resonantStrip n, ‖a z‖ ≤ B)
    (x y : ℂ) (hx : x ∈ refinedResonantDisk n) (hy : y ∈ refinedResonantDisk n) :
    ‖a x-a y‖ ≤ (B/(Real.pi/4))*‖x-y‖ :=
  Convex.norm_image_sub_le_of_norm_deriv_le
    (fun z hz => (ha z (refinedResonantDisk_subset_strip n hz)).differentiableAt)
    (norm_deriv_le_on_refined_disk_of_bound n a B ha hb) (convex_ball _ _) hy hx

end NLS.ZakharovShabat
