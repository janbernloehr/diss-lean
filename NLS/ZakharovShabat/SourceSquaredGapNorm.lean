import NLS.ZakharovShabat.SourceSquaredGapReciprocalRows
import NLS.ZakharovShabat.SourcePeriodicGapTails

/-!
# Norm of the source squared-gap sequence

The squared gap at half the original exponent has norm at most the
square of the unsquared gap norm, including below exponent one. This
turns a locally uniform gap bound into a uniform constant for the
quadratic correction of Lemma 10.8.
-/

noncomputable section
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The squared source gap has its expected half-exponent norm bound,
also for `1 < p < 2`. -/
theorem norm_sourcePeriodicSquaredGapCoeff_le_sq
    (hp : p ≠ ⊤) (hp1 : 1 < p) (ψ : CoeffPair p) :
    ‖sourcePeriodicSquaredGapCoeff hp hp1 ψ‖ ≤
      ‖sourcePeriodicGapDisplacement hp hp1 ψ‖^2 := by
  let g := sourcePeriodicGapDisplacement hp hp1 ψ
  have hpr : 0 < p.toReal :=
    ENNReal.toReal_pos (ne_of_gt (zero_lt_one.trans hp1)) hp
  have hrEq : (ENNReal.ofReal (p.toReal/2)).toReal = p.toReal/2 := by
    rw [ENNReal.toReal_ofReal (by positivity : 0 ≤ p.toReal/2)]
  have hr : 0 < (ENNReal.ofReal (p.toReal/2)).toReal := by
    rw [hrEq]
    positivity
  have hterm (n : ℤ) :
      ‖sourcePeriodicSquaredGapCoeff hp hp1 ψ n‖^
          (ENNReal.ofReal (p.toReal/2)).toReal = ‖g n‖^p.toReal := by
    rw [hrEq, sourcePeriodicSquaredGapCoeff_apply]
    exact norm_sq_rpow_half (g n) p.toReal
  apply lp.norm_le_of_forall_sum_le hr (sq_nonneg _)
  intro s
  calc
    ∑ n ∈ s, ‖sourcePeriodicSquaredGapCoeff hp hp1 ψ n‖^
        (ENNReal.ofReal (p.toReal/2)).toReal =
          ∑ n ∈ s, ‖g n‖^p.toReal := by
            apply Finset.sum_congr rfl
            intro n _
            exact hterm n
    _ ≤ ‖g‖^p.toReal := lp.sum_rpow_le_norm_rpow hpr g s
    _ = (‖g‖^2)^(ENNReal.ofReal (p.toReal/2)).toReal := by
      rw [hrEq]
      rw [← Real.rpow_natCast ‖g‖ 2,
        ← Real.rpow_mul (norm_nonneg g)]
      congr 1
      ring

/-- The half-exponent squared-gap norm has a common bound near every
source potential. -/
theorem exists_local_sourcePeriodicSquaredGapCoeff_bound
    (hp : p ≠ ⊤) (hp1 : 1 < p) (φ : CoeffPair p) :
    ∃ V : Set (CoeffPair p), IsOpen V ∧ φ ∈ V ∧
      ∃ R : ℝ, 0 ≤ R ∧
        ∀ ψ ∈ V, ‖sourcePeriodicSquaredGapCoeff hp hp1 ψ‖ ≤ R^2 := by
  obtain ⟨_,_,V,hVopen,hφV,R,hR,hdata⟩ :=
    exists_uniform_small_sourcePeriodicGapDisplacement hp hp1 φ
      (by norm_num : (0 : ℝ) < 1)
  refine ⟨V,hVopen,hφV,R,hR,?_⟩
  intro ψ hψ
  calc
    ‖sourcePeriodicSquaredGapCoeff hp hp1 ψ‖ ≤
        ‖sourcePeriodicGapDisplacement hp hp1 ψ‖^2 :=
          norm_sourcePeriodicSquaredGapCoeff_le_sq hp hp1 ψ
    _ ≤ R^2 := pow_le_pow_left₀ (norm_nonneg _) (hdata ψ hψ).1 2

end NLS.ZakharovShabat
