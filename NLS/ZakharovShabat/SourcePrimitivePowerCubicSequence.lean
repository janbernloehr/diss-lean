import NLS.ZakharovShabat.SourcePrimitivePowerComplexBound
import NLS.ZakharovShabat.SourcePeriodicGapTails
import NLS.SequenceSpaces.QuarticSummability
import NLS.SequenceSpaces.BoundedCoordinateAnalytic

/-! # The analytic cubic-moment sequence in ℓ¹

The quartic gap estimate and locally bounded ℓ⁴ gap sequence give a
locally bounded ℓ¹-valued map. Its scalar coordinates are the actual
analytic moments, so bounded-coordinate Taylor assembly proves full
Banach-space analyticity without a ball-uniform series assumption.
-/
noncomputable section
open Set Metric Filter Topology Complex
open scoped ENNReal
namespace NLS.ZakharovShabat.SourcePrimitivePowerAtlas
local instance : Fact ((1 : ℝ≥0∞) ≤ 4) := ⟨by norm_num⟩
variable {W : Set (CoeffPair 4)}
variable (A : SourcePrimitivePowerAtlas (by simp) (by norm_num) W)

/-- The cubic moments as an actual ℓ¹ sequence on their almost-real domain. -/
def cubicSequence (ψ : CoeffPair 4) : Coeff 1 :=
  Coeff.ofFunctionOrZero 1 (fun n => A.moment n 3 ψ)

/-- A common connected neighborhood supports the actual analytic ℓ¹-valued
cubic-moment sequence and absolute convergence of its scalar sum. -/
theorem exists_cubicSequence_analytic :
    ∃ U : Set (CoeffPair 4), IsOpen U ∧ IsConnected U ∧ realTypeSourceLocus 4 ⊆ U ∧ U ⊆ A.domain ∧
      (∀ ψ ∈ U, ∀ n, A.cubicSequence ψ n = A.moment n 3 ψ) ∧
      AnalyticOnNhd ℂ A.cubicSequence U ∧
      ∀ ψ ∈ U, Summable (fun n => ‖A.moment n 3 ψ‖) := by
  obtain ⟨U,hU,hconn,hreal,hsub,hbound⟩ := A.exists_almostReal_all_moments_power_bound
  have hquartic (ψ : CoeffPair 4) (hψ : ψ ∈ U) : ∃ B : ℝ,
      ∀ n, ‖A.moment n 3 ψ‖ ≤ B*‖sourcePeriodicGapDisplacement (by simp) (by norm_num) ψ n‖^4 := by
    obtain ⟨r,hr,_,B,_,hb⟩ := hbound ψ hψ
    exact ⟨B^3,fun n => by simpa only [sourcePeriodicGapDisplacement_apply] using hb ψ (mem_ball_self hr) n 3⟩
  have hcoeff (ψ : CoeffPair 4) (hψ : ψ ∈ U) (n : ℤ) : A.cubicSequence ψ n = A.moment n 3 ψ := by
    obtain ⟨B,hb⟩ := hquartic ψ hψ
    exact Coeff.ofFunctionOrZero_one_apply_of_quartic_bound _ _ B hb n
  refine ⟨U,hU,hconn,hreal,hsub,hcoeff,?_,?_⟩
  · intro φ hφ
    obtain ⟨r,hr,hrU,B,hB,hb⟩ := hbound φ hφ
    obtain ⟨_,_,G,hG,hφG,R,hR,hgap⟩ := exists_uniform_small_sourcePeriodicGapDisplacement
      (p := 4) (by simp) (by norm_num) φ (by norm_num : (0:ℝ)<1)
    let V := ball φ r ∩ G
    have hV : IsOpen V := isOpen_ball.inter hG
    have hVU : V ⊆ U := fun _ h => hrU h.1
    have hcoord (n : ℤ) : AnalyticOnNhd ℂ (fun ψ => A.cubicSequence ψ n) V := by
      intro ψ hψ
      exact (A.analytic_moment n 3 ψ (hsub (hVU hψ))).congr
        (Filter.eventuallyEq_of_mem (hV.mem_nhds hψ) (fun χ hχ => (hcoeff χ (hVU hχ) n).symm))
    have hnorm (ψ : CoeffPair 4) (hψ : ψ ∈ V) : ‖A.cubicSequence ψ‖ ≤ B^3*R^4 := by
      have hb' (n : ℤ) : ‖A.moment n 3 ψ‖ ≤
          B^3*‖sourcePeriodicGapDisplacement (by simp) (by norm_num) ψ n‖^4 := by
        simpa only [sourcePeriodicGapDisplacement_apply] using hb ψ hψ.1 n 3
      exact (Coeff.norm_ofFunctionOrZero_one_le_of_quartic_bound _ _ (B^3) hb').trans
        (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) (hgap ψ hψ.2).1 4)
          (pow_nonneg hB.le 3))
    exact Coeff.analyticOnNhd_of_bounded_coordinatewise A.cubicSequence hV hcoord (B^3*R^4) hnorm
      φ ⟨mem_ball_self hr,hφG⟩
  · intro ψ hψ
    obtain ⟨B,hb⟩ := hquartic ψ hψ
    exact (Coeff.summable_norm_of_quartic_bound _ _ B hb).1

end NLS.ZakharovShabat.SourcePrimitivePowerAtlas
