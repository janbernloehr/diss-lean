import NLS.ZakharovShabat.SourceEtaRemainderH1Decay
import NLS.ZakharovShabat.SourceAngularRealCharts

/-! # One-derivative eta-remainder phase multipliers

The actual remainder is real on all real sources, including collapsed
gaps where it vanishes. Its exact exponential error multiplier gains
one sequence derivative at every real order and Banach exponent,
uniformly on physical H1 balls.
-/

noncomputable section
open Set Metric Complex Filter Topology
open scoped ENNReal

namespace NLS.ZakharovShabat.SourceBirkhoffMapComplexData
variable {p : ℝ≥0∞} [Fact (1 ≤ p)] {hp : p ≠ ⊤} {hp1 : 1 < p}
variable {W₀ B W : Set (CoeffPair p)} {s : (n : ℤ) → CoeffPair p → DeletedCoeff p n}
variable (D : SourceBirkhoffMapComplexData hp hp1 W₀ B W s)
include D

/-- The actual eta remainder vanishes at every real collapsed gap. -/
theorem etaRemainder_eq_zero_of_real_collapsed_gap
    (φ : realTypeSourceSubmodule p) (n : ℤ)
    (hg : sourcePeriodicGapDisplacement hp hp1 φ.val n = 0) :
    sourceAngularEtaRemainder hp hp1 n s φ.val = 0 := by
  have hμ := sourceDirichletRoot_eq_midpoint_of_real_collapsed_gap hp hp1 φ.val φ.property n hg
  obtain ⟨U,_,hφU,_,C,_,h⟩ := D.exists_local_uniform_etaRemainder_gap_bound φ
  have hb := h φ.val hφU n
  simp only [hμ,sub_self,hg,norm_zero,zero_div,add_zero,mul_zero] at hb
  exact norm_eq_zero.mp (le_antisymm hb (norm_nonneg _))

/-- The original eta remainder is real, including collapsed gaps where it vanishes. -/
theorem etaRemainder_im_eq_zero (φ : realTypeSourceSubmodule p) (n : ℤ) :
    (sourceAngularEtaRemainder hp hp1 n s φ.val).im = 0 := by
  by_cases hg : canonicalPeriodicGap hp hp1 (periodOnePotential φ.val) (periodOnePotential_mem φ.val) n = 0
  · have hγ : sourcePeriodicGapDisplacement hp hp1 φ.val n = 0 := by
      simpa only [sourcePeriodicGapDisplacement_apply] using hg
    rw [D.etaRemainder_eq_zero_of_real_collapsed_gap φ n hγ]
    rfl
  obtain ⟨O,V,U,c,T,r,R,z₀,ρ,δ,ε,hφU,_,_,E⟩ :=
    D.angular.exists_real_analytic_eta_chart W D.source_open D.source_subset φ.val
      (D.real_subset φ.property) φ.property n hg
  have hη := E.representative_im_eq_zero_of_realType
    D.angular.psi.toSourcePsiIsolatingComplexExtension φ.val hφU φ.property
  rw [E.annulus.etaRemainder_eq_cauchyCandidate ρ E.inner_lt_cauchy E.cauchy_lt_outer
    φ.val (E.angle.source_subset hφU)]
  simpa only [sourceAngularEtaCauchyRepresentative,Complex.add_im,Complex.sub_im,Complex.ofReal_im,
    E.angle.angle_im_eq_zero_of_realType φ.val hφU φ.property,sub_self,zero_add] using hη

/-- The eta remainder has the sharp real phase-error bound. -/
theorem norm_etaRemainderPhase_sub_one_le (φ : realTypeSourceSubmodule p) (n : ℤ) (t : ℝ) :
    ‖exp ((t:ℂ)*I*sourceAngularEtaRemainder hp hp1 n s φ.val)-1‖ ≤
      |t| *‖sourceAngularEtaRemainder hp hp1 n s φ.val‖ := by
  let η := sourceAngularEtaRemainder hp hp1 n s φ.val
  have hi : η.im = 0 := D.etaRemainder_im_eq_zero φ n
  have he : η = (η.re:ℂ) := Complex.ext rfl (by simpa only [Complex.ofReal_im] using hi)
  change ‖exp ((t:ℂ)*I*η)-1‖ ≤ |t| *‖η‖
  rw [he]
  have hexp : (t:ℂ)*I*(η.re:ℂ) = I*((t*η.re:ℝ):ℂ) := by push_cast; ring
  rw [hexp]
  exact (Real.norm_exp_I_mul_ofReal_sub_one_le (x := t*η.re)).trans (by
    rw [norm_mul,Real.norm_eq_abs,Complex.norm_real])

end NLS.ZakharovShabat.SourceBirkhoffMapComplexData

namespace NLS.ZakharovShabat.SourceBirkhoffMapComplexData
variable {W₀ B W : Set (CoeffPair 2)} {s : (n : ℤ) → CoeffPair 2 → DeletedCoeff 2 n}
variable (D : SourceBirkhoffMapComplexData (by simp) (by norm_num) W₀ B W s)
include D

/-- Exact eta-remainder phase errors gain one sequence derivative uniformly on physical H1 balls. -/
theorem etaRemainder_phase_multipliers_uniform_physical_H1_ball (R : ℝ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ a : realTypeSobolevSourceLocus, ‖sourcePhysicalH1Coordinates a.val‖ ≤ R →
      ∀ (q : ℝ≥0∞) (_ : Fact (1 ≤ q)) (r t : ℝ),
        ∃ T : WeightedCoeff (Weight.sobolev r) q →L[ℂ] WeightedCoeff (Weight.sobolev (r+1)) q,
          (∀ c n, (T c).val n = (exp ((t:ℂ)*I*sourceAngularEtaRemainder (by simp) (by norm_num)
            n s (sobolevSourceInclusion a.val))-1)*c.val n) ∧ ‖T‖ ≤ |t| *K := by
  obtain ⟨K,hK,h⟩ := D.etaRemainder_uniform_physical_H1_decay R
  refine ⟨K,hK,?_⟩
  intro a ha q hq r t
  apply WeightedCoeff.exists_sobolev_gain_multiplier r _ (|t| *K) (by positivity)
  intro n
  have hp := D.norm_etaRemainderPhase_sub_one_le ⟨sobolevSourceInclusion a.val,a.property⟩ n t
  calc
    _ ≤ (1+|(n:ℝ)|)*(|t| *‖sourceAngularEtaRemainder (by simp) (by norm_num) n s (sobolevSourceInclusion a.val)‖) :=
      mul_le_mul_of_nonneg_left hp (by positivity)
    _ = |t| *((1+|(n:ℝ)|)*‖sourceAngularEtaRemainder (by simp) (by norm_num) n s (sobolevSourceInclusion a.val)‖) := by ring
    _ ≤ |t| *K := mul_le_mul_of_nonneg_left (h a ha n) (abs_nonneg t)

end NLS.ZakharovShabat.SourceBirkhoffMapComplexData
