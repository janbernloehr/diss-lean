import NLS.KdV.HillAbelianCauchyCharts
import NLS.ZakharovShabat.SourceStandardRootContourAnyCircle

/-! The ACTUAL diagonal Hill differential has period 2*pi. Subtracting
I divided by its selected standard root removes exactly that period.
Only this remainder, not the diagonal differential, has zero period. -/
noncomputable section
open Set Metric Complex Filter Topology NLS.ComplexAnalysis NLS.ZakharovShabat
open scoped ENNReal Classical
namespace NLS.KdV.HillProductEquationPatch

def onIndexAbelianRemainderDifferential (P : HillProductEquationPatch) (n : ℕ+)
    (t : ℂ × PeriodOneHminusOne) : ℂ :=
  P.abelianFrequencyDifferential n t-I/sourceStandardRoot (by norm_num) (by norm_num) (P.sourcePsi t.2) ((n:ℕ):ℤ) t.1

theorem analytic_onIndexAbelianRemainderDifferential (P : HillProductEquationPatch) (n : ℕ+) :
    AnalyticOnNhd ℂ (P.onIndexAbelianRemainderDifferential n) P.abelianJointFrequencyDomain := by
  intro t ht
  exact (P.analytic_abelianFrequencyDifferential_joint n t ht).sub
    (analyticAt_const.div (P.analytic_abelianSelectedRoot n t ⟨ht.1,ht.2 _⟩)
      (sourceStandardRoot_ne_zero_off_segment (by norm_num) (by norm_num) (P.sourcePsi t.2) ((n:ℕ):ℤ) t.1 (ht.2 _)))

theorem onIndexAbelianRemainderDifferential_eq_gap_quotient (P : HillProductEquationPatch) (n : ℕ+)
    (t : ℂ × PeriodOneHminusOne) (ht : t.1 ∈ sourceCanonicalRootDomain (by norm_num) (by norm_num) (P.sourcePsi t.2)) :
    P.onIndexAbelianRemainderDifferential n t =
      (P.abelianGapNumerator n n t-I)/sourceStandardRoot (by norm_num) (by norm_num) (P.sourcePsi t.2) ((n:ℕ):ℤ) t.1 := by
  rw [onIndexAbelianRemainderDifferential,P.abelianFrequencyDifferential_eq_gap_quotient n n t ht,sub_div]

theorem onIndexAbelianRemainderDifferential_period (P : HillProductEquationPatch) (n : ℕ+)
    (q : PeriodOneHminusOne) (hq : q ∈ P.source)
    (D : SourceCriticalRootPeriodCircle (by norm_num) (by norm_num) (P.sourcePsi q) ((n:ℕ):ℤ)) :
    (∮ z in C((D.center:ℂ),D.radius), P.onIndexAbelianRemainderDifferential n (z,q)) = 0 := by
  have hp := P.abelianFrequencyDifferential_period n n q hq D
  rw [if_pos rfl] at hp
  have hπ : (2*Real.pi:ℂ) ≠ 0 := by simp [Real.pi_ne_zero]
  have hp' : (∮ z in C((D.center:ℂ),D.radius), P.abelianFrequencyDifferential n (z,q)) = (2*Real.pi:ℂ) := by
    calc
      _ = (2*Real.pi:ℂ)*((2*Real.pi:ℂ)⁻¹*(∮ z in C((D.center:ℂ),D.radius), P.abelianFrequencyDifferential n (z,q))) := by
        rw [← mul_assoc,mul_inv_cancel₀ hπ,one_mul]
      _ = _ := by rw [hp]; ring
  have hroot (z : ℂ) (hz : z ∈ sphere (D.center:ℂ) D.radius) := D.sphere_subset_rootDomain hz
  have hfd : CircleIntegrable (fun z => P.abelianFrequencyDifferential n (z,q)) (D.center:ℂ) D.radius := by
    apply ContinuousOn.circleIntegrable D.radius_pos.le
    intro z hz
    exact ((P.analytic_abelianFrequencyDifferential_joint n (z,q) ⟨hq,hroot z hz⟩).comp
      (f := fun w : ℂ => (w,q)) (analyticAt_id.prod analyticAt_const)).continuousAt.continuousWithinAt
  have hqr : CircleIntegrable (fun z => (sourceStandardRoot (by norm_num) (by norm_num) (P.sourcePsi q) ((n:ℕ):ℤ) z)⁻¹) (D.center:ℂ) D.radius := by
    apply ContinuousOn.circleIntegrable D.radius_pos.le
    intro z hz
    exact (sourceStandardRoot_inv_analyticAt (by norm_num) (by norm_num) (P.sourcePsi q) ((n:ℕ):ℤ) z (hroot z hz _)).continuousAt.continuousWithinAt
  have hI := hqr.const_mul I
  change CircleIntegrable (fun z => I*(sourceStandardRoot (by norm_num) (by norm_num) (P.sourcePsi q) ((n:ℕ):ℤ) z)⁻¹) _ _ at hI
  change (∮ z in C((D.center:ℂ),D.radius), P.abelianFrequencyDifferential n (z,q)-I/sourceStandardRoot (by norm_num) (by norm_num) (P.sourcePsi q) ((n:ℕ):ℤ) z) = 0
  simp only [div_eq_mul_inv]
  rw [circleIntegral.integral_sub hfd hI,circleIntegral.integral_const_mul,hp',
    circleIntegral_sourceStandardRoot_inv_of_gap_mem_ball (by norm_num) (by norm_num) (P.sourcePsi q) ((n:ℕ):ℤ) (D.center:ℂ) D.radius D.radius_pos D.gap]
  linear_combination (2*Real.pi:ℂ)*I_sq

end NLS.KdV.HillProductEquationPatch
