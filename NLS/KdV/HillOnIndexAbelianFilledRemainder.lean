import NLS.KdV.HillOnIndexAbelianCauchyCompatibility
import NLS.KdV.HillAbelianFilledQuotient

/-! One intrinsic diagonal REMAINDER quotient fills the entire assigned
disc times the unchanged complex source patch, including collapsed
and nonreal gaps. The original diagonal period is not set to zero. -/
noncomputable section
open Set Metric Complex Filter Topology NLS.ComplexAnalysis NLS.ZakharovShabat
open scoped ENNReal Classical
namespace NLS.KdV

namespace HillProductEquationPatch

def onIndexAbelianFilledRemainder (P : HillProductEquationPatch) (m : ℕ+) (t : ℂ × PeriodOneHminusOne) : ℂ :=
  if ht : t ∈ ball (P.centers ((m:ℕ):ℤ):ℂ) (P.radii ((m:ℕ):ℤ)) ×ˢ P.source then
    let E := Classical.choice (nonempty_hillAbelianCauchyEvaluation P m t ht)
    E.chart.onIndexRemainderSolution E.radius t
  else 0

theorem onIndexAbelianFilledRemainder_eq_chart (P : HillProductEquationPatch) (m : ℕ+)
    (C : HillAbelianCauchyChart P m) (ρ : ℝ) (hrρ : C.inner < ρ) (hρR : ρ < C.outer)
    (t : ℂ × PeriodOneHminusOne) (ht : t ∈ ball (P.centers ((m:ℕ):ℤ):ℂ) ρ ×ˢ C.source) :
    P.onIndexAbelianFilledRemainder m t = C.onIndexRemainderSolution ρ t := by
  have hdom : t ∈ ball (P.centers ((m:ℕ):ℤ):ℂ) (P.radii ((m:ℕ):ℤ)) ×ˢ P.source :=
    ⟨ball_subset_ball (hρR.trans C.outer_lt_assigned).le ht.1,C.subset ht.2⟩
  rw [onIndexAbelianFilledRemainder,dif_pos hdom]
  let E := Classical.choice (nonempty_hillAbelianCauchyEvaluation P m t hdom)
  exact E.chart.onIndexRemainderSolution_eq_on_overlap C E.radius ρ E.inner_lt E.lt_outer hrρ hρR
    t.2 E.source_mem ht.2 t.1 E.energy_mem ht.1

theorem analytic_onIndexAbelianFilledRemainder (P : HillProductEquationPatch) (m : ℕ+) :
    AnalyticOnNhd ℂ (P.onIndexAbelianFilledRemainder m)
      (ball (P.centers ((m:ℕ):ℤ):ℂ) (P.radii ((m:ℕ):ℤ)) ×ˢ P.source) := by
  intro t ht
  obtain ⟨C,hq,ρ,hrρ,hρR,hz⟩ := exists_hillAbelianCauchyChart P m t.2 ht.2 t.1 ht.1
  apply (C.analytic_onIndexRemainderSolution ρ hrρ hρR t ⟨hz,hq⟩).congr
  filter_upwards [(isOpen_ball.prod C.source_open).mem_nhds ⟨hz,hq⟩] with s hs
  exact (P.onIndexAbelianFilledRemainder_eq_chart m C ρ hrρ hρR s hs).symm

theorem onIndexAbelianFilledRemainder_equation (P : HillProductEquationPatch) (m : ℕ+)
    (q : PeriodOneHminusOne) (hq : q ∈ P.source) (z : ℂ)
    (hz : z ∈ ball (P.centers ((m:ℕ):ℤ):ℂ) (P.radii ((m:ℕ):ℤ))) :
    sourceAngularSelectedPolynomial (by norm_num) (by norm_num) (P.sourcePsi q) ((m:ℕ):ℤ) z*
      deriv (fun w => P.onIndexAbelianFilledRemainder m (w,q)) z+
      (z-sourceStandardRootMidpoint (by norm_num) (by norm_num) (P.sourcePsi q) ((m:ℕ):ℤ))*P.onIndexAbelianFilledRemainder m (z,q) =
      P.abelianGapNumerator m m (z,q)-I := by
  obtain ⟨C,hqC,ρ,hrρ,hρR,hzC⟩ := exists_hillAbelianCauchyChart P m q hq z hz
  have hderiv : (fun w => P.onIndexAbelianFilledRemainder m (w,q)) =ᶠ[𝓝 z] (fun w => C.onIndexRemainderSolution ρ (w,q)) := by
    filter_upwards [isOpen_ball.mem_nhds hzC] with w hw
    exact P.onIndexAbelianFilledRemainder_eq_chart m C ρ hrρ hρR (w,q) ⟨hw,hqC⟩
  rw [hderiv.deriv_eq,P.onIndexAbelianFilledRemainder_eq_chart m C ρ hrρ hρR (z,q) ⟨hzC,hqC⟩]
  exact C.onIndexRemainderSolution_equation ρ hrρ hρR q hqC z hzC

end HillProductEquationPatch
end NLS.KdV
