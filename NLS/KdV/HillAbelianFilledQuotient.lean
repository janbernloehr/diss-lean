import NLS.KdV.HillAbelianCauchyCompatibility

/-! ONE intrinsic filled off-index quadratic quotient, jointly
analytic across the ENTIRE original energy-frequency gap disc and
complex native source patch, including ALL collapsed gaps. -/
noncomputable section
open Set Metric Complex Filter Topology NLS.ComplexAnalysis NLS.ZakharovShabat
open scoped ENNReal Classical
namespace NLS.KdV

structure HillAbelianCauchyEvaluation (P : HillProductEquationPatch) (m : ℕ+) (t : ℂ × PeriodOneHminusOne) where
  chart : HillAbelianCauchyChart P m
  radius : ℝ
  inner_lt : chart.inner < radius
  lt_outer : radius < chart.outer
  energy_mem : t.1 ∈ ball (P.centers ((m:ℕ):ℤ):ℂ) radius
  source_mem : t.2 ∈ chart.source

theorem nonempty_hillAbelianCauchyEvaluation (P : HillProductEquationPatch) (m : ℕ+)
    (t : ℂ × PeriodOneHminusOne) (ht : t ∈ ball (P.centers ((m:ℕ):ℤ):ℂ) (P.radii ((m:ℕ):ℤ)) ×ˢ P.source) :
    Nonempty (HillAbelianCauchyEvaluation P m t) := by
  obtain ⟨C,hq,ρ,hrρ,hρR,hz⟩ := exists_hillAbelianCauchyChart P m t.2 ht.2 t.1 ht.1
  exact ⟨⟨C,ρ,hrρ,hρR,hz,hq⟩⟩

namespace HillProductEquationPatch

def offIndexAbelianFilledQuotient (P : HillProductEquationPatch) (n m : ℕ+) (t : ℂ × PeriodOneHminusOne) : ℂ :=
  if ht : t ∈ ball (P.centers ((m:ℕ):ℤ):ℂ) (P.radii ((m:ℕ):ℤ)) ×ˢ P.source then
    let E := Classical.choice (nonempty_hillAbelianCauchyEvaluation P m t ht)
    E.chart.solution n E.radius t
  else 0

theorem offIndexAbelianFilledQuotient_eq_chart (P : HillProductEquationPatch) (n m : ℕ+) (hmn : m ≠ n)
    (C : HillAbelianCauchyChart P m) (ρ : ℝ) (hrρ : C.inner < ρ) (hρR : ρ < C.outer)
    (t : ℂ × PeriodOneHminusOne) (ht : t ∈ ball (P.centers ((m:ℕ):ℤ):ℂ) ρ ×ˢ C.source) :
    P.offIndexAbelianFilledQuotient n m t = C.solution n ρ t := by
  have hdom : t ∈ ball (P.centers ((m:ℕ):ℤ):ℂ) (P.radii ((m:ℕ):ℤ)) ×ˢ P.source :=
    ⟨ball_subset_ball (hρR.trans C.outer_lt_assigned).le ht.1,C.subset ht.2⟩
  rw [offIndexAbelianFilledQuotient,dif_pos hdom]
  let E := Classical.choice (nonempty_hillAbelianCauchyEvaluation P m t hdom)
  exact E.chart.solution_eq_on_overlap C n hmn E.radius ρ E.inner_lt E.lt_outer hrρ hρR
    t.2 E.source_mem ht.2 t.1 E.energy_mem ht.1

theorem analytic_offIndexAbelianFilledQuotient (P : HillProductEquationPatch) (n m : ℕ+) (hmn : m ≠ n) :
    AnalyticOnNhd ℂ (P.offIndexAbelianFilledQuotient n m)
      (ball (P.centers ((m:ℕ):ℤ):ℂ) (P.radii ((m:ℕ):ℤ)) ×ˢ P.source) := by
  intro t ht
  obtain ⟨C,hq,ρ,hrρ,hρR,hz⟩ := exists_hillAbelianCauchyChart P m t.2 ht.2 t.1 ht.1
  apply (C.analytic_solution n ρ hrρ hρR t ⟨hz,hq⟩).congr
  filter_upwards [(isOpen_ball.prod C.source_open).mem_nhds ⟨hz,hq⟩] with s hs
  exact (P.offIndexAbelianFilledQuotient_eq_chart n m hmn C ρ hrρ hρR s hs).symm

theorem offIndexAbelianFilledQuotient_equation (P : HillProductEquationPatch) (n m : ℕ+) (hmn : m ≠ n)
    (q : PeriodOneHminusOne) (hq : q ∈ P.source) (z : ℂ)
    (hz : z ∈ ball (P.centers ((m:ℕ):ℤ):ℂ) (P.radii ((m:ℕ):ℤ))) :
    sourceAngularSelectedPolynomial (by norm_num) (by norm_num) (P.sourcePsi q) ((m:ℕ):ℤ) z*
      deriv (fun w => P.offIndexAbelianFilledQuotient n m (w,q)) z+
      (z-sourceStandardRootMidpoint (by norm_num) (by norm_num) (P.sourcePsi q) ((m:ℕ):ℤ))*P.offIndexAbelianFilledQuotient n m (z,q) =
      P.abelianGapNumerator n m (z,q) := by
  obtain ⟨C,hqC,ρ,hrρ,hρR,hzC⟩ := exists_hillAbelianCauchyChart P m q hq z hz
  have hderiv : (fun w => P.offIndexAbelianFilledQuotient n m (w,q)) =ᶠ[𝓝 z] (fun w => C.solution n ρ (w,q)) := by
    filter_upwards [isOpen_ball.mem_nhds hzC] with w hw
    exact P.offIndexAbelianFilledQuotient_eq_chart n m hmn C ρ hrρ hρR (w,q) ⟨hw,hqC⟩
  rw [hderiv.deriv_eq,P.offIndexAbelianFilledQuotient_eq_chart n m hmn C ρ hrρ hρR (z,q) ⟨hzC,hqC⟩]
  exact C.solution_equation n hmn ρ hrρ hρR q hqC z hzC

end HillProductEquationPatch
end NLS.KdV
