import NLS.KdV.HminusOneHillPsiFixedShift
import NLS.ZakharovShabat.SourcePsiShiftedEnergyGrowth

/-! Every actual local Hill numerator, and differences of numerators
from ANY two charts, retain entire frequency lifts and sub-sine growth
at ANY common complex reference shift. This provides the growth input
for different-shift period uniqueness; transported periods are separate. -/
noncomputable section
open Set Metric Complex NLS.ZakharovShabat NLS.ComplexAnalysis
open scoped ENNReal Classical
namespace NLS.KdV
namespace MiuraHillPsiFamily

theorem numerator_eq_fixed_root_descent (A : MiuraHillPsiFamily) (n : ℕ+) (u : Coeff 2) (E : ℂ) :
    A.numerator n (E,u) = oddSquareDescent (sourcePsiCandidate (p := 2) ((n:ℕ):ℤ))
      (E,(A.roots ((n:ℕ):ℤ) (hillMiuraDiagonal u):Coeff 2)) :=
  oddSquareDescent_congr_slice (sourceSelectedPsiNumerator A.roots ((n:ℕ):ℤ))
    (sourcePsiCandidate (p := 2) ((n:ℕ):ℤ)) (hillMiuraDiagonal u)
    (A.roots ((n:ℕ):ℤ) (hillMiuraDiagonal u):Coeff 2) (fun _ => rfl) E

theorem numerator_energy_entire (A : MiuraHillPsiFamily) (n : ℕ+) (u : Coeff 2) :
    AnalyticOnNhd ℂ (fun E : ℂ => A.numerator n (E,u)) univ := by
  intro E _
  have hG := analyticOnNhd_sourcePsiCandidateEnergy (by norm_num) (by norm_num) ((n:ℕ):ℤ)
    (E,(A.roots ((n:ℕ):ℤ) (hillMiuraDiagonal u):Coeff 2)) (mem_univ _)
  simpa only [Function.comp_def,← A.numerator_eq_fixed_root_descent n u] using
    hG.comp (f := fun e : ℂ => (e,(A.roots ((n:ℕ):ℤ) (hillMiuraDiagonal u):Coeff 2)))
      (analyticAt_id.prod analyticAt_const)

theorem shifted_numerator_pullback_entire (A : MiuraHillPsiFamily) (n : ℕ+) (u : Coeff 2) (d : ℂ) :
    AnalyticOnNhd ℂ (fun z : ℂ => 2*z*A.numerator n (z^2+d,u)) univ := by
  simpa only [← A.numerator_eq_fixed_root_descent n u] using
    analyticOnNhd_shifted_sourcePsiEnergyLift (by norm_num) (by norm_num) ((n:ℕ):ℤ)
      (A.roots ((n:ℕ):ℤ) (hillMiuraDiagonal u):Coeff 2) d

theorem shifted_numerator_pullback_sub_sine (A : MiuraHillPsiFamily) (n : ℕ+) (u : Coeff 2) (d : ℂ)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ K : ℕ, ∀ k : ℕ, K ≤ k → ∀ z ∈ sphere (0:ℂ) (centralCircleRadius k),
      ‖(2*z*A.numerator n (z^2+d,u))/(-2*sin z)‖ ≤ ε := by
  simpa only [← A.numerator_eq_fixed_root_descent n u] using
    shifted_energy_numerator_sub_sine_growth (by norm_num) (by norm_num) ((n:ℕ):ℤ)
      (A.roots ((n:ℕ):ℤ) (hillMiuraDiagonal u):Coeff 2) d ε hε

end MiuraHillPsiFamily
namespace HillHminusDirichletBall

theorem psiNumerator_energy_entire (B : HillHminusDirichletBall) (A : MiuraHillPsiFamily)
    (q : PeriodOneHminusOne) (n : ℕ+) :
    AnalyticOnNhd ℂ (fun E : ℂ => B.psiNumerator A n (E,q)) univ := by
  intro E _
  exact (A.numerator_energy_entire n (B.miuraBall.actionBall.lift q)
    (E+(B.miuraBall.actionBall.shift:ℂ)) (mem_univ _)).comp
      (f := fun e : ℂ => e+(B.miuraBall.actionBall.shift:ℂ)) (analyticAt_id.add analyticAt_const)

theorem psiNumerator_pullback_at_reference_shift (B : HillHminusDirichletBall) (A : MiuraHillPsiFamily)
    (q : PeriodOneHminusOne) (n : ℕ+) (c z : ℂ) :
    B.psiNumerator A n (z^2-c,q) = A.numerator n
      (z^2+((B.miuraBall.actionBall.shift:ℂ)-c),B.miuraBall.actionBall.lift q) := by
  dsimp only [psiNumerator]
  congr 2
  ring

theorem psiNumerator_arbitrary_shift_pullback_entire (B : HillHminusDirichletBall) (A : MiuraHillPsiFamily)
    (q : PeriodOneHminusOne) (n : ℕ+) (c : ℂ) :
    AnalyticOnNhd ℂ (fun z : ℂ => 2*z*B.psiNumerator A n (z^2-c,q)) univ := by
  simp_rw [B.psiNumerator_pullback_at_reference_shift A q n c]
  exact A.shifted_numerator_pullback_entire n (B.miuraBall.actionBall.lift q) _

theorem psiNumerator_arbitrary_shift_pullback_sub_sine (B : HillHminusDirichletBall) (A : MiuraHillPsiFamily)
    (q : PeriodOneHminusOne) (n : ℕ+) (c : ℂ) (ε : ℝ) (hε : 0 < ε) :
    ∃ K : ℕ, ∀ k : ℕ, K ≤ k → ∀ z ∈ sphere (0:ℂ) (centralCircleRadius k),
      ‖(2*z*B.psiNumerator A n (z^2-c,q))/(-2*sin z)‖ ≤ ε := by
  simp_rw [B.psiNumerator_pullback_at_reference_shift A q n c]
  exact A.shifted_numerator_pullback_sub_sine n (B.miuraBall.actionBall.lift q) _ ε hε

theorem psiNumerator_difference_arbitrary_shift_sub_sine (B C : HillHminusDirichletBall)
    (A D : MiuraHillPsiFamily) (q : PeriodOneHminusOne) (n : ℕ+) (c : ℂ) (ε : ℝ) (hε : 0 < ε) :
    ∃ K : ℕ, ∀ k : ℕ, K ≤ k → ∀ z ∈ sphere (0:ℂ) (centralCircleRadius k),
      ‖(2*z*(B.psiNumerator A n (z^2-c,q)-C.psiNumerator D n (z^2-c,q)))/(-2*sin z)‖ ≤ ε := by
  obtain ⟨KB,hB⟩ := B.psiNumerator_arbitrary_shift_pullback_sub_sine A q n c (ε/2) (by positivity)
  obtain ⟨KC,hC⟩ := C.psiNumerator_arbitrary_shift_pullback_sub_sine D q n c (ε/2) (by positivity)
  refine ⟨max KB KC,?_⟩
  intro k hk z hz
  rw [mul_sub,sub_div]
  exact (norm_sub_le _ _).trans (by
    linarith [hB k ((le_max_left _ _).trans hk) z hz,hC k ((le_max_right _ _).trans hk) z hz])

end HillHminusDirichletBall
end NLS.KdV
