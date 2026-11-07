import NLS.SequenceSpaces.QuadraticFrequencyDomain

/-! Principal positive-frequency lifting is jointly BANACH analytic
in the independent complex energy shift and inverse-index l2 data on
ONE open simultaneous slit domain, with a global norm bound. -/
noncomputable section
open Set Metric Complex
open scoped ENNReal Classical
namespace NLS.LpSequence

theorem analyticAt_positiveFrequencyError (α : ℝ) (m : ℕ+)
    (t : ℂ × lp (fun _ : ℕ+ => ℂ) 2) (ht : t ∈ quadraticFrequencyDomain α) :
    AnalyticAt ℂ (positiveFrequencyError α m) t := by
  have hs := (Complex.differentiableOn_sqrt.analyticAt (isOpen_slitPlane.mem_nhds (ht m))).comp
    (f := quadraticLatticeEnergy α m) (analyticAt_quadraticLatticeEnergy α m t)
  exact hs.sub analyticAt_const

theorem analyticOnNhd_positiveFrequencyDisplacement (α : ℝ) (hα : 0 < α) :
    AnalyticOnNhd ℂ (positiveFrequencyDisplacement α hα) (quadraticFrequencyDomain α) := by
  intro t ht
  let U₀ : Set (ℂ × lp (fun _ : ℕ+ => ℂ) 2) := {s | ‖s.1‖ < ‖t.1‖+1 ∧ ‖s.2‖ < ‖t.2‖+1}
  have hU₀ : IsOpen U₀ := (isOpen_lt continuous_fst.norm continuous_const).inter
    (isOpen_lt continuous_snd.norm continuous_const)
  let U := quadraticFrequencyDomain α ∩ U₀
  have hU : IsOpen U := (isOpen_quadraticFrequencyDomain α hα).inter hU₀
  have htU : t ∈ U := ⟨ht,by change ‖t.1‖ < ‖t.1‖+1 ∧ ‖t.2‖ < ‖t.2‖+1; constructor <;> linarith⟩
  have hcoord (m : ℕ+) : AnalyticOnNhd ℂ (fun s => positiveFrequencyDisplacement α hα s m) U := by
    intro s hs
    exact analyticAt_positiveFrequencyError α m s hs.1
  have hbound (s : ℂ × lp (fun _ : ℕ+ => ℂ) 2) (hs : s ∈ U) :
      ‖positiveFrequencyDisplacement α hα s‖ ≤ α⁻¹*(‖t.2‖+1+2*(‖t.1‖+1)) := by
    have hs₀ := hs.2
    change ‖s.1‖ < ‖t.1‖+1 ∧ ‖s.2‖ < ‖t.2‖+1 at hs₀
    exact (norm_positiveFrequencyDisplacement_le α hα s).trans
      (mul_le_mul_of_nonneg_left (by linarith) (inv_nonneg.mpr hα.le))
  exact (analyticOnNhd_positiveL2_of_bounded_coordinatewise (positiveFrequencyDisplacement α hα)
    hU hcoord _ hbound) t htU

theorem positiveFrequencyDisplacement_sq (α : ℝ) (hα : 0 < α)
    (t : ℂ × lp (fun _ : ℕ+ => ℂ) 2) (m : ℕ+) :
    ((α:ℂ)*(m:ℕ)+positiveFrequencyDisplacement α hα t m)^2 = quadraticLatticeEnergy α m t := by
  rw [positiveFrequencyDisplacement_apply,add_sub_cancel]
  exact NLS.ComplexAnalysis.complex_sqrt_sq _

end NLS.LpSequence
