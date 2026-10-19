import NLS.SequenceSpaces.WeightedFiniteBlock
import NLS.SequenceSpaces.WeightedCoefficientLimit
import NLS.SequenceSpaces.FourierTail
import NLS.ComplexAnalysis.IntegralMajorantUnit

/-! # Integrating bounded weighted coordinates

Finite blocks realize coordinate integrals with a weighted norm bound without measurability assumptions on chosen full sequences.
-/

noncomputable section
open Set Complex Filter Topology MeasureTheory
open scoped ENNReal
namespace NLS.WeightedCoeff
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- Integrating continuous raw coordinates with a uniform weighted bound
produces an actual weighted sequence. Finite blocks avoid any assumption
that a chosen full sequence realization is strongly measurable. -/
theorem exists_interval_integral_of_bounded_coordinates
    (w : Weight) (F : ℝ → ℤ → ℂ) (hF : ∀ n, Continuous (fun x => F x n))
    (g : ℝ → ℂ) (hg : Continuous g) (C : ℝ) (hC : 0 ≤ C)
    (hb : ∀ x ∈ Icc (0:ℝ) 1, ∃ a : WeightedCoeff w p,
      (∀ n, a.val n = F x n) ∧ ‖a‖ ≤ C)
    (t : Icc (0:ℝ) 1) :
    ∃ a : WeightedCoeff w p,
      (∀ n, a.val n = ∫ x in (0:ℝ)..t.val, g x*F x n) ∧
      ‖a‖ ≤ C*(∫ x in (0:ℝ)..1, ‖g x‖) := by
  classical
  let H (N : ℕ) (x : ℝ) := finiteBlock (p := p) w (Coeff.lowFrequencies N) (F x)
  have hH (N : ℕ) : Continuous (H N) := continuous_iff_continuousAt.mpr
    (fun x => continuousAt_finiteBlock w _ F x (fun n _ => (hF n).continuousAt))
  have hHC (N : ℕ) (x : ℝ) (hx : x ∈ Icc (0:ℝ) 1) : ‖H N x‖ ≤ C := by
    obtain ⟨a,ha,han⟩ := hb x hx
    have he : H N x = truncate w p (Coeff.lowFrequencies N) a := by
      apply Subtype.ext
      funext n
      simp [H,ha]
    rw [he]
    exact (norm_truncate_le w p _ a).trans han
  let A (N : ℕ) : WeightedCoeff w p := ∫ x in (0:ℝ)..t.val, g x • H N x
  have hA (N : ℕ) : ‖A N‖ ≤ C*(∫ x in (0:ℝ)..1, ‖g x‖) := by
    apply NLS.ComplexAnalysis.norm_integral_unit_le_mul_integral_norm
      (fun x => g x • H N x) (hg.smul (hH N)) g hg C hC _ t
    intro x hx
    rw [norm_smul]
    simpa only [mul_comm] using mul_le_mul_of_nonneg_left (hHC N x hx) (norm_nonneg (g x))
  have hcoeff (N : ℕ) (n : ℤ) (hn : n.natAbs < N) :
      (A N).val n = ∫ x in (0:ℝ)..t.val, g x*F x n := by
    change evalCLM w p n (∫ x in (0:ℝ)..t.val, g x • H N x) = _
    have hi := (evalCLM w p n).intervalIntegral_comp_comm
      (f := fun x => g x • H N x) (μ := volume) (a := 0) (b := t.val)
      ((hg.smul (hH N)).intervalIntegrable _ _)
    simpa only [evalCLM_apply,smul_val,H,finiteBlock_val,Coeff.mem_lowFrequencies,if_pos hn] using! hi.symm
  apply exists_of_bounded_coefficientwise_tendsto (l := atTop) w A _ _ hA
  intro n
  apply tendsto_const_nhds.congr'
  filter_upwards [eventually_ge_atTop (n.natAbs+1)] with N hN
  exact (hcoeff N n (by omega)).symm

end NLS.WeightedCoeff
