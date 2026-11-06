import NLS.SequenceSpaces.LocallyBoundedRealization
import Mathlib.Logic.Equiv.Nat

noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology
open scoped ENNReal ComplexConjugate Classical

namespace NLS.ComplexAnalysis



variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

theorem analyticOnNhd_tsum_of_summable_uniform_bound
    (f : ℕ → E → ℂ) (U : Set E) (hU : IsOpen U)
    (hf : ∀ n : ℕ, AnalyticOnNhd ℂ (f n) U)
    (M : ℕ → ℝ) (hM : Summable M)
    (hbound : ∀ n : ℕ, ∀ x ∈ U, ‖f n x‖ ≤ M n) :
    AnalyticOnNhd ℂ (fun x => ∑' n : ℕ, f n x) U := by
  let : Fact (1 ≤ (1 : ℝ≥0∞)) := ⟨le_rfl⟩
  let e : ℤ ≃ ℕ := Equiv.intEquivNat
  let S : E → NLS.Coeff 1 := fun x => NLS.Coeff.ofFunctionOrZero 1 (fun z : ℤ => f (e z) x)
  have hs : Summable (fun z : ℤ => M (e z)) := e.summable_iff.mpr hM
  have hb (x : E) (hx : x ∈ U) (z : ℤ) : ‖f (e z) x‖^(1 : ℝ≥0∞).toReal ≤ M (e z) := by
    simpa only [ENNReal.toReal_one,Real.rpow_one] using hbound (e z) x hx
  have hcoords (x : E) (hx : x ∈ U) (z : ℤ) : S x z=f (e z) x :=
    NLS.Coeff.ofFunctionOrZero_apply_of_mem 1 _ (NLS.Coeff.memℓp_of_power_dominated _ _ hs (hb x hx)) z
  have hnorm (x : E) (hx : x ∈ U) : ‖S x‖ ≤ ∑' z : ℤ, M (e z) := by
    have hh := NLS.Coeff.norm_ofFunctionOrZero_rpow_le (p := 1) (by simp) _ _ hs (hb x hx)
    simpa only [ENNReal.toReal_one,Real.rpow_one] using hh
  have hcoordA (z : ℤ) : AnalyticOnNhd ℂ (fun x => S x z) U := by
    intro x hx
    apply (hf (e z) x hx).congr
    filter_upwards [hU.mem_nhds hx] with y hy
    exact (hcoords y hy z).symm
  have hSA : AnalyticOnNhd ℂ S U := NLS.Coeff.analyticOnNhd_of_bounded_coordinatewise S hU hcoordA _ hnorm
  intro x hx
  have ha := ((lp.tsumCLM ℂ ℤ ℂ).analyticAt (S x)).comp (hSA x hx)
  apply ha.congr
  filter_upwards [hU.mem_nhds hx] with y hy
  change (∑' z : ℤ, S y z)=∑' n : ℕ, f n y
  rw [tsum_congr (hcoords y hy)]
  exact e.tsum_eq (fun n => f n y)

end NLS.ComplexAnalysis
