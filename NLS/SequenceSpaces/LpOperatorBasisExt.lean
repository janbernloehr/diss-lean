import Mathlib.Analysis.Normed.Lp.lpSpace
import Mathlib.Analysis.Complex.Basic

/-! # Bounded linear maps determined by the coordinates of any scalar lp space -/
noncomputable section
set_option autoImplicit false
namespace NLS.SequenceSpaces
open Filter Topology
open scoped ENNReal
variable {ι F : Type*} [DecidableEq ι] [NormedAddCommGroup F] [NormedSpace ℂ F]
  {p : ℝ≥0∞} [Fact (1 ≤ p)]

theorem lp_continuousLinearMap_eq_of_single (hp : p ≠ ⊤)
    (A B : lp (fun _ : ι => ℂ) p →L[ℂ] F)
    (he : ∀ n : ι, A (lp.single p n 1)=B (lp.single p n 1)) : A=B := by
  classical
  ext v
  have hsingle (n : ι) : A (lp.single p n (v n))=B (lp.single p n (v n)) := by
    have hh : (lp.single p n (v n) : lp (fun _ : ι => ℂ) p)=v n • lp.single p n 1 := by
      ext m
      by_cases hm : m=n <;> simp [lp.single_apply,hm]
    rw [hh,map_smul,map_smul,he]
  have hA := (A.continuous.tendsto v).comp (lp.hasSum_single hp v)
  have hB := (B.continuous.tendsto v).comp (lp.hasSum_single hp v)
  apply tendsto_nhds_unique hA
  apply hB.congr
  intro s
  simp only [Function.comp_def,map_sum]
  exact Finset.sum_congr rfl (fun n _ => (hsingle n).symm)

end NLS.SequenceSpaces
