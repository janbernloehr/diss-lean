import NLS.SequenceSpaces.PositiveScalarExtension
import NLS.SequenceSpaces.FunctionOrZero
import NLS.SequenceSpaces.BoundedCoordinateAnalytic

/-! A locally bounded absolute positive-index series with analytic
coordinates assembles into an actual analytic l1 map. Summation then
gives full Banach-source analyticity of the literal infinite series. -/
noncomputable section
open Set Metric Filter Topology NLS.LpSequence
open scoped ENNReal Classical
namespace NLS.Coeff

def positiveSummableRealization (u : ℕ+ → ℂ) : Coeff 1 :=
  ofFunctionOrZero 1 (positiveScalarExtension u)

theorem positiveSummableRealization_apply (u : ℕ+ → ℂ)
    (hu : Summable (fun m => ‖u m‖)) (k : ℤ) :
    positiveSummableRealization u k=positiveScalarExtension u k := by
  apply ofFunctionOrZero_apply_of_mem
  apply memℓp_gen
  simpa using summable_norm_positiveScalarExtension u hu

theorem norm_positiveSummableRealization (u : ℕ+ → ℂ)
    (hu : Summable (fun m => ‖u m‖)) :
    ‖positiveSummableRealization u‖=∑' m : ℕ+, ‖u m‖ := by
  rw [lp.norm_eq_tsum_rpow (by norm_num : 0 < (1:ℝ≥0∞).toReal)]
  simp only [ENNReal.toReal_one,one_div_one,Real.rpow_one,positiveSummableRealization_apply u hu]
  have he := positiveEmbedding.injective.tsum_eq (f := fun k : ℤ => ‖positiveScalarExtension u k‖) (by
    intro k hk
    by_contra hn
    exact hk (by
      dsimp only
      rw [positiveScalarExtension_zero_of_not_mem_range u k hn,norm_zero]))
  change (∑' m : ℕ+, ‖positiveScalarExtension u ((m:ℕ):ℤ)‖)=_ at he
  simpa only [positiveScalarExtension_apply] using he.symm

theorem tsum_positiveSummableRealization (u : ℕ+ → ℂ)
    (hu : Summable (fun m => ‖u m‖)) :
    (∑' k : ℤ, positiveSummableRealization u k)=∑' m : ℕ+, u m := by
  simp only [positiveSummableRealization_apply u hu,tsum_positiveScalarExtension]

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

theorem analyticOnNhd_positiveSummableRealization
    (u : E → ℕ+ → ℂ) (U : Set E)
    (hcoord : ∀ m : ℕ+, AnalyticOnNhd ℂ (fun x => u x m) U)
    (hsum : ∀ x ∈ U, Summable (fun m => ‖u x m‖))
    (hlocal : ∀ x ∈ U, ∃ V : Set E, IsOpen V ∧ x ∈ V ∧ V ⊆ U ∧
      ∃ M : ℝ, ∀ y ∈ V, (∑' m : ℕ+, ‖u y m‖) ≤ M) :
    AnalyticOnNhd ℂ (fun x => positiveSummableRealization (u x)) U := by
  intro x hx
  obtain ⟨V,hV,hxV,hVU,M,hbound⟩ := hlocal x hx
  have hcoords (k : ℤ) : AnalyticOnNhd ℂ (fun y => positiveSummableRealization (u y) k) V := by
    intro y hy
    by_cases hk : k ∈ range positiveEmbedding
    · obtain ⟨m,rfl⟩ := hk
      apply (hcoord m y (hVU hy)).congr
      filter_upwards [hV.mem_nhds hy] with z hz
      rw [positiveSummableRealization_apply _ (hsum z (hVU hz))]
      change u z m=positiveScalarExtension (u z) ((m:ℕ):ℤ)
      rw [positiveScalarExtension_apply]
    · apply analyticAt_const.congr
      filter_upwards [hV.mem_nhds hy] with z hz
      rw [positiveSummableRealization_apply _ (hsum z (hVU hz)),
        positiveScalarExtension_zero_of_not_mem_range _ k hk]
  apply analyticOnNhd_of_bounded_coordinatewise
    (fun y => positiveSummableRealization (u y)) hV hcoords M _ x hxV
  intro y hy
  rw [norm_positiveSummableRealization _ (hsum y (hVU hy))]
  exact hbound y hy

theorem analyticOnNhd_positive_tsum_of_locally_bounded_absolute
    (u : E → ℕ+ → ℂ) (U : Set E) (hU : IsOpen U)
    (hcoord : ∀ m : ℕ+, AnalyticOnNhd ℂ (fun x => u x m) U)
    (hsum : ∀ x ∈ U, Summable (fun m => ‖u x m‖))
    (hlocal : ∀ x ∈ U, ∃ V : Set E, IsOpen V ∧ x ∈ V ∧ V ⊆ U ∧
      ∃ M : ℝ, ∀ y ∈ V, (∑' m : ℕ+, ‖u y m‖) ≤ M) :
    AnalyticOnNhd ℂ (fun x => ∑' m : ℕ+, u x m) U := by
  have ha := analyticOnNhd_positiveSummableRealization u U hcoord hsum hlocal
  intro x hx
  have hs := ((lp.tsumCLM ℂ ℤ ℂ).analyticAt _).comp (f := fun y => positiveSummableRealization (u y)) (ha x hx)
  apply hs.congr
  filter_upwards [hU.mem_nhds hx] with y hy
  exact tsum_positiveSummableRealization (u y) (hsum y hy)

end NLS.Coeff
