import NLS.SequenceSpaces.LocallyBoundedRealization

/-! Whole Hilbert bounds extend across finite coordinate exceptions.
The dense set may depend on the finite coordinates being tested. -/
noncomputable section
set_option autoImplicit false
open Set Filter Topology
open scoped ENNReal
namespace NLS.Coeff

theorem exists_l2_of_dense_finite_coordinate_bounds
    {E : Type*} [PseudoMetricSpace E]
    (U : Set E) (hU : IsOpen U) (f : E → ℤ → ℂ)
    (hc : ∀ n, ContinuousOn (fun x => f x n) U) (M : ℝ) (hM : 0≤M)
    (hd : ∀ S : Finset ℤ, U⊆closure {y∈U | ∃ b : Coeff 2,
      ‖b‖≤M ∧ ∀ n∈S, b n=f y n}) (x : E) (hx : x∈U) :
    ∃ b : Coeff 2, (∀ n, b n=f x n) ∧ ‖b‖≤M := by
  have hsum (S : Finset ℤ) : ∑ n∈S, ‖f x n‖^2≤M^2 := by
    obtain ⟨y,hy,ht⟩ := mem_closure_iff_seq_limit.mp (hd S hx)
    have hlim : Tendsto (fun i => ∑ n∈S, ‖f (y i) n‖^2) atTop
        (𝓝 (∑ n∈S, ‖f x n‖^2)) := by
      apply tendsto_finsetSum S
      intro n _
      exact (((hc n).continuousAt (hU.mem_nhds hx)).tendsto.comp ht).norm.pow 2
    apply le_of_tendsto hlim
    filter_upwards [] with i
    obtain ⟨b,hb,he⟩ := (hy i).2
    calc
      _ = ∑ n∈S, ‖b n‖^2 := Finset.sum_congr rfl (fun n hn => by rw [he n hn])
      _ ≤ ‖b‖^2 := by
        simpa only [ENNReal.toReal_ofNat,Real.rpow_two] using
          lp.sum_rpow_le_norm_rpow (by norm_num : 0<(2 : ℝ≥0∞).toReal) b S
      _ ≤ M^2 := pow_le_pow_left₀ (norm_nonneg _) hb 2
  let b : Coeff 2 := ⟨f x,memℓp_gen' (C := M^2) (fun S => by
    simpa only [ENNReal.toReal_ofNat,Real.rpow_two] using hsum S)⟩
  refine ⟨b,fun _ => rfl,?_⟩
  apply lp.norm_le_of_forall_sum_le (by norm_num : 0<(2 : ℝ≥0∞).toReal) hM
  intro S
  simpa only [ENNReal.toReal_ofNat,Real.rpow_two] using hsum S

end NLS.Coeff
