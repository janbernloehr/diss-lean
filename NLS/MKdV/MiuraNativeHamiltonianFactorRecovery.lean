import NLS.MKdV.MiuraNativeHamiltonianActionFibers
import NLS.MKdV.MiuraCartesianRealActionData

/-! # Local native Hamiltonian factors recover all real representatives

Nearby real Cartesian lifts and global action-fiber invariance remove
the source-neighborhood restriction from each local analytic factor.
-/
noncomputable section
open Set Metric Complex NLS.ZakharovShabat
open scoped ENNReal ComplexConjugate
namespace NLS.MKdV.MiuraNativeCartesianChart
variable {s : ℕ} {a : MiuraRealSobolevSource s}

theorem exists_action_factor_global_recovery (C : MiuraNativeCartesianChart s a) (hs : 1 ≤ s) :
    ∃ V : Set MiuraActionMeanTarget, ∃ F : MiuraActionMeanTarget → ℂ,
      IsOpen V ∧ miuraNormalizedNativeActionMeanMap s a.val ∈ V ∧ AnalyticOnNhd ℂ F V ∧
        ∀ b : MiuraRealSobolevSource s, miuraNormalizedNativeActionMeanMap s b.val ∈ V →
          F (miuraNormalizedNativeActionMeanMap s b.val) = miuraSpectralHillHamiltonian s b.val := by
  obtain ⟨W,V₀,F,hW,haW,hWball,hV₀,haV₀,hF,hrec⟩ := C.exists_action_factor
  let z : MiuraRealCartesianTarget :=
    ⟨miuraSobolevNormalizedCartesianMap s a.val,miuraSobolevNormalizedCartesianMap_real s a⟩
  obtain ⟨V₁,hV₁,haV₁,hlift⟩ := exists_miuraCartesian_real_target_action_lift_neighborhood z W hW haW
  have he := miuraNormalizedCartesian_actionMean s a.val a.property
  refine ⟨V₀ ∩ V₁,F,hV₀.inter hV₁,⟨haV₀,he ▸ haV₁⟩,hF.mono inter_subset_left,?_⟩
  intro b hb
  let q : MiuraRealCartesianTarget :=
    ⟨miuraSobolevNormalizedCartesianMap s b.val,miuraSobolevNormalizedCartesianMap_real s b⟩
  have hq : miuraPositiveCartesianActionMean q.val = miuraNormalizedNativeActionMeanMap s b.val :=
    miuraNormalizedCartesian_actionMean s b.val b.property
  obtain ⟨v,hv,hvr,hJ⟩ := hlift q (hq.symm ▸ hb.2)
  have hJ' := hJ.trans hq
  have hf := (hrec v hv).2
  rw [hJ'] at hf
  exact hf.trans (C.hamiltonian_eq_of_normalized_actionMean hs b v (hWball hv) hvr hJ')

end NLS.MKdV.MiuraNativeCartesianChart
