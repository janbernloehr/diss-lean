import NLS.ZakharovShabat.FloquetRootProjection

/-! # Uniform local bounds for separated Floquet root projections -/
noncomputable section
set_option autoImplicit false
open Matrix Filter
open scoped Matrix.Norms.Elementwise Topology
namespace NLS.ZakharovShabat

/-- A continuous monodromy family has uniformly bounded algebraic mode
projections near any parameter with nonzero discriminant. No local choice
of roots or normalized eigenvectors is needed. -/
theorem eventually_norm_floquetRootProjection_le
    (M : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (z₀ : ℂ) (hM : ContinuousAt M z₀)
    (hdisc : (M z₀).trace^2-4 ≠ 0) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ z in 𝓝 z₀, ∀ μ ν : ℂ,
      (M z).trace = μ+ν → μ*ν = 1 → ‖floquetRootProjection (M z) μ ν‖ ≤ C := by
  have htr : ContinuousAt (fun z => (M z).trace) z₀ := by
    unfold Matrix.trace
    fun_prop
  have hd : ContinuousAt (fun z => ‖(M z).trace^2-4‖) z₀ :=
    ((htr.pow 2).sub continuousAt_const).norm
  let δ := Real.sqrt (‖(M z₀).trace^2-4‖/2)
  have hp : 0 < ‖(M z₀).trace^2-4‖ := norm_pos_iff.mpr hdisc
  have hδ : 0 < δ := Real.sqrt_pos.mpr (half_pos hp)
  let B := ‖M z₀‖+1
  let T := ‖(M z₀).trace‖+1
  let C := (B+T+1)/δ
  have hC : 0 < C := by dsimp [C,B,T]; positivity
  refine ⟨C,hC,?_⟩
  have hMb : ∀ᶠ z in 𝓝 z₀, ‖M z‖ < B :=
    hM.norm.eventually (gt_mem_nhds (by dsimp [B]; linarith))
  have hTb : ∀ᶠ z in 𝓝 z₀, ‖(M z).trace‖ < T :=
    htr.norm.eventually (gt_mem_nhds (by dsimp [T]; linarith))
  have hdb : ∀ᶠ z in 𝓝 z₀, ‖(M z₀).trace^2-4‖/2 < ‖(M z).trace^2-4‖ :=
    hd.eventually (lt_mem_nhds (half_lt_self hp))
  filter_upwards [hMb,hTb,hdb] with z hzM hzT hzd μ ν hsum hprod
  have hsep : δ^2 ≤ ‖(M z).trace^2-4‖ := by
    dsimp [δ]
    rw [Real.sq_sqrt (half_pos hp).le]
    exact hzd.le
  exact (norm_floquetRootProjection_le_of_discriminant_bound
    (M z) (M z).trace μ ν B δ hδ hzM.le hsum hprod hsep).trans
      (div_le_div_of_nonneg_right (by linarith) hδ.le)

end NLS.ZakharovShabat
