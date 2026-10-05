import NLS.SequenceSpaces.HilbertScalarGradient
import NLS.SequenceSpaces.RealCoeff

/-! # Quantitative local concavity from the ℓ² gradient derivative

A scalar analytic function whose gradient derivative is minus twice the
identity at zero has Hessian bounded above by minus the squared norm on
real directions throughout a sufficiently small complex neighborhood.
-/
noncomputable section
open Set Metric Complex
open scoped ComplexConjugate
namespace NLS.Coeff

/-- Real inclusion preserves the Hilbert sequence norm. -/
theorem norm_real_hilbert_inclusion (a : RealCoeff 2) : ‖RealCoeff.complexCLM 2 a‖ = ‖a‖ := by
  apply le_antisymm
  · exact lp.norm_mono (by norm_num) (fun n => by simp)
  · exact lp.norm_mono (by norm_num) (fun n => by simp)

/-- On real directions the bilinear self-pairing is the squared Hilbert norm. -/
theorem dualPairing_real_self (a : RealCoeff 2) :
    dualPairing (RealCoeff.complexCLM 2 a) (RealCoeff.complexCLM 2 a) = (‖a‖^2:ℝ) := by
  have he : dualPairing (RealCoeff.complexCLM 2 a) (RealCoeff.complexCLM 2 a) =
      inner ℂ (RealCoeff.complexCLM 2 a) (RealCoeff.complexCLM 2 a) := by
    rw [dualPairing_apply,lp.inner_eq_tsum]
    apply tsum_congr
    intro n
    rw [RCLike.inner_apply']
    change (a n:ℂ)*(a n:ℂ) = star (a n:ℂ)*(a n:ℂ)
    rw [Complex.star_def,Complex.conj_ofReal]
  simpa only [inner_self_eq_norm_sq_to_K,norm_real_hilbert_inclusion,ofReal_pow] using! he


/-- Continuity of the analytic gradient derivative gives the exact local
strict-concavity bound required for the renormalized Hamiltonian. -/
theorem exists_ball_hessian_le_negative_norm_sq
    (H : Coeff 2 → ℂ) (V : Set (Coeff 2)) (hV : IsOpen V) (h0 : (0:Coeff 2) ∈ V)
    (hH : AnalyticOnNhd ℂ H V)
    (hd0 : fderiv ℂ (scalarGradient H) 0 = (-2:ℂ) • ContinuousLinearMap.id ℂ (Coeff 2)) :
    ∃ r : ℝ, 0 < r ∧ ball (0:Coeff 2) r ⊆ V ∧
      ∀ b ∈ ball (0:Coeff 2) r, ∀ J : RealCoeff 2,
        (fderiv ℂ (fderiv ℂ H) b (RealCoeff.complexCLM 2 J) (RealCoeff.complexCLM 2 J)).re ≤ -‖J‖^2 := by
  have hG := analyticOnNhd_scalarGradient H hH
  have hclose := (hG.fderiv 0 h0).continuousAt.eventually
    (ball_mem_nhds (fderiv ℂ (scalarGradient H) 0) (by norm_num : (0:ℝ) < 1))
  obtain ⟨r,hr,hball⟩ := Metric.mem_nhds_iff.mp (Filter.inter_mem (hV.mem_nhds h0) hclose)
  refine ⟨r,hr,fun b hb => (hball hb).1,?_⟩
  intro b hb J
  let j := RealCoeff.complexCLM 2 J
  let L := fderiv ℂ (scalarGradient H) b - fderiv ℂ (scalarGradient H) 0
  have hL : ‖L‖ ≤ 1 := (show ‖L‖ < 1 from by simpa only [L,dist_eq_norm,Set.mem_ofPred_eq] using! (hball hb).2).le
  have hbound : ‖dualPairing (L j) j‖ ≤ ‖J‖^2 := by
    calc
      ‖dualPairing (L j) j‖ ≤ ‖L j‖ * ‖j‖ := norm_dualPairing_le _ _
      _ ≤ (‖L‖ * ‖j‖) * ‖j‖ := mul_le_mul_of_nonneg_right (L.le_opNorm j) (norm_nonneg _)
      _ ≤ (1 * ‖j‖) * ‖j‖ := by gcongr
      _ = ‖J‖^2 := by rw [norm_real_hilbert_inclusion]; ring
  have he : fderiv ℂ (scalarGradient H) b j = L j + (-2:ℂ) • j := by
    simp [L,hd0]
  have hess : fderiv ℂ (fderiv ℂ H) b j j = dualPairing (L j) j - 2*(‖J‖^2:ℝ) := by
    rw [hessian_eq_dualPairing_gradient_derivative H b (hH b (hball hb).1),he]
    simp only [map_add,map_smul,add_apply,smul_apply,
      smul_eq_mul]
    rw [show dualPairing j j = (‖J‖^2:ℝ) from dualPairing_real_self J]
    ring
  have hreal : (dualPairing (L j) j).re ≤ ‖J‖^2 := (Complex.re_le_norm _).trans hbound
  rw [hess]
  simp only [sub_re,mul_re,re_ofNat,im_ofNat,ofReal_re,ofReal_im,mul_zero,sub_zero]
  linarith

end NLS.Coeff
