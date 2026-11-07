import NLS.KdV.HillHminusOneDiscriminant
import NLS.SequenceSpaces.PeriodOneMiuraRegularityBound
import NLS.SequenceSpaces.SobolevHomogeneous

/-! Quantitative fractional lifts on one original complex Miura chart. -/
noncomputable section
open Set Metric Complex NLS.WeightedCoeff
namespace NLS.KdV

theorem sobolevToL2_eq_of_raw_coefficients (s : ℝ) (hs : 0 ≤ s)
    (U : WeightedCoeff (Weight.sobolev s) 2) (u : Coeff 2)
    (h : ∀ k, U.val k = u k) : sobolevToL2 hs U = u := by
  apply Subtype.ext
  funext k
  simpa only [sobolevToL2_apply] using h k


theorem HillHminusMiuraChart.exists_local_lift_norm_bound
    (C : HillHminusMiuraChart) (q : PeriodOneHminusOne) (hq : q ∈ C.domain) :
    ∃ V : Set PeriodOneHminusOne, ∃ R : ℝ,
      IsOpen V ∧ q ∈ V ∧ V ⊆ C.domain ∧ 0 ≤ R ∧ ∀ a ∈ V, ‖C.lift a‖ ≤ R := by
  let R := ‖C.lift q‖+1
  have hR : 0 ≤ R := by dsimp only [R]; positivity
  let Vb := C.domain ∩ C.lift ⁻¹' ball 0 R
  have hVb : IsOpen Vb :=
    C.lift_analytic.continuousOn.isOpen_inter_preimage C.domain_open isOpen_ball
  have hqVb : q ∈ Vb := ⟨hq,by simp only [mem_preimage,mem_ball,dist_zero_right,R]; linarith⟩
  exact ⟨Vb,R,hVb,hqVb,fun _ ha => ha.1,hR,
    fun a ha => (mem_ball_zero_iff.mp ha.2).le⟩

theorem HillHminusMiuraChart.fractional_lift_bound_of_norm_bounds
    (C : HillHminusMiuraChart) (r : ℝ) (hr : 1/2 < r) (hr1 : r < 1)
    (M R : ℝ) (hR : 0 ≤ R)
    (b : WeightedCoeff (Weight.sobolev (-r)) 2) (hb : ‖b‖ ≤ M)
    (had : sobolevInclusion (show (-1:ℝ) ≤ -r by linarith) b ∈ C.domain)
    (hlift : ‖C.lift (sobolevInclusion (show (-1:ℝ) ≤ -r by linarith) b)‖ ≤ R) :
    ∃ U : WeightedCoeff (Weight.sobolev (1-r)) 2,
      (∀ k, U.val k = C.lift (sobolevInclusion (show (-1:ℝ) ≤ -r by linarith) b) k) ∧
      ‖U‖ ≤ 2*(M+‖C.energyShift‖+‖negativeSobolevL2Kernel r (by linarith)‖*(R^2+R)) := by
  have hr2 : 1 < r*2 := by linarith
  let L := 2*(M+‖C.energyShift‖+‖negativeSobolevL2Kernel r hr2‖*(R^2+R))
  let a : PeriodOneHminusOne := sobolevInclusion (show (-1:ℝ) ≤ -r by linarith) b
  have himage : ∀ k, (periodOneMiura (C.lift a)).val k = b.val k+(lp.single 2 0 C.energyShift : Coeff 2) k := by
    intro k
    have hh := congrArg (fun x : PeriodOneHminusOne => x.val k) (C.image a had)
    change (periodOneMiura (C.lift a)).val k = a.val k+
      (periodOneL2Inclusion (lp.single 2 0 C.energyShift)).val k at hh
    simpa only [a,sobolevInclusion_apply,periodOneL2Inclusion_apply] using hh
  obtain ⟨U,hU,hUnorm⟩ := exists_periodOneMiura_sobolev_lift_bound r hr2 (C.lift a) b C.energyShift himage
  have hUL : ‖U‖ ≤ L := by
    apply hUnorm.trans
    have hsq : ‖C.lift a‖^2 ≤ R^2 := sq_le_sq₀ (norm_nonneg _) hR |>.mpr hlift
    dsimp only [L]
    exact mul_le_mul_of_nonneg_left
      (add_le_add (add_le_add hb (le_refl ‖C.energyShift‖))
        (mul_le_mul_of_nonneg_left (add_le_add hsq hlift)
          (norm_nonneg (negativeSobolevL2Kernel r hr2)))) (by norm_num)
  exact ⟨U,hU,hUL⟩

theorem HillHminusMiuraChart.exists_local_fractional_lift_bound
    (C : HillHminusMiuraChart) (q : PeriodOneHminusOne) (hq : q ∈ C.domain)
    (r : ℝ) (hr : 1/2 < r) (hr1 : r < 1) (M : ℝ) (hM : 0 ≤ M) :
    ∃ V : Set PeriodOneHminusOne, ∃ R L : ℝ,
      IsOpen V ∧ q ∈ V ∧ V ⊆ C.domain ∧ 0 ≤ R ∧ 0 ≤ L ∧
      ∀ b : WeightedCoeff (Weight.sobolev (-r)) 2, ‖b‖ ≤ M →
        sobolevInclusion (show (-1:ℝ) ≤ -r by linarith) b ∈ V →
        ∃ U : WeightedCoeff (Weight.sobolev (1-r)) 2,
          (∀ k, U.val k = C.lift (sobolevInclusion (show (-1:ℝ) ≤ -r by linarith) b) k) ∧
          ‖C.lift (sobolevInclusion (show (-1:ℝ) ≤ -r by linarith) b)‖ ≤ R ∧ ‖U‖ ≤ L := by
  obtain ⟨V,R,hV,hqV,hVd,hR,hbound⟩ := C.exists_local_lift_norm_bound q hq
  let L := 2*(M+‖C.energyShift‖+‖negativeSobolevL2Kernel r (by linarith)‖*(R^2+R))
  have hL : 0 ≤ L := by dsimp only [L]; positivity
  refine ⟨V,R,L,hV,hqV,hVd,hR,hL,?_⟩
  intro b hb ha
  obtain ⟨U,hU,hUL⟩ := C.fractional_lift_bound_of_norm_bounds r hr hr1 M R hR b hb (hVd ha) (hbound _ ha)
  exact ⟨U,hU,hbound _ ha,hUL⟩

end NLS.KdV
