import NLS.ComplexAnalysis.EntireLimit
import NLS.ComplexAnalysis.EntireEvenSquareDescent

/-! # Locally uniform limits after removing a squared spectral variable

An odd characteristic has the form z H(z²). Uniform bounds on frequency
circles control the energy circles, and the maximum principle fills zero
energy without choosing a continuous square root there.
-/
noncomputable section
open Set Metric Complex Filter Topology
namespace NLS.ComplexAnalysis

theorem tendstoLocallyUniformlyOn_of_squared_characteristic
    (F H : ℕ → ℂ → ℂ) (f h : ℂ → ℂ)
    (hH : ∀ N, Differentiable ℂ (H N)) (hh : Differentiable ℂ h)
    (hF : ∀ N z, F N z = z*H N (z^2)) (hf : ∀ z, f z = z*h (z^2))
    (ht : TendstoLocallyUniformlyOn F f atTop univ) :
    TendstoLocallyUniformlyOn H h atTop univ := by
  apply tendstoLocallyUniformlyOn_of_forall_exists_nhds
  intro E _
  let R := max ‖E‖ 1+1
  have hR : 1 < R := by dsimp only [R]; linarith [le_max_right ‖E‖ 1]
  have hER : ‖E‖ < R := by dsimp only [R]; linarith [le_max_left ‖E‖ 1]
  refine ⟨closedBall (0 : ℂ) R,nhdsWithin_le_nhds ?_,?_⟩
  · exact mem_of_superset (isOpen_ball.mem_nhds (by
      simpa only [mem_ball,dist_zero_right] using hER)) ball_subset_closedBall
  · have hu := (tendstoLocallyUniformlyOn_iff_tendstoUniformlyOn_of_compact
      (isCompact_closedBall (0 : ℂ) (R+1))).mp (ht.mono (subset_univ _))
    rw [Metric.tendstoUniformlyOn_iff] at hu ⊢
    intro ε hε
    filter_upwards [hu (ε/2) (half_pos hε)] with N hN
    intro w hw
    have hb : ‖H N w-h w‖ ≤ ε/2 := by
      apply Complex.norm_le_of_forall_mem_frontier_norm_le isBounded_ball
        ((hH N).sub hh).diffContOnCl
      · intro v hv
        rw [frontier_ball (0 : ℂ) (by linarith : R ≠ 0)] at hv
        have hnv : ‖v‖ = R := by simpa only [mem_sphere,dist_zero_right] using hv
        let z := Complex.sqrt v
        have hzsq : z^2 = v := complex_sqrt_sq v
        have hnz : ‖z‖^2 = R := by rw [← norm_pow,hzsq,hnv]
        have hz1 : 1 ≤ ‖z‖ := by nlinarith [norm_nonneg z]
        have hzR : ‖z‖ ≤ R+1 := by nlinarith [norm_nonneg z]
        have hbound := hN z (by simpa only [mem_closedBall,dist_zero_right] using hzR)
        rw [dist_eq_norm,hF N z,hf z,← mul_sub,hzsq,norm_mul] at hbound
        rw [norm_sub_rev] at hbound
        exact (le_mul_of_one_le_left (norm_nonneg (H N v-h v)) hz1).trans hbound.le
      · simpa only [closure_ball (0 : ℂ) (by linarith : R ≠ 0)] using hw
    rw [dist_eq_norm]
    simpa only [norm_sub_rev] using hb.trans_lt (half_lt_self hε)

theorem deriv_of_squared_characteristic (f h : ℂ → ℂ)
    (he : ∀ z, f z = z*h (z^2)) (z : ℂ) (hh : DifferentiableAt ℂ h (z^2)) :
    deriv f z = h (z^2)+2*z^2*deriv h (z^2) := by
  have hc := (hasDerivAt_id z).mul (hh.hasDerivAt.comp z ((hasDerivAt_id z).pow 2))
  change HasDerivAt (fun w => w*h (w^2)) _ z at hc
  rw [← funext he] at hc
  rw [hc.deriv]
  simp only [Function.comp_apply,Pi.pow_apply,id_eq,Nat.cast_ofNat,Nat.reduceSub,pow_one,mul_one,one_mul]
  ring

end NLS.ComplexAnalysis
