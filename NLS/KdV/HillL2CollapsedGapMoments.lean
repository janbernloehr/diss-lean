import NLS.KdV.HillL2GapCutBoundary
import NLS.KdV.HillRealGapIntegrals

/-! # Exact vanishing of actual high moments at collapsed gaps

At a double characteristic zero, the trace derivative also vanishes.
Deflation and a disc unit root then fill the logarithmic derivative
holomorphically through that point. Its polynomial contour integrals
vanish. Thus the actual source moments and real gap integrals agree
exactly in the collapsed high-gap case, at every hierarchy level.
-/

noncomputable section
open Set Metric Complex
open NLS.ComplexAnalysis
namespace NLS.KdV

theorem HillRealHighGapPair.trace_deriv_zero_of_collapsed
    (q : Coeff 2) (n : ℕ) (p : HillRealHighGapPair q n) (he : p.left = p.right) :
    deriv (hillL2Discriminant q) p.left = 0 := by
  have hδ := p.deriv_zero_of_collapsed q n he
  have hd := (((analyticOnNhd_hillL2Discriminant q p.left (mem_univ _)).differentiableAt.hasDerivAt.pow 2).sub_const 4).deriv
  have hder : deriv (hillL2Radicand q) p.left =
      (2*hillL2Discriminant q p.left)*deriv (hillL2Discriminant q) p.left := by
    change deriv (fun z : ℂ => hillL2Discriminant q z^2-4) p.left = _
    simpa only [Pi.pow_apply,Nat.cast_ofNat,Nat.add_one_sub_one,pow_one] using hd
  have hDne : hillL2Discriminant q p.left ≠ 0 := by
    intro hz
    have h := p.left_zero
    simp [hillL2Radicand,hz] at h
  rw [hδ] at hder
  exact (mul_eq_zero.mp hder.symm).resolve_left (mul_ne_zero (by norm_num) hDne)

theorem HillRealHighGapPair.collapsed_moment_zero
    (q : WeightedCoeff SpectralWeight.one.toWeight 2)
    (hq : SpectralWeight.one.toCoeff q ∈ Coeff.paritySubspace 0)
    (n : ℕ) (hn : 1 ≤ n) (hcut : 8*‖q‖ ≤ (n : ℝ))
    (p : HillRealHighGapPair (SpectralWeight.one.toCoeff q) n) (he : p.left = p.right) (m : ℕ) :
    hillL2HighContourMoment n m (SpectralWeight.one.toCoeff q) = 0 := by
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  let N := deriv (hillL2Discriminant (SpectralWeight.one.toCoeff q))
  let Q := twoZeroQuotient (hillL2Radicand (SpectralWeight.one.toCoeff q)) p.left p.right
  obtain ⟨hQ,hfactor,hunit⟩ := p.deflated_unit q n hn
  obtain ⟨h,hh,hhunit⟩ := exists_analytic_squareRoot_on_ball Q (freeHillValue n : ℂ) (n : ℝ)
    hnpos (hQ.mono ball_subset_closedBall) (fun z hz => hunit z (ball_subset_closedBall hz))
  let B : ℂ → ℂ := fun z => (z-p.left)*h z
  have hNa : N p.left = 0 := p.trace_deriv_zero_of_collapsed _ n he
  have hloc := p.localization q hq n hn hcut
  have ha : (p.left : ℂ) ∈ ball (freeHillValue n : ℂ) (n : ℝ) := by
    rw [mem_ball,dist_eq_norm,← ofReal_sub,norm_real,Real.norm_eq_abs]
    linarith [hloc.1]
  have hB : AnalyticOnNhd ℂ B (ball (freeHillValue n : ℂ) (n : ℝ)) :=
    (analyticOnNhd_id.sub analyticOnNhd_const).mul hh
  have hBsq (z : ℂ) (hz : z ∈ ball (freeHillValue n : ℂ) (n : ℝ)) :
      B z^2 = hillL2Radicand (SpectralWeight.one.toCoeff q) z := by
    dsimp only [B]
    rw [mul_pow,(hhunit z hz).2,hfactor z]
    dsimp only [Q]
    rw [he]
    ring
  have hcircle (z : ℂ) (hz : z ∈ sphere (freeHillValue n : ℂ) (3*(n : ℝ)/4)) :
      z ∈ ball (freeHillValue n : ℂ) (n : ℝ) := by
    rw [mem_ball,mem_sphere.mp hz]
    linarith
  have hsource (z : ℂ) (hz : z ∈ sphere (freeHillValue n : ℂ) (3*(n : ℝ)/4)) :
      (z,SpectralWeight.one.toCoeff q) ∈ hillL2ContinuationDomain := by
    apply hillL2Continuation_high_annulus q hq n hn hcut (3*(n : ℝ)/4) (3*(n : ℝ)/4)
      (by linarith) (by linarith) z
    exact ⟨sphere_subset_closedBall hz,fun ht => sphere_disjoint_ball.le_bot ⟨hz,ht⟩⟩
  have hBne (z : ℂ) (hz : z ∈ sphere (freeHillValue n : ℂ) (3*(n : ℝ)/4)) : B z ≠ 0 := by
    intro hzB
    have hδ : hillL2Radicand (SpectralWeight.one.toCoeff q) z ≠ 0 :=
      (hillL2SourceFamily.continuationDomain_subset (hsource z hz)).2
    apply hδ
    rw [← hBsq z (hcircle z hz),hzB]
    norm_num
  have hS : AnalyticOnNhd ℂ (fun z => hillL2ContinuedRoot (z,SpectralWeight.one.toCoeff q))
      (sphere (freeHillValue n : ℂ) (3*(n : ℝ)/4)) := by
    intro z hz
    exact (analyticOnNhd_hillL2ContinuedRoot _ (hsource z hz)).comp
      (f := fun z : ℂ => (z,SpectralWeight.one.toCoeff q)) (analyticAt_id.prod analyticAt_const)
  obtain ⟨k,hk,hmatch⟩ := exists_fixed_sign_of_sq_eq_on_preconnected
    (fun z => hillL2ContinuedRoot (z,SpectralWeight.one.toCoeff q)) B
    (sphere (freeHillValue n : ℂ) (3*(n : ℝ)/4))
    (isPreconnected_sphere (by simp) _ _) hS.continuousOn (hB.mono hcircle).continuousOn
    (fun z hz => (hillL2ContinuedRoot_sq _ (hsource z hz)).trans (hBsq z (hcircle z hz)).symm) hBne
  have hkne : k ≠ 0 := by rcases hk with rfl | rfl <;> norm_num
  let g : ℂ → ℂ := fun z => dslope N p.left z/(k*h z)
  have hN : AnalyticOnNhd ℂ N univ := (analyticOnNhd_hillL2Discriminant _).deriv
  have hg : AnalyticOnNhd ℂ g (ball (freeHillValue n : ℂ) (n : ℝ)) := by
    intro z hz
    exact (analyticOnNhd_dslope_of_analytic N _ p.left (hN.mono (subset_univ _)) ha z hz).div
      (analyticAt_const.mul (hh z hz)) (mul_ne_zero hkne (hhunit z hz).1)
  have heq (z : ℂ) (hz : z ∈ sphere (freeHillValue n : ℂ) (3*(n : ℝ)/4)) :
      deriv (hillL2Discriminant (SpectralWeight.one.toCoeff q)) z /
        hillL2ContinuedRoot (z,SpectralWeight.one.toCoeff q) = g z := by
    have hza : z ≠ (p.left : ℂ) := by
      intro hez
      apply hBne z hz
      simp [B,hez]
    dsimp only [g]
    rw [dslope_of_ne N hza,slope_def_field,hNa,sub_zero,hmatch z hz]
    dsimp only [B,N]
    field_simp
  rw [hillL2HighContourMoment_arnold_radius q hq n hn hcut (3*(n : ℝ)/4)
    (by linarith) (by linarith) m]
  have hi : (∮ z in C((freeHillValue n : ℂ),3*(n : ℝ)/4),
      z^(m+1)*deriv (hillL2Discriminant (SpectralWeight.one.toCoeff q)) z /
        hillL2ContinuedRoot (z,SpectralWeight.one.toCoeff q)) = 0 := by
    calc
      _ = ∮ z in C((freeHillValue n : ℂ),3*(n : ℝ)/4), z^(m+1)*g z := by
        apply circleIntegral.integral_congr (by positivity)
        intro z hz
        dsimp only
        rw [mul_div_assoc,heq z hz]
      _ = 0 := (DiffContOnCl.mk_ball
        (((analyticOnNhd_id.pow (m+1)).mul (hg.mono
          (closedBall_subset_ball (by linarith : 3*(n : ℝ)/4 < n)))).differentiableOn.mono ball_subset_closedBall)
        (((analyticOnNhd_id.pow (m+1)).mul (hg.mono
          (closedBall_subset_ball (by linarith : 3*(n : ℝ)/4 < n)))).continuousOn)).circleIntegral_eq_zero (by positivity)
  rw [hi,mul_zero]

theorem hillL2HighContourMoment_eq_gapIntegral_of_closed
    (q : WeightedCoeff SpectralWeight.one.toWeight 2)
    (hq : SpectralWeight.one.toCoeff q ∈ Coeff.paritySubspace 0)
    (hr : IsRealHillPotential (SpectralWeight.one.toCoeff q)) (n : ℕ) (hn : 2 ≤ n)
    (hcut : 8*‖q‖ ≤ (n : ℝ))
    (hc : hillRealLabels q hq hr (2*n-1) = hillRealLabels q hq hr (2*n)) (m : ℕ) :
    hillL2HighContourMoment n m (SpectralWeight.one.toCoeff q) =
      (hillRealGapIntegral q hq hr n m : ℂ) := by
  obtain ⟨p,hl,hu⟩ := hillRealLabels_high_pair q hq hr n hn hcut
  have hp : p.left = p.right := hl.symm.trans (hc.trans hu)
  rw [p.collapsed_moment_zero q hq n (by omega) hcut hp m,
    hillRealGapIntegral_closed q hq hr n m hc,ofReal_zero]

end NLS.KdV
