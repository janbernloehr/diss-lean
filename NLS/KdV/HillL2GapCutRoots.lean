import NLS.KdV.HillCanonicalRealLabels
import NLS.KdV.HillL2ContourDeformation
import NLS.ComplexAnalysis.TwoZeroDeflation
import NLS.ComplexAnalysis.AnalyticTwoZeroRoot
import NLS.ComplexAnalysis.ContinuousSquareRootPath
import Mathlib.Analysis.Normed.Module.Connected

/-! # Actual high Hill roots on the complete local gap complement

Deflating the exact characteristic orders gives a nowhere-zero analytic
unit, including at a collapsed gap. The shared disc square-root theorem
and standard endpoint root give a root on the full cut complement. One
connected isolating circle fixes its sign from the actual L2 source root.
-/

noncomputable section
open Set Metric Complex
open NLS.ComplexAnalysis
namespace NLS.KdV

theorem HillRealHighGapPair.deriv_zero_of_collapsed
    (q : Coeff 2) (n : ℕ) (p : HillRealHighGapPair q n) (he : p.left = p.right) :
    deriv (hillL2Radicand q) p.left = 0 := by
  have ho := p.orders p.left p.left_mem
  rw [he] at ho
  simp only [Multiset.insert_eq_cons,Multiset.count_cons,Multiset.count_singleton,ite_true] at ho
  by_contra hd
  have horder := (analyticOnNhd_hillL2Radicand q p.left (mem_univ _)).analyticOrderAt_eq_one_of_zero_deriv_ne_zero
    p.left_zero hd
  have hone : analyticOrderNatAt (hillL2Radicand q) p.left = 1 := congrArg ENat.toNat horder
  rw [he] at hone
  omega

theorem HillRealHighGapPair.deflated_unit
    (q : WeightedCoeff SpectralWeight.one.toWeight 2)
    (n : ℕ) (hn : 1 ≤ n) (p : HillRealHighGapPair (SpectralWeight.one.toCoeff q) n) :
    AnalyticOnNhd ℂ (twoZeroQuotient (hillL2Radicand (SpectralWeight.one.toCoeff q)) p.left p.right)
      (closedBall (freeHillValue n : ℂ) (n : ℝ)) ∧
    (∀ z, hillL2Radicand (SpectralWeight.one.toCoeff q) z =
      (z-p.left)*(z-p.right)*twoZeroQuotient (hillL2Radicand (SpectralWeight.one.toCoeff q)) p.left p.right z) ∧
    ∀ z ∈ closedBall (freeHillValue n : ℂ) (n : ℝ),
      twoZeroQuotient (hillL2Radicand (SpectralWeight.one.toCoeff q)) p.left p.right z ≠ 0 := by
  have hf := (analyticOnNhd_hillL2Radicand (SpectralWeight.one.toCoeff q)).mono
    (subset_univ (closedBall (freeHillValue n : ℂ) (n : ℝ)))
  have hdouble : (p.left : ℂ) = (p.right : ℂ) →
      deriv (hillL2Radicand (SpectralWeight.one.toCoeff q)) p.left = 0 := by
    intro he
    exact p.deriv_zero_of_collapsed _ _ (Complex.ofReal_inj.mp he)
  refine ⟨analyticOnNhd_twoZeroQuotient _ _ p.left p.right hf p.left_mem p.right_mem,
    twoZeroQuotient_factor _ p.left p.right p.left_zero p.right_zero hdouble,?_⟩
  intro z hz
  exact twoZeroQuotient_ne_zero _ _ p.left p.right z hf p.left_mem p.right_mem hz
    p.left_zero p.right_zero hdouble
    (fun hzero => (p.zeros_iff z (openHillStrip_subset n (hillClosedBall_subset_openStrip n hn hz))).mp hzero)
    (fun _ => p.orders z hz)

theorem HillRealHighGapPair.exists_source_normalized_cut_root
    (q : WeightedCoeff SpectralWeight.one.toWeight 2)
    (hq : SpectralWeight.one.toCoeff q ∈ Coeff.paritySubspace 0)
    (n : ℕ) (hn : 1 ≤ n) (hcut : 16*‖q‖ ≤ (n : ℝ))
    (p : HillRealHighGapPair (SpectralWeight.one.toCoeff q) n) :
    ∃ R : ℂ → ℂ,
      AnalyticOnNhd ℂ R (ball (freeHillValue n : ℂ) (n : ℝ) \ segment ℝ (p.left : ℂ) p.right) ∧
      (∀ z ∈ ball (freeHillValue n : ℂ) (n : ℝ) \ segment ℝ (p.left : ℂ) p.right,
        R z ≠ 0 ∧ R z^2 = hillL2Radicand (SpectralWeight.one.toCoeff q) z) ∧
      (p.left = p.right → AnalyticOnNhd ℂ R (ball (freeHillValue n : ℂ) (n : ℝ))) ∧
      ∀ z ∈ sphere (freeHillValue n : ℂ) (3*(n : ℝ)/4),
        R z = hillL2ContinuedRoot (z,SpectralWeight.one.toCoeff q) := by
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  obtain ⟨hQ,hfactor,hunit⟩ := p.deflated_unit q n hn
  obtain ⟨B,hB,hsq,hcollapsed⟩ := exists_analytic_squareRoot_on_two_zero_cut
    (hillL2Radicand (SpectralWeight.one.toCoeff q))
    (twoZeroQuotient (hillL2Radicand (SpectralWeight.one.toCoeff q)) p.left p.right)
    p.left p.right (freeHillValue n : ℂ) (n : ℝ) hnpos
    (hQ.mono ball_subset_closedBall) (fun z hz => hunit z (ball_subset_closedBall hz))
    (fun z _ => hfactor z)
  have hloc := p.localization q hq n hn (by linarith [norm_nonneg q])
  have hL : (p.left : ℂ) ∈ closedBall (freeHillValue n : ℂ) (4*‖q‖) := by
    simpa only [mem_closedBall,dist_eq_norm,← ofReal_sub,norm_real,Real.norm_eq_abs] using hloc.1
  have hU : (p.right : ℂ) ∈ closedBall (freeHillValue n : ℂ) (4*‖q‖) := by
    simpa only [mem_closedBall,dist_eq_norm,← ofReal_sub,norm_real,Real.norm_eq_abs] using hloc.2
  have hseg : segment ℝ (p.left : ℂ) p.right ⊆ closedBall (freeHillValue n : ℂ) (4*‖q‖) :=
    (convex_closedBall _ _).segment_subset hL hU
  have hcircle (z : ℂ) (hz : z ∈ sphere (freeHillValue n : ℂ) (3*(n : ℝ)/4)) :
      z ∈ ball (freeHillValue n : ℂ) (n : ℝ) \ segment ℝ (p.left : ℂ) p.right := by
    have he : ‖z-(freeHillValue n : ℂ)‖ = 3*(n : ℝ)/4 := by
      simpa only [mem_sphere,dist_eq_norm] using hz
    refine ⟨?_,?_⟩
    · rw [mem_ball,dist_eq_norm,he]
      linarith
    · intro hs
      have hh : ‖z-(freeHillValue n : ℂ)‖ ≤ 4*‖q‖ := by
        simpa only [mem_closedBall,dist_eq_norm] using hseg hs
      linarith
  have hsource (z : ℂ) (hz : z ∈ sphere (freeHillValue n : ℂ) (3*(n : ℝ)/4)) :
      (z,SpectralWeight.one.toCoeff q) ∈ hillL2ContinuationDomain := by
    apply mem_hillL2ContinuationDomain_of_high_distance q hq n hn hcut z
      (ball_subset_closedBall (hcircle z hz).1)
    have he : ‖z-(freeHillValue n : ℂ)‖ = 3*(n : ℝ)/4 := by
      simpa only [mem_sphere,dist_eq_norm] using hz
    rw [he]
    linarith
  have hsourceA : AnalyticOnNhd ℂ (fun z => hillL2ContinuedRoot (z,SpectralWeight.one.toCoeff q))
      (sphere (freeHillValue n : ℂ) (3*(n : ℝ)/4)) := by
    intro z hz
    exact (analyticOnNhd_hillL2ContinuedRoot _ (hsource z hz)).comp
      (f := fun z : ℂ => (z,SpectralWeight.one.toCoeff q)) (analyticAt_id.prod analyticAt_const)
  obtain ⟨k,hk,hmatch⟩ := exists_fixed_sign_of_sq_eq_on_preconnected
    (fun z => hillL2ContinuedRoot (z,SpectralWeight.one.toCoeff q)) B
    (sphere (freeHillValue n : ℂ) (3*(n : ℝ)/4))
    (isPreconnected_sphere (by simp) _ _) hsourceA.continuousOn
    (hB.mono (fun z hz => hcircle z hz)).continuousOn
    (fun z hz => (hillL2ContinuedRoot_sq _ (hsource z hz)).trans (hsq z (hcircle z hz)).2.symm)
    (fun z hz => (hsq z (hcircle z hz)).1)
  have hk2 : k^2 = 1 := by rcases hk with rfl | rfl <;> norm_num
  have hkne : k ≠ 0 := by rcases hk with rfl | rfl <;> norm_num
  refine ⟨fun z => k*B z,analyticOnNhd_const.mul hB,?_,?_,?_⟩
  · intro z hz
    refine ⟨mul_ne_zero hkne (hsq z hz).1,?_⟩
    rw [mul_pow,hk2,one_mul,(hsq z hz).2]
  · intro he
    exact analyticOnNhd_const.mul (hcollapsed (congrArg Complex.ofReal he))
  · intro z hz
    exact (hmatch z hz).symm

end NLS.KdV
