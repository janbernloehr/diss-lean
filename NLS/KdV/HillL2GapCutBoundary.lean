import NLS.KdV.HillL2GapCutPrimitives
import NLS.ComplexAnalysis.TwoZeroRootEndpointBound
import NLS.ComplexAnalysis.SegmentPrimitiveBoundary

/-! # Finite endpoint limits of the actual high Hill cut primitive

The exact deflated unit is nonzero at each endpoint. The shared two-zero
root bound therefore supplies inverse-square-root growth for the actual
logarithmic derivative. The slit theorem yields one finite limit at each
endpoint for all approaches in the full cut complement, including both
sides. Their values and the real-gap jump are not assumed here.
-/

noncomputable section
open Set Metric Complex Filter Topology
open NLS.ComplexAnalysis
namespace NLS.KdV

theorem HillRealHighGapPair.primitive_endpoint_limits
    (q : WeightedCoeff SpectralWeight.one.toWeight 2)
    (hq : SpectralWeight.one.toCoeff q ∈ Coeff.paritySubspace 0)
    (n : ℕ) (hn : 1 ≤ n) (hcut : 16*‖q‖ ≤ (n : ℝ))
    (p : HillRealHighGapPair (SpectralWeight.one.toCoeff q) n) (hopen : p.left ≠ p.right)
    (R P : ℂ → ℂ)
    (hR : AnalyticOnNhd ℂ R (ball (freeHillValue n : ℂ) (n : ℝ) \ segment ℝ (p.left : ℂ) p.right))
    (hsq : ∀ z ∈ ball (freeHillValue n : ℂ) (n : ℝ) \ segment ℝ (p.left : ℂ) p.right,
      R z ≠ 0 ∧ R z^2 = hillL2Radicand (SpectralWeight.one.toCoeff q) z)
    (hP : ∀ z ∈ ball (freeHillValue n : ℂ) (7*(n : ℝ)/8) \ segment ℝ (p.left : ℂ) p.right,
      HasDerivAt P (deriv (hillL2Discriminant (SpectralWeight.one.toCoeff q)) z/R z) z) :
    ∃ A B : ℂ,
      Tendsto P (𝓝[ball (freeHillValue n : ℂ) (7*(n : ℝ)/8) \ segment ℝ (p.left : ℂ) p.right] p.left) (𝓝 A) ∧
      Tendsto P (𝓝[ball (freeHillValue n : ℂ) (7*(n : ℝ)/8) \ segment ℝ (p.left : ℂ) p.right] p.right) (𝓝 B) := by
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  let Q := twoZeroQuotient (hillL2Radicand (SpectralWeight.one.toCoeff q)) p.left p.right
  let N := deriv (hillL2Discriminant (SpectralWeight.one.toCoeff q))
  let Ω := ball (freeHillValue n : ℂ) (7*(n : ℝ)/8)
  let D := ball (freeHillValue n : ℂ) (n : ℝ) \ segment ℝ (p.left : ℂ) p.right
  have hsub : Ω \ segment ℝ (p.left : ℂ) p.right ⊆ D := by
    intro z hz
    exact ⟨ball_subset_ball (by linarith) hz.1,hz.2⟩
  obtain ⟨hQ,hfactor,hunit⟩ := p.deflated_unit q n hn
  have hN : AnalyticOnNhd ℂ N univ := (analyticOnNhd_hillL2Discriminant _).deriv
  have hroot (z : ℂ) (hz : z ∈ D) : R z ≠ 0 ∧ R z^2 = (z-p.left)*(z-p.right)*Q z :=
    ⟨(hsq z hz).1,(hsq z hz).2.trans (hfactor z)⟩
  have hab : (p.left : ℂ) ≠ (p.right : ℂ) := fun he => hopen (ofReal_inj.mp he)
  obtain ⟨δl,Ml,εl,hδl,hMl,hεl,hbl⟩ := exists_two_zero_root_endpoint_bound N Q R D p.left p.right hab
    (hN p.left (mem_univ _)).continuousAt (hQ p.left p.left_mem).continuousAt
    (hunit p.left p.left_mem) hroot
  obtain ⟨δr,Mr,εr,hδr,hMr,hεr,hbr⟩ := exists_two_zero_root_endpoint_bound N Q R D p.right p.left hab.symm
    (hN p.right (mem_univ _)).continuousAt (hQ p.right p.right_mem).continuousAt
    (hunit p.right p.right_mem) (fun z hz => ⟨(hsq z hz).1,by
      rw [(hsq z hz).2,hfactor z]
      dsimp only [Q]
      ring⟩)
  have hg : AnalyticOnNhd ℂ (fun z => N z/R z) (Ω \ segment ℝ (p.left : ℂ) p.right) := by
    intro z hz
    exact (hN z (mem_univ _)).div (hR z (hsub hz)) (hsq z (hsub hz)).1
  have hloc := p.localization q hq n hn (by linarith [norm_nonneg q])
  have hl : (p.left : ℂ) ∈ Ω := by
    rw [mem_ball,dist_eq_norm,← ofReal_sub,norm_real,Real.norm_eq_abs]
    linarith [hloc.1]
  have hr : (p.right : ℂ) ∈ Ω := by
    rw [mem_ball,dist_eq_norm,← ofReal_sub,norm_real,Real.norm_eq_abs]
    linarith [hloc.2]
  obtain ⟨A,hA⟩ := exists_primitive_segment_left_boundary_limit (fun z => N z/R z) P Ω p.left p.right
    δl Ml εl isOpen_ball hl hab hδl hMl hεl hg.continuousOn hP
    (fun z hz hdist => hbl z (hsub hz) hdist)
  obtain ⟨B,hB⟩ := exists_primitive_segment_right_boundary_limit (fun z => N z/R z) P Ω p.left p.right
    δr Mr εr isOpen_ball hr hab hδr hMr hεr hg.continuousOn hP
    (fun z hz hdist => hbr z (hsub hz) hdist)
  exact ⟨A,B,hA,hB⟩

end NLS.KdV
