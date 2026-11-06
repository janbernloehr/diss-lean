import NLS.KdV.HillL2SourceNormalizedCutRoots
import NLS.ComplexAnalysis.PrimitiveOnDiscComplement
import NLS.ComplexAnalysis.CirclePolynomialIntegrationByParts

/-! # Actual Hill primitives on the complete local gap complement

The source-matched root has zero logarithmic period on an enclosing
circle. The shared annular/radial continuation constructs a primitive
on the full smaller disc minus the actual gap, including both sides of
the real bands. Every checked source moment equals its polynomial
moment. Endpoint limits and the jump formula are separate obligations.
-/

noncomputable section
open Set Metric Complex
open NLS.ComplexAnalysis
namespace NLS.KdV

theorem HillRealHighGapPair.exists_source_cut_primitive
    (q : WeightedCoeff SpectralWeight.one.toWeight 2)
    (hq : SpectralWeight.one.toCoeff q ∈ Coeff.paritySubspace 0)
    (n : ℕ) (hn : 1 ≤ n) (hcut : 8*‖q‖ ≤ (n : ℝ))
    (p : HillRealHighGapPair (SpectralWeight.one.toCoeff q) n) :
    ∃ R P : ℂ → ℂ,
      AnalyticOnNhd ℂ R (ball (freeHillValue n : ℂ) (n : ℝ) \ segment ℝ (p.left : ℂ) p.right) ∧
      (∀ z ∈ ball (freeHillValue n : ℂ) (n : ℝ) \ segment ℝ (p.left : ℂ) p.right,
        R z ≠ 0 ∧ R z^2 = hillL2Radicand (SpectralWeight.one.toCoeff q) z) ∧
      (p.left = p.right → AnalyticOnNhd ℂ R (ball (freeHillValue n : ℂ) (n : ℝ))) ∧
      (∀ z ∈ sphere (freeHillValue n : ℂ) (3*(n : ℝ)/4),
        R z = hillL2ContinuedRoot (z,SpectralWeight.one.toCoeff q)) ∧
      AnalyticOnNhd ℂ P (ball (freeHillValue n : ℂ) (7*(n : ℝ)/8) \ segment ℝ (p.left : ℂ) p.right) ∧
      (∀ z ∈ ball (freeHillValue n : ℂ) (7*(n : ℝ)/8) \ segment ℝ (p.left : ℂ) p.right,
        HasDerivAt P (deriv (hillL2Discriminant (SpectralWeight.one.toCoeff q)) z / R z) z) ∧
      ∀ m : ℕ, hillL2HighContourMoment n m (SpectralWeight.one.toCoeff q) =
        -(Real.pi : ℂ)⁻¹ * ∮ z in C((freeHillValue n : ℂ),3*(n : ℝ)/4), z^m*P z := by
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  obtain ⟨R,hR,hsq,hcollapsed,hmatch⟩ := p.exists_source_normalized_cut_root q hq n hn hcut
  let K := segment ℝ (p.left : ℂ) p.right
  let A := ball (freeHillValue n : ℂ) (7*(n : ℝ)/8) \ K
  let g : ℂ → ℂ := fun z => deriv (hillL2Discriminant (SpectralWeight.one.toCoeff q)) z/R z
  have hKclosed : IsClosed K := by
    apply IsCompact.isClosed
    dsimp only [K]
    rw [segment_eq_image_lineMap]
    exact isCompact_Icc.image AffineMap.lineMap_continuous
  have hloc := p.localization q hq n hn hcut
  have hL : (p.left : ℂ) ∈ ball (freeHillValue n : ℂ) (3*(n : ℝ)/4) := by
    rw [mem_ball,dist_eq_norm,← ofReal_sub,norm_real,Real.norm_eq_abs]
    linarith [hloc.1]
  have hU : (p.right : ℂ) ∈ ball (freeHillValue n : ℂ) (3*(n : ℝ)/4) := by
    rw [mem_ball,dist_eq_norm,← ofReal_sub,norm_real,Real.norm_eq_abs]
    linarith [hloc.2]
  have hKinner : K ⊆ ball (freeHillValue n : ℂ) (3*(n : ℝ)/4) :=
    (convex_ball _ _).segment_subset hL hU
  have hg : AnalyticOnNhd ℂ g (closedBall (freeHillValue n : ℂ) (7*(n : ℝ)/8) \ K) := by
    intro z hz
    have hzN : z ∈ ball (freeHillValue n : ℂ) (n : ℝ) \ K :=
      ⟨closedBall_subset_ball (by linarith) hz.1,hz.2⟩
    exact ((analyticOnNhd_hillL2Discriminant _).deriv z (mem_univ _)).div (hR z hzN) (hsq z hzN).1
  have hperiod : (∮ z in C((freeHillValue n : ℂ),3*(n : ℝ)/4), g z) = 0 := by
    calc
      _ = ∮ z in C((freeHillValue n : ℂ),3*(n : ℝ)/4),
          deriv (hillL2Discriminant (SpectralWeight.one.toCoeff q)) z /
            hillL2ContinuedRoot (z,SpectralWeight.one.toCoeff q) := by
        apply circleIntegral.integral_congr (by positivity)
        intro z hz
        dsimp only [g]
        rw [hmatch z hz]
      _ = 0 := hillL2Continued_period_eq_zero_radius q hq n hn hcut
        (3*(n : ℝ)/4) (by linarith) (by linarith)
  obtain ⟨P,hP⟩ := exists_primitive_on_disc_complement_of_zero_period g
    (freeHillValue n : ℂ) p.left (3*(n : ℝ)/4) (7*(n : ℝ)/8)
    (by positivity) (by linarith) K hKclosed (left_mem_segment ℝ _ _)
    ((convex_segment (𝕜 := ℝ) _ _).starConvex (left_mem_segment ℝ _ _)) hKinner hg hperiod
  have hA : IsOpen A := isOpen_ball.sdiff hKclosed
  have hPA : AnalyticOnNhd ℂ P A :=
    (show DifferentiableOn ℂ P A from fun z hz => (hP z hz).differentiableAt.differentiableWithinAt).analyticOnNhd hA
  have hcircle (z : ℂ) (hz : z ∈ sphere (freeHillValue n : ℂ) (3*(n : ℝ)/4)) : z ∈ A := by
    refine ⟨?_,?_⟩
    · have he := mem_sphere.mp hz
      rw [mem_ball]
      linarith
    · exact fun hs => sphere_disjoint_ball.le_bot ⟨hz,hKinner hs⟩
  refine ⟨R,P,hR,hsq,hcollapsed,hmatch,hPA,hP,?_⟩
  intro m
  have hi : (∮ z in C((freeHillValue n : ℂ),3*(n : ℝ)/4),
      z^(m+1)*deriv (hillL2Discriminant (SpectralWeight.one.toCoeff q)) z /
        hillL2ContinuedRoot (z,SpectralWeight.one.toCoeff q)) =
      ∮ z in C((freeHillValue n : ℂ),3*(n : ℝ)/4), z^(m+1)*deriv P z := by
    apply circleIntegral.integral_congr (by positivity)
    intro z hz
    dsimp only
    rw [(hP z (hcircle z hz)).deriv]
    dsimp only [g]
    rw [hmatch z hz]
    exact mul_div_assoc _ _ _
  have hip := circleIntegral_pow_mul_deriv_eq_neg P A hPA (freeHillValue n : ℂ)
    (3*(n : ℝ)/4) (by positivity) hcircle m
  rw [hillL2HighContourMoment_arnold_radius q hq n hn hcut (3*(n : ℝ)/4)
    (by linarith) (by linarith) m,hi,hip]
  have hm : (m+1 : ℂ) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero m
  have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  field_simp

end NLS.KdV
