import NLS.KdV.HillL2GapCutPrimitives
import NLS.ComplexAnalysis.TraceRootPrimitive
import NLS.ComplexAnalysis.ComplexSegmentComplementConnected

/-! # Source-normalized Hill primitives on the full local cut

One value on the enclosing source circle fixes the additive constant.
The resulting primitive has the exact exponential and hyperbolic trace
identities on the entire cut domain, and agrees with the source
primitive on the whole circle. No endpoint value is assumed.
-/

noncomputable section
open Set Metric Complex
open NLS.ComplexAnalysis
namespace NLS.KdV

/-- The actual high-energy root and its source-normalized primitive.
Both sides of the gap and both real adjacent bands are in the cut domain. -/
structure HillL2NormalizedCutPrimitive (q : Coeff 2) (n : ℕ)
    (p : HillRealHighGapPair q n) (R F : ℂ → ℂ) : Prop where
  root_analytic : AnalyticOnNhd ℂ R
    (ball (freeHillValue n : ℂ) (n : ℝ) \ segment ℝ (p.left : ℂ) p.right)
  root_data : ∀ z ∈ ball (freeHillValue n : ℂ) (n : ℝ) \ segment ℝ (p.left : ℂ) p.right,
    R z ≠ 0 ∧ R z^2 = hillL2Radicand q z
  collapsed_analytic : p.left = p.right →
    AnalyticOnNhd ℂ R (ball (freeHillValue n : ℂ) (n : ℝ))
  root_source : ∀ z ∈ sphere (freeHillValue n : ℂ) (3*(n : ℝ)/4),
    R z = hillL2ContinuedRoot (z,q)
  analytic : AnalyticOnNhd ℂ F
    (ball (freeHillValue n : ℂ) (7*(n : ℝ)/8) \ segment ℝ (p.left : ℂ) p.right)
  hasDerivAt : ∀ z ∈ ball (freeHillValue n : ℂ) (7*(n : ℝ)/8) \ segment ℝ (p.left : ℂ) p.right,
    HasDerivAt F (deriv (hillL2Discriminant q) z / R z) z
  exp_eq : ∀ z ∈ ball (freeHillValue n : ℂ) (7*(n : ℝ)/8) \ segment ℝ (p.left : ℂ) p.right,
    exp (F z) = (hillL2Discriminant q z + R z)/2
  trace_eq : ∀ z ∈ ball (freeHillValue n : ℂ) (7*(n : ℝ)/8) \ segment ℝ (p.left : ℂ) p.right,
    2*cosh (F z) = hillL2Discriminant q z ∧ 2*sinh (F z) = R z
  source : ∀ z ∈ sphere (freeHillValue n : ℂ) (3*(n : ℝ)/4),
    F z = hillL2ContinuedPrimitive (z,q)
  moment_eq : ∀ m : ℕ, hillL2HighContourMoment n m q =
    -(Real.pi : ℂ)⁻¹ * ∮ z in C((freeHillValue n : ℂ),3*(n : ℝ)/4), z^m*F z

theorem HillRealHighGapPair.exists_normalized_source_cut_primitive
    (q : WeightedCoeff SpectralWeight.one.toWeight 2)
    (hq : SpectralWeight.one.toCoeff q ∈ Coeff.paritySubspace 0)
    (n : ℕ) (hn : 1 ≤ n) (hcut : 8*‖q‖ ≤ (n : ℝ))
    (p : HillRealHighGapPair (SpectralWeight.one.toCoeff q) n) :
    ∃ R F : ℂ → ℂ, HillL2NormalizedCutPrimitive (SpectralWeight.one.toCoeff q) n p R F := by
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  obtain ⟨R,P,hR,hsq,hcollapsed,hmatch,hP,hderiv,_⟩ :=
    p.exists_source_cut_primitive q hq n hn hcut
  let K := segment ℝ (p.left : ℂ) p.right
  let A := ball (freeHillValue n : ℂ) (7*(n : ℝ)/8) \ K
  let a : ℂ := (freeHillValue n : ℂ) + (3*(n : ℝ)/4 : ℝ)
  have ha : a ∈ sphere (freeHillValue n : ℂ) (3*(n : ℝ)/4) := by
    simp only [a, mem_sphere, dist_eq_norm, add_sub_cancel_left,
      norm_real, Real.norm_eq_abs, abs_of_pos (by positivity : 0 < 3*(n : ℝ)/4)]
  have hloc := p.localization q hq n hn hcut
  have hL : (p.left : ℂ) ∈ ball (freeHillValue n : ℂ) (3*(n : ℝ)/4) := by
    rw [mem_ball,dist_eq_norm,← ofReal_sub,norm_real,Real.norm_eq_abs]
    linarith [hloc.1]
  have hU : (p.right : ℂ) ∈ ball (freeHillValue n : ℂ) (3*(n : ℝ)/4) := by
    rw [mem_ball,dist_eq_norm,← ofReal_sub,norm_real,Real.norm_eq_abs]
    linarith [hloc.2]
  have hK : K ⊆ ball (freeHillValue n : ℂ) (3*(n : ℝ)/4) :=
    (convex_ball _ _).segment_subset hL hU
  have hcircle (z : ℂ) (hz : z ∈ sphere (freeHillValue n : ℂ) (3*(n : ℝ)/4)) : z ∈ A := by
    refine ⟨?_,fun hs => sphere_disjoint_ball.le_bot ⟨hz,hK hs⟩⟩
    rw [mem_ball]
    linarith [mem_sphere.mp hz]
  have hsub : A ⊆ ball (freeHillValue n : ℂ) (n : ℝ) \ K := by
    intro z hz
    exact ⟨ball_subset_ball (by linarith) hz.1,hz.2⟩
  have hsource (z : ℂ) (hz : z ∈ sphere (freeHillValue n : ℂ) (3*(n : ℝ)/4)) :
      (z,SpectralWeight.one.toCoeff q) ∈ hillL2ContinuationDomain := by
    apply mem_hillL2ContinuationDomain_of_high_distance q hq n hn hcut z
      (ball_subset_closedBall (hsub (hcircle z hz)).1)
    have he : ‖z-(freeHillValue n : ℂ)‖ = 3*(n : ℝ)/4 := by
      simpa only [mem_sphere,dist_eq_norm] using hz
    rw [he]
    linarith
  have hKclosed : IsClosed K := by
    apply IsCompact.isClosed
    dsimp only [K]
    rw [segment_eq_image_lineMap]
    exact isCompact_Icc.image AffineMap.lineMap_continuous
  have hA : IsOpen A := isOpen_ball.sdiff hKclosed
  have hconn : IsPreconnected A :=
    (isPathConnected_convex_complex_segment_complement_including_singleton
      (ball (freeHillValue n : ℂ) (7*(n : ℝ)/8)) p.left p.right isOpen_ball (convex_ball _ _)
      (ball_subset_ball (by linarith) hL)).isConnected.isPreconnected
  let F : ℂ → ℂ := fun z => P z - P a + hillL2ContinuedPrimitive (a,SpectralWeight.one.toCoeff q)
  have hFA : AnalyticOnNhd ℂ F A := (hP.sub analyticOnNhd_const).add analyticOnNhd_const
  have hd (z : ℂ) (hz : z ∈ A) :
      HasDerivAt F (deriv (hillL2Discriminant (SpectralWeight.one.toCoeff q)) z/R z) z :=
    ((hderiv z hz).sub_const _).add_const _
  have hFa : F a = hillL2ContinuedPrimitive (a,SpectralWeight.one.toCoeff q) := by simp [F]
  have hexp : ∀ z ∈ A, exp (F z) = (hillL2Discriminant (SpectralWeight.one.toCoeff q) z+R z)/2 := by
    apply exp_primitive_of_traceRoot _ R F A hA hconn
      ((analyticOnNhd_hillL2Discriminant _).mono (subset_univ _)) (hR.mono hsub)
      (fun z hz => (hsq z (hsub hz)).2) (fun z hz => (hsq z (hsub hz)).1) hd a (hcircle a ha)
    rw [hFa,exp_hillL2ContinuedPrimitive _ (hsource a ha),hmatch a ha]
    rfl
  have hsrcA : AnalyticOnNhd ℂ (fun z => hillL2ContinuedPrimitive (z,SpectralWeight.one.toCoeff q))
      (sphere (freeHillValue n : ℂ) (3*(n : ℝ)/4)) := by
    intro z hz
    exact (analyticOnNhd_hillL2ContinuedPrimitive _ (hsource z hz)).comp
      (f := fun z : ℂ => (z,SpectralWeight.one.toCoeff q)) (analyticAt_id.prod analyticAt_const)
  have hFsource : ∀ z ∈ sphere (freeHillValue n : ℂ) (3*(n : ℝ)/4),
      F z = hillL2ContinuedPrimitive (z,SpectralWeight.one.toCoeff q) := by
    apply continuousLogarithms_eqOn F _ _ (isPreconnected_sphere (by simp) _ _)
      (hFA.mono hcircle).continuousOn hsrcA.continuousOn _ a ha hFa
    intro z hz
    rw [hexp z (hcircle z hz),exp_hillL2ContinuedPrimitive _ (hsource z hz),hmatch z hz]
    rfl
  refine ⟨R,F,hR,hsq,hcollapsed,hmatch,hFA,hd,hexp,?_,hFsource,?_⟩
  · intro z hz
    exact traceRoot_identities_of_exp _ R F z (hsq z (hsub hz)).2 (hexp z hz)
  · intro m
    rw [hillL2HighContourMoment_eq_radius q hq n hn hcut (3*(n : ℝ)/4)
      (by linarith) (by linarith) m]
    congr 1
    apply circleIntegral.integral_congr (by positivity)
    intro z hz
    dsimp only
    rw [hFsource z hz]

end NLS.KdV
