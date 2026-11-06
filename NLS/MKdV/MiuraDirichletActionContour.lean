import NLS.MKdV.MiuraDirichletDiscriminantDirection
import NLS.ZakharovShabat.SourceOrdinaryLaurentCotangentCircle

/-! # The original physical-action generator of an independent Dirichlet energy

The action field is the actual Gardner direction of the original contour
action. Its pairing with the independent Dirichlet gradient is an explicit
spectral circle integral. No prescribed divisor velocity is used.
-/
noncomputable section
open Set Metric Complex Filter Topology MeasureTheory
open NLS.LinearVolterra NLS.Fourier NLS.Poisson NLS.KdV NLS.ZakharovShabat NLS.ComplexAnalysis
open scoped ENNReal ComplexConjugate
namespace NLS.MKdV

theorem miuraDirichlet_physicalAction_generator_circle
    (a : ScalarDomain 2) (ha : ∀ j, a.val j = conj (a.val (-j))) (m : ℕ) (hm : 1 ≤ m)
    (B : MiuraDirichletBranch a ha m hm) (n : ℕ) (hn : 1 ≤ n) :
    let φ : realDiagonalSourceLocus 2 :=
      ⟨(realDiagonalH1Source a ha).val,⟨(realDiagonalH1Source a ha).property,rfl⟩⟩
    let C := (sourceDiagonalLaurentAtlas (by simp) (by norm_num)).localChart φ
    reflectedHilbertPairing (scalarInclusion B.energyGradient.gradient)
      (l2GardnerDirection (miuraL2Action n) (scalarInclusion a)) =
      -(2/(Real.pi : ℂ))*(∮ z in C(C.cauchy.discs.center n,C.contourRadius n),
        z*(∫ x in (0 : ℝ)..1,
          extend (hillDirichletGradientCurve (realSobolevMiuraHillPotential a ha) m hm) x*
          extend (hillEnergyTraceGradientSpatialCurve (sobolevMiuraHillPotential a) (z^2)) x)/
            sourceCanonicalRoot (by simp) (by norm_num) (sobolevSourceInclusion (a,a)) z) := by
  let φ : realDiagonalSourceLocus 2 :=
    ⟨(realDiagonalH1Source a ha).val,⟨(realDiagonalH1Source a ha).property,rfl⟩⟩
  let C := (sourceDiagonalLaurentAtlas (by simp) (by norm_num)).localChart φ
  let T := (reflectedHilbertPairing (scalarInclusion B.energyGradient.gradient)).comp miuraSourceDifferenceCLM
  have hφ : φ.val ∈ ball φ.val C.radius := mem_ball_self C.radius_pos
  have hn0 : (n : ℤ) ≠ 0 := by omega
  have hcircle : sphere (C.cauchy.discs.center n) (C.contourRadius n) ⊆
      sourceCanonicalRootDomain (by simp) (by norm_num) φ.val := by
    intro z hz
    exact C.cauchy.intermediate_circle_root n φ.val (C.source_subset hφ) _
      (C.contourRadius_bounds n).1 (C.contourRadius_bounds n).2 z hz
  have hint := circleIntegrable_sourceActionVariationCotangent (by simp) (by norm_num) φ.val _ _
    (C.contourRadius_pos n).le hcircle
  have hmap := map_circleIntegral T hint
  have hc := fderiv_sourceComplexAction_eq_Laurent_cotangent_circle (by simp) (by norm_num) φ n hn0
  change reflectedHilbertPairing (scalarInclusion B.energyGradient.gradient)
    (l2GardnerDirection (miuraL2Action n) (scalarInclusion a)) = _
  rw [miuraActionGardnerDirection_eq_sourceDifference a ha n hn]
  change T (fderiv ℂ (sourceComplexAction (by simp) (by norm_num) n) φ.val) = _
  rw [hc,map_smul,smul_eq_mul,hmap]
  have he : (∮ z in C(C.cauchy.discs.center n,C.contourRadius n),
      T (sourceActionVariationCotangent (by simp) (by norm_num) φ.val z)) =
      2*(∮ z in C(C.cauchy.discs.center n,C.contourRadius n),
        z*(∫ x in (0 : ℝ)..1,
          extend (hillDirichletGradientCurve (realSobolevMiuraHillPotential a ha) m hm) x*
          extend (hillEnergyTraceGradientSpatialCurve (sobolevMiuraHillPotential a) (z^2)) x)/
            sourceCanonicalRoot (by simp) (by norm_num) (sobolevSourceInclusion (a,a)) z) := by
    rw [← circleIntegral.integral_const_mul]
    apply circleIntegral.integral_congr (C.contourRadius_pos n).le
    intro z hz
    have hz0 : z ≠ 0 := by
      intro heq
      exact C.zero_not_mem_contour_disc n hn0 (heq ▸ sphere_subset_closedBall hz)
    change T ((sourceCanonicalRoot (by simp) (by norm_num) φ.val z)⁻¹ •
      sourceDiscriminantCotangent (by simp) z φ.val) = _
    rw [map_smul,smul_eq_mul]
    change _*reflectedHilbertPairing (scalarInclusion B.energyGradient.gradient)
      (miuraSourceDifferenceCLM (sourceDiscriminantCotangent (by simp) z (sobolevSourceInclusion (a,a)))) = _
    rw [miuraDirichletGradient_discriminant_difference a ha m hm B z hz0]
    change _ = 2*(z*_ / sourceCanonicalRoot (by simp) (by norm_num) φ.val z)
    ring
  rw [he]
  ring

end NLS.MKdV
