import NLS.MKdV.MiuraDirichletActionMotion

/-! # Original independent divisor motion under the physical mKdV actions

These certify the actual trace cotangent, its contour-energy Gardner
factor, and the motion of the original globally labeled Dirichlet energy
under every complete physical action flow. The negative rotation of the
full independent Abelian phase remains to be proved.
-/
noncomputable section
open Set Metric Complex Filter Topology MeasureTheory
open NLS.LinearVolterra NLS.Fourier NLS.Poisson NLS.KdV NLS.MKdV NLS.ZakharovShabat NLS.ComplexAnalysis
open scoped ENNReal ComplexConjugate
namespace NLS.Articles.MKdVNLSHierarchies

theorem independent_Dirichlet_discriminant_physical_Gardner
    (a : ScalarDomain 2) (ha : ∀ j, a.val j = conj (a.val (-j))) (n : ℕ) (hn : 1 ≤ n)
    (B : MiuraDirichletBranch a ha n hn) (E : ℂ) :
    B.energyGradient.bracket (miuraHillDiscriminantGradient a E) =
      4*E*(∫ x in (0 : ℝ)..1,
        extend (hillDirichletGradientCurve (realSobolevMiuraHillPotential a ha) n hn) x*
        extend (hillEnergyTraceGradientSpatialCurve (sobolevMiuraHillPotential a) E) x) :=
  miuraHillDiscriminantGradient_bracket_eq_energy_first a ha n hn B E

theorem independent_Dirichlet_original_action_contour
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
            sourceCanonicalRoot (by simp) (by norm_num) (sobolevSourceInclusion (a,a)) z) :=
  miuraDirichlet_physicalAction_generator_circle a ha m hm B n hn

theorem independent_Dirichlet_energy_complete_action_motion
    (s : ℕ) (hs : 1 ≤ s) (a : MiuraRealSobolevSource s) (n : ℕ) (hn : 1 ≤ n)
    (m : ℕ) (hm : 1 ≤ m) (t : ℝ) :
    let b := hierarchySobolevToScalarDomain s hs (miuraNativeRealActionFlow s a n t).val
    let hb := miuraNativeH1Profile_real s hs (miuraNativeRealActionFlow s a n t)
    let φ : realDiagonalSourceLocus 2 :=
      ⟨(realDiagonalH1Source b hb).val,⟨(realDiagonalH1Source b hb).property,rfl⟩⟩
    let C := (sourceDiagonalLaurentAtlas (by simp) (by norm_num)).localChart φ
    HasDerivAt (fun r => miuraNativeDirichletEnergy s hs m hm (miuraNativeRealActionFlow s a n r))
      (-(2/(Real.pi : ℂ))*(∮ z in C(C.cauchy.discs.center n,C.contourRadius n),
        z*(∫ x in (0 : ℝ)..1,
          extend (hillDirichletGradientCurve (realSobolevMiuraHillPotential b hb) m hm) x*
          extend (hillEnergyTraceGradientSpatialCurve (sobolevMiuraHillPotential b) (z^2)) x)/
            sourceCanonicalRoot (by simp) (by norm_num) (sobolevSourceInclusion (b,b)) z)) t :=
  hasDerivAt_miuraNativeDirichletEnergy_actionFlow_circle s hs a n hn m hm t

end NLS.Articles.MKdVNLSHierarchies
