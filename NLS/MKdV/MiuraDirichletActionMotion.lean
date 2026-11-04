import NLS.MKdV.MiuraDirichletActionContour
import NLS.MKdV.MiuraNativeActionFlowAllTimes
import NLS.MKdV.MiuraNativeAbelianPhase

/-! # Actual independent Dirichlet energies along complete physical action flows

Local analytic branch agreement transfers the native chain rule to the
original globally labeled Dirichlet energy at every time. Closed gaps,
infinite support and arbitrary signed mean are included.
-/
noncomputable section
open Set Complex Filter Topology MeasureTheory
open NLS.LinearVolterra NLS.Fourier NLS.Poisson NLS.KdV NLS.ZakharovShabat
open scoped ENNReal ComplexConjugate
namespace NLS.MKdV

def miuraNativeDirichletEnergy (s : ℕ) (hs : 1 ≤ s) (m : ℕ) (hm : 1 ≤ m)
    (a : MiuraRealSobolevSource s) : ℂ :=
  let q := realSobolevMiuraHillPotential (hierarchySobolevToScalarDomain s hs a.val) (miuraNativeH1Profile_real s hs a)
  (hillDirichletEnergy q.val q.property.1 q.property.2 m hm : ℂ)

theorem hasDerivAt_miuraNativeDirichletEnergy_actionFlow
    (s : ℕ) (hs : 1 ≤ s) (a : MiuraRealSobolevSource s) (n : ℕ) (hn : 1 ≤ n)
    (m : ℕ) (hm : 1 ≤ m) (t : ℝ)
    (B : MiuraDirichletBranch
      (hierarchySobolevToScalarDomain s hs (miuraNativeRealActionFlow s a n t).val)
      (miuraNativeH1Profile_real s hs (miuraNativeRealActionFlow s a n t)) m hm) :
    HasDerivAt (fun r => miuraNativeDirichletEnergy s hs m hm (miuraNativeRealActionFlow s a n r))
      (reflectedHilbertPairing (scalarInclusion B.energyGradient.gradient)
        (l2GardnerDirection (miuraL2Action n)
          (scalarInclusion (hierarchySobolevToScalarDomain s hs (miuraNativeRealActionFlow s a n t).val)))) t := by
  let A : ℝ → ScalarDomain 2 := fun r => hierarchySobolevToScalarDomain s hs (miuraNativeRealActionFlow s a n r).val
  have hA : Continuous A :=
    (hierarchySobolevToScalarDomain s hs).continuous.comp (continuous_miuraActionFlow s a.val a.property n)
  have hreal (r : ℝ) : ∀ j, (A r).val j = conj ((A r).val (-j)) :=
    miuraNativeH1Profile_real s hs (miuraNativeRealActionFlow s a n r)
  have hmatch := B.eventually_real_family_match A hA hreal t rfl
  have hd := hasDerivAt_independent_functional_miuraActionFlow_allTimes s hs a n hn t
    (fun b => B.energyBranch (sobolevMiuraHillPotential b)) B.energyGradient
  have he : (fun r => miuraNativeDirichletEnergy s hs m hm (miuraNativeRealActionFlow s a n r)) =ᶠ[𝓝 t]
      (fun r => B.energyBranch (sobolevMiuraHillPotential (A r))) := by
    filter_upwards [hmatch] with r hr
    exact hr.1.symm
  have hjet := scalarInclusion_hierarchySobolevToScalarDomain s hs (miuraNativeRealActionFlow s a n t).val
  rw [← hjet] at hd
  exact hd.congr_of_eventuallyEq he

/-- The derivative of the original labeled energy, with no chosen branch
in its statement, is the actual physical-action spectral contour. -/
theorem hasDerivAt_miuraNativeDirichletEnergy_actionFlow_circle
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
          extend (hillDiscriminantGradientSpatialCurve (sobolevMiuraHillPotential b) (z^2)) x)/
            sourceCanonicalRoot (by simp) (by norm_num) (sobolevSourceInclusion (b,b)) z)) t := by
  let b := hierarchySobolevToScalarDomain s hs (miuraNativeRealActionFlow s a n t).val
  let hb := miuraNativeH1Profile_real s hs (miuraNativeRealActionFlow s a n t)
  obtain ⟨B⟩ := nonempty_miuraDirichletBranch b hb m hm
  have hd := hasDerivAt_miuraNativeDirichletEnergy_actionFlow s hs a n hn m hm t B
  rw [miuraDirichlet_physicalAction_generator_circle b hb m hm B n hn] at hd
  exact hd

end NLS.MKdV
