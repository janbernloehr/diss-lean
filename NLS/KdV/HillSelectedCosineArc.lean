import NLS.KdV.HillPhysicalCosinePath

noncomputable section
set_option autoImplicit false
open Set Complex NLS.ComplexAnalysis
namespace NLS.KdV

/-- The ACTUAL selected Dirichlet angle and the entire interior of its
signed affine path share one connected real arc with no sine zeros. -/
theorem exists_hillDirichlet_selected_regular_arc
    (q : WeightedCoeff SpectralWeight.one.toWeight 2)
    (hq : SpectralWeight.one.toCoeff q∈Coeff.paritySubspace 0)
    (hr : IsRealHillPotential (SpectralWeight.one.toCoeff q))
    (k : ℕ) (hk : 1≤k) (hgap : hillRealGapHalfLength q hq hr k≠0)
    (hw : hillDirichletSheetRoot (SpectralWeight.one.toCoeff q)
      (hillDirichletEnergy q hq hr k hk)≠0) :
    let θ := hillDirichletSelectedRealAngle q hq hr k hk hgap
    ∃ S : Set ℂ, IsPreconnected S ∧ (θ:ℂ)∈S ∧
      (∀ z∈S, z.im=0) ∧ (∀ z∈S, Complex.sin z≠0) ∧
      ∀ t∈Ioo (0:ℝ) 1, AffineMap.lineMap (realCosineArcAnchor θ:ℂ) (θ:ℂ) t∈S := by
  dsimp only
  let θ := hillDirichletSelectedRealAngle q hq hr k hk hgap
  have hspec := hillDirichletSelectedRealAngle_spec q hq hr k hk hgap
  have hs : Complex.sin (θ:ℂ)≠0 := by
    rw [hspec.2.2]
    exact hillDirichletGapSine_ne_zero_of_regular_sheet q hq hr k hk hgap hw
  have hθ0 : θ≠0 := by intro h; apply hs; rw [h,ofReal_zero,Complex.sin_zero]
  have hθp : θ≠Real.pi := by intro h; apply hs; rw [h,Complex.sin_pi]
  have hθm : θ≠-Real.pi := by
    intro h
    apply hs
    rw [h,ofReal_neg,Complex.sin_neg,Complex.sin_pi,neg_zero]
  obtain ⟨S,hS,hθS,hreal,hSin,hpath⟩ := exists_regular_real_cosine_arc θ
    ⟨lt_of_le_of_ne hspec.1.1 (Ne.symm hθm),lt_of_le_of_ne hspec.1.2 hθp⟩ hθ0
  refine ⟨S,hS,hθS,hreal,hSin,?_⟩
  intro t ht
  have h := hpath t ht
  rw [Path.extend_apply _ (Ioo_subset_Icc_self ht)] at h
  exact h

end NLS.KdV
