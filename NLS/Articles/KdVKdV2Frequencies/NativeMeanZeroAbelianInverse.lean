import NLS.Articles.KdVKdV2Frequencies.NativeFourierAbelianMap
import NLS.KdV.HillMeanZeroAbelianDerivative
import NLS.ComplexAnalysis.AnalyticOpenInverse

/-! # An actual local analytic inverse of the mean-zero weighted Abelian map -/
noncomputable section
open Set Metric Complex
namespace NLS.Articles.KdVKdV2Frequencies
open NLS.KdV

theorem exists_hillPhysical_native_meanZero_abelian_inverse :
    ∃ η : ℝ, ∃ Z : Coeff 2 → WeightedCoeff (hillAbelianTargetWeight SpectralWeight.one) 2,
      ∃ V W : Set (DeletedCoeff 2 0), ∃ G : DeletedCoeff 2 0 → DeletedCoeff 2 0,
      0 < η ∧ AnalyticOnNhd ℂ Z (ball (0 : Coeff 2) η) ∧ Z 0 = 0 ∧
      (∀ p : RealHillWeightedPotential SpectralWeight.one,
        SpectralWeight.one.doubleIndex.toCoeff p.val ∈ ball (0 : Coeff 2) η →
        Z (SpectralWeight.one.doubleIndex.toCoeff p.val) = hillPhysicalAbelianMap SpectralWeight.one p) ∧
      IsOpen V ∧ IsOpen W ∧ 0 ∈ V ∧ 0 ∈ W ∧ V ⊆ ball (0 : DeletedCoeff 2 0) η ∧
      let F := WeightedCoeff.meanZeroWeightedMap (hillAbelianTargetWeight SpectralWeight.one) Z
      F '' V = W ∧ Set.BijOn F V W ∧ AnalyticOnNhd ℂ F V ∧ AnalyticOnNhd ℂ G W ∧
      (∀ a ∈ V, G (F a) = a ∧
        WeightedCoeff.meanZeroWeightedLiftCLM (hillAbelianTargetWeight SpectralWeight.one) (F a) = Z a.val) ∧
      (∀ b ∈ W, G b ∈ V ∧ Z (G b).val =
        WeightedCoeff.meanZeroWeightedLiftCLM (hillAbelianTargetWeight SpectralWeight.one) b) ∧
      ∀ p : RealHillWeightedPotential SpectralWeight.one,
        ∀ hmean : (SpectralWeight.one.doubleIndex.toCoeff p.val) 0 = 0,
        let a : DeletedCoeff 2 0 := ⟨SpectralWeight.one.doubleIndex.toCoeff p.val,hmean⟩
        a ∈ V → Z a.val = hillPhysicalAbelianMap SpectralWeight.one p ∧
          G (WeightedCoeff.meanZeroWeightedProjectionCLM (hillAbelianTargetWeight SpectralWeight.one)
            (hillPhysicalAbelianMap SpectralWeight.one p)) = a := by
  obtain ⟨η,Z,_,hη,_,hZa,hZ0,hZb,hphysical,hFourier⟩ := exists_hillPhysical_native_fourier_abelian_map
  let w := hillAbelianTargetWeight SpectralWeight.one
  let F := WeightedCoeff.meanZeroWeightedMap w Z
  have hFa : AnalyticOnNhd ℂ F (ball (0 : DeletedCoeff 2 0) η) :=
    WeightedCoeff.analyticOnNhd_meanZeroWeightedMap w Z η hZa
  have hF0 : F 0 = 0 := by
    change WeightedCoeff.meanZeroWeightedProjectionCLM w (Z 0) = 0
    rw [hZ0,map_zero]
  have hunit := isUnit_fderiv_meanZeroAbelianMap Z (hZa 0 (mem_ball_self hη)).differentiableAt hFourier
  obtain ⟨V,W,hV,hW,h0V,h0W,hsub,himage,hbij,G,hFaV,hGa,hleft,hright⟩ :=
    NLS.ComplexAnalysis.exists_analytic_inverse_open_sets isOpen_ball hFa (mem_ball_self hη) hunit
  have hsource (a : DeletedCoeff 2 0) (ha : a ∈ V) : a.val ∈ ball (0 : Coeff 2) η := by
    simpa only [mem_ball_zero_iff,Submodule.norm_coe] using hsub ha
  have hlift (a : DeletedCoeff 2 0) (ha : a ∈ V) : WeightedCoeff.meanZeroWeightedLiftCLM w (F a) = Z a.val :=
    WeightedCoeff.meanZeroWeightedLift_projection w (Z a.val) ((hZb a.val (hsource a ha)).2)
  refine ⟨η,Z,V,W,G,hη,hZa,hZ0,hphysical,hV,hW,h0V,by simpa only [hF0] using h0W,hsub,
    himage,hbij,hFaV,hGa,?_,?_,?_⟩
  · intro a ha
    exact ⟨hleft a ha,hlift a ha⟩
  · intro b hb
    obtain ⟨hGb,he⟩ := hright b hb
    exact ⟨hGb,(hlift (G b) hGb).symm.trans (by rw [he])⟩
  · intro p hmean a ha
    have hp := hphysical p (hsource a ha)
    refine ⟨hp,?_⟩
    rw [← hp]
    exact hleft a ha

end NLS.Articles.KdVKdV2Frequencies
