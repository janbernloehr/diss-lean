import NLS.Articles.KdVKdV2Frequencies.NativeMeanZeroAbelianInverse
import NLS.KdV.HillNativeAbelianActionVector
import NLS.ComplexAnalysis.AnalyticInverseVectorFields

/-! # The actual action Hamiltonian fields in one native analytic Abelian chart

One pair of complex mean-zero neighborhoods works before every positive action
index. The pulled-back signed rotations are analytic vector fields and agree
with the literal original physical action Hamiltonian directions at all real
sources in the chart, including sources with collapsed gaps.
-/
noncomputable section
open Set Metric
namespace NLS.Articles.KdVKdV2Frequencies
open NLS.KdV NLS.ComplexAnalysis

theorem exists_hillPhysical_native_action_hamiltonian_fields :
    ∃ η : ℝ, ∃ Z : Coeff 2 → WeightedCoeff (hillAbelianTargetWeight SpectralWeight.one) 2,
      ∃ V W : Set (DeletedCoeff 2 0), ∃ G : DeletedCoeff 2 0 → DeletedCoeff 2 0,
      ∃ X : ℕ → DeletedCoeff 2 0 → DeletedCoeff 2 0,
      0 < η ∧ AnalyticOnNhd ℂ Z (ball (0 : Coeff 2) η) ∧ Z 0 = 0 ∧
      (∀ p : RealHillWeightedPotential SpectralWeight.one,
        SpectralWeight.one.doubleIndex.toCoeff p.val ∈ ball (0 : Coeff 2) η →
        Z (SpectralWeight.one.doubleIndex.toCoeff p.val) = hillPhysicalAbelianMap SpectralWeight.one p) ∧
      IsOpen V ∧ IsOpen W ∧ 0 ∈ V ∧ 0 ∈ W ∧ V ⊆ ball (0 : DeletedCoeff 2 0) η ∧
      let F := WeightedCoeff.meanZeroWeightedMap (hillAbelianTargetWeight SpectralWeight.one) Z
      F '' V = W ∧ Set.BijOn F V W ∧ AnalyticOnNhd ℂ F V ∧ AnalyticOnNhd ℂ G W ∧
      (∀ a ∈ V, G (F a) = a ∧
        WeightedCoeff.meanZeroWeightedLiftCLM (hillAbelianTargetWeight SpectralWeight.one) (F a) = Z a.val) ∧
      (∀ b ∈ W, G b ∈ V ∧ F (G b) = b) ∧
      ∀ (m : ℕ) (hm : 1 ≤ m),
        AnalyticOnNhd ℂ (X m) V ∧
        (∀ a ∈ V, X m a = (fderiv ℂ G (F a))
          (WeightedCoeff.meanZeroSignedModeGenerator (hillAbelianTargetWeight SpectralWeight.one) m (F a))) ∧
        (∀ a ∈ V, (fderiv ℂ F a) (X m a) =
          WeightedCoeff.meanZeroSignedModeGenerator (hillAbelianTargetWeight SpectralWeight.one) m (F a)) ∧
        ∀ p : RealHillWeightedPotential SpectralWeight.one,
          ∀ hmean : (SpectralWeight.one.doubleIndex.toCoeff p.val) 0 = 0,
          let a : DeletedCoeff 2 0 := ⟨SpectralWeight.one.doubleIndex.toCoeff p.val,hmean⟩
          a ∈ V → X m a = hillDeletedActionDirection p m hm ∧
            (fderiv ℂ F a) (hillDeletedActionDirection p m hm) =
              WeightedCoeff.meanZeroSignedModeGenerator (hillAbelianTargetWeight SpectralWeight.one) m (F a) := by
  obtain ⟨η,Z,V,W,G,hη,hZa,hZ0,hphysical,hV,hW,h0V,h0W,hsub,himage,hbij,hFa,hGa,hleft,hright,_hp⟩ :=
    exists_hillPhysical_native_meanZero_abelian_inverse
  let w := hillAbelianTargetWeight SpectralWeight.one
  let F := WeightedCoeff.meanZeroWeightedMap w Z
  let X := fun m => inverseTransportVectorField F G (WeightedCoeff.meanZeroSignedModeGenerator w m)
  have hzero := hillNativeAbelian_zero_mode_of_physical η hη Z hZa hphysical
  have hFG (b : DeletedCoeff 2 0) (hb : b ∈ W) : F (G b) = b := by
    change WeightedCoeff.meanZeroWeightedProjectionCLM _ (Z (G b).val) = b
    rw [(hright b hb).2,WeightedCoeff.meanZeroWeightedProjection_lift]
  refine ⟨η,Z,V,W,G,X,hη,hZa,hZ0,hphysical,hV,hW,h0V,h0W,hsub,himage,hbij,hFa,hGa,hleft,
    fun b hb => ⟨(hright b hb).1,hFG b hb⟩,?_⟩
  intro m hm
  refine ⟨analyticOnNhd_inverseTransportVectorField F G _ hFa hGa hbij.mapsTo,fun _ _ => rfl,?_,?_⟩
  · intro a ha
    exact inverseTransportVectorField_pushforward_of_right F G _ hW hFG a (hbij.mapsTo ha)
      (hleft a ha).1 (hFa a ha).differentiableAt (hGa (F a) (hbij.mapsTo ha)).differentiableAt
  intro p hmean a ha
  have hp : a.val ∈ ball (0 : Coeff 2) η := by
    simpa only [mem_ball_zero_iff,Submodule.norm_coe] using hsub ha
  have hpush := fderiv_hillNativeAbelian_meanZero_action_vector η Z hZa hzero hphysical p hmean hp m hm
  refine ⟨?_,hpush⟩
  exact inverseTransportVectorField_eq_of_pushforward F G _ hV (fun b hb => (hleft b hb).1) a ha
    (hFa a ha).differentiableAt (hGa (F a) (hbij.mapsTo ha)).differentiableAt _ hpush

end NLS.Articles.KdVKdV2Frequencies
