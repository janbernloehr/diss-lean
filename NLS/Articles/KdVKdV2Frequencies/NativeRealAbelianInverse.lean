import NLS.Articles.KdVKdV2Frequencies.NativeMeanZeroAbelianInverse
import NLS.KdV.HillNativeAbelianRealEquivariance
import NLS.SequenceSpaces.DeletedRealLocalInverse

/-! # A local analytic inverse of the actual physical real Abelian map at zero

The source is mean-zero period-one L2, the target carries the actual half-shift
weight. The inverse is analytic on a complex neighborhood and preserves the
physical real form there. Global bijectivity, canonicality, rough regularity
and the main article frequency conclusions are separate obligations.
-/
noncomputable section
open Set Metric
namespace NLS.Articles.KdVKdV2Frequencies
open NLS.KdV

theorem exists_hillPhysical_native_real_abelian_inverse :
    ∃ η : ℝ, ∃ Z : Coeff 2 → WeightedCoeff (hillAbelianTargetWeight SpectralWeight.one) 2,
      ∃ V W : Set (DeletedCoeff 2 0), ∃ G : DeletedCoeff 2 0 → DeletedCoeff 2 0,
      0 < η ∧ AnalyticOnNhd ℂ Z (ball (0 : Coeff 2) η) ∧ Z 0 = 0 ∧
      IsOpen V ∧ IsOpen W ∧ 0 ∈ V ∧ 0 ∈ W ∧ V ⊆ ball (0 : DeletedCoeff 2 0) η ∧
      let F := WeightedCoeff.meanZeroWeightedMap (hillAbelianTargetWeight SpectralWeight.one) Z
      F '' V = W ∧ Set.BijOn F V W ∧ AnalyticOnNhd ℂ F V ∧ AnalyticOnNhd ℂ G W ∧
      (∀ a ∈ V, G (F a) = a ∧
        WeightedCoeff.meanZeroWeightedLiftCLM (hillAbelianTargetWeight SpectralWeight.one) (F a) = Z a.val) ∧
      (∀ b ∈ W, G b ∈ V ∧ Z (G b).val =
        WeightedCoeff.meanZeroWeightedLiftCLM (hillAbelianTargetWeight SpectralWeight.one) b) ∧
      (∀ b ∈ W, deletedL2Conjugation b = b → deletedL2Conjugation (G b) = G b) ∧
      (∀ b ∈ W, deletedL2Conjugation b = b →
        ∃ p : RealHillWeightedPotential SpectralWeight.one,
          SpectralWeight.one.doubleIndex.toCoeff p.val = (G b).val ∧
          (SpectralWeight.one.doubleIndex.toCoeff p.val) 0 = 0 ∧
          hillPhysicalAbelianMap SpectralWeight.one p =
            WeightedCoeff.meanZeroWeightedLiftCLM (hillAbelianTargetWeight SpectralWeight.one) b) ∧
      ∀ p : RealHillWeightedPotential SpectralWeight.one,
        ∀ hmean : (SpectralWeight.one.doubleIndex.toCoeff p.val) 0 = 0,
        let a : DeletedCoeff 2 0 := ⟨SpectralWeight.one.doubleIndex.toCoeff p.val,hmean⟩
        a ∈ V → Z a.val = hillPhysicalAbelianMap SpectralWeight.one p ∧
          G (WeightedCoeff.meanZeroWeightedProjectionCLM (hillAbelianTargetWeight SpectralWeight.one)
            (hillPhysicalAbelianMap SpectralWeight.one p)) = a := by
  obtain ⟨η,Z,V,W,G,hη,hZa,hZ0,hphysical,hV,hW,h0V,h0W,hsub,himage,hbij,hFa,hGa,hleft,hright,hp⟩ :=
    exists_hillPhysical_native_meanZero_abelian_inverse
  let F := WeightedCoeff.meanZeroWeightedMap (hillAbelianTargetWeight SpectralWeight.one) Z
  have hF0 : F 0 = 0 := by
    change WeightedCoeff.meanZeroWeightedProjectionCLM _ (Z 0) = 0
    rw [hZ0,map_zero]
  have hconj := hillNativeAbelian_meanZero_conjugation η hη Z hZa hphysical
  have hFG (b : DeletedCoeff 2 0) (hb : b ∈ W) : F (G b) = b := by
    change WeightedCoeff.meanZeroWeightedProjectionCLM _ (Z (G b).val) = b
    rw [(hright b hb).2,WeightedCoeff.meanZeroWeightedProjection_lift]
  obtain ⟨U,hU,h0U,hUW,hreal⟩ := exists_real_preserving_inverse_neighborhood F G V W hV hW h0V h0W
    hF0 hGa.continuousOn hbij.injOn (fun a ha => (hleft a ha).1)
    (fun b hb => ⟨(hright b hb).1,hFG b hb⟩) η hsub hconj
  let A := V ∩ F ⁻¹' U
  have hA : IsOpen A := hFa.continuousOn.isOpen_inter_preimage hV hU
  have h0A : (0 : DeletedCoeff 2 0) ∈ A := ⟨h0V,by change F 0 ∈ U; rwa [hF0]⟩
  have hGU (b : DeletedCoeff 2 0) (hb : b ∈ U) : G b ∈ A :=
    ⟨(hright b (hUW hb)).1,by change F (G b) ∈ U; rwa [hFG b (hUW hb)]⟩
  have hbijAU : Set.BijOn F A U := by
    refine ⟨fun a ha => ha.2,fun a ha b hb he => hbij.injOn ha.1 hb.1 he,?_⟩
    intro b hb
    exact ⟨G b,hGU b hb,hFG b (hUW hb)⟩
  refine ⟨η,Z,A,U,G,hη,hZa,hZ0,hA,hU,h0A,h0U,
    fun a ha => hsub ha.1,hbijAU.image_eq,hbijAU,hFa.mono inter_subset_left,hGa.mono hUW,
    fun a ha => hleft a ha.1,fun b hb => ⟨hGU b hb,(hright b (hUW hb)).2⟩,hreal,?_,?_⟩
  · intro b hb hJb
    have hJGb : periodOneL2Conjugation (G b).val = (G b).val :=
      (deletedL2Conjugation_fixed_iff (G b)).mp (hreal b hb hJb)
    let p := hillUnitRealSourceLift (G b).val hJGb
    have hcoeff : SpectralWeight.one.doubleIndex.toCoeff p.val = (G b).val :=
      hillUnitRealSourceLift_toCoeff _ _
    have hmem : (G b).val ∈ ball (0 : Coeff 2) η := by
      simpa only [mem_ball_zero_iff,Submodule.norm_coe] using hsub (hright b (hUW hb)).1
    have he : Z (G b).val = hillPhysicalAbelianMap SpectralWeight.one p := by
      simpa only [hcoeff] using hphysical p (by simpa only [hcoeff] using hmem)
    exact ⟨p,hcoeff,by rw [hcoeff]; exact (G b).property,he.symm.trans (hright b (hUW hb)).2⟩
  · intro p hmean a ha
    exact hp p hmean ha.1

end NLS.Articles.KdVKdV2Frequencies
