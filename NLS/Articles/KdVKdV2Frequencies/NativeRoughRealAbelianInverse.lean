import NLS.Articles.KdVKdV2Frequencies.NativeRoughMeanZeroAbelianInverse
import NLS.SequenceSpaces.WeightedSourceRealEquivariance
import NLS.SequenceSpaces.DeletedRealLocalInverse

/-! # An actual real local Birkhoff inverse at the rough endpoint

The analytic signed extension admits a two-sided local inverse between
mean-zero H-minus-one and H-minus-one-half. Its inverse preserves the
physical real form, and every real target in the image neighborhood has
an actual mean-zero real H-minus-one preimage, without L2 membership.
-/
noncomputable section
set_option autoImplicit false
open Set Metric Complex
open scoped ComplexConjugate
namespace NLS.Articles.KdVKdV2Frequencies
open NLS.KdV

theorem exists_hillHminus_native_real_abelian_inverse :
    ∃ η : ℝ, ∃ Z : PeriodOneHminusOne → WeightedCoeff (Weight.sobolev (-1/2)) 2,
      ∃ U V : Set (DeletedCoeff 2 0), ∃ G : DeletedCoeff 2 0 → DeletedCoeff 2 0,
      0 < η ∧ AnalyticOnNhd ℂ Z (ball (0 : PeriodOneHminusOne) η) ∧ Z 0=0 ∧
      (∀ p : RealPeriodOneHillPotential,
        (hillPhysicalHminusEmbedding p).val∈ball (0 : PeriodOneHminusOne) η → ∀ j : ℤ,
        (Z (hillPhysicalHminusEmbedding p).val).val j=
          hillAbelianRawCoordinateSequence SpectralWeight.one (hillUnitRealSourceUnembed p) j) ∧
      IsOpen U ∧ IsOpen V ∧ 0∈U ∧ 0∈V ∧ U⊆ball (0 : DeletedCoeff 2 0) η ∧
      let F := WeightedCoeff.meanZeroWeightedMap (Weight.sobolev (-1/2))
        (fun u => Z ((WeightedCoeff.weightIsometry (Weight.sobolev (-1)) 2).symm u))
      F '' U=V ∧ Set.BijOn F U V ∧ AnalyticOnNhd ℂ F U ∧ AnalyticOnNhd ℂ G V ∧
      (∀ a∈U, G (F a)=a ∧
        WeightedCoeff.meanZeroWeightedLiftCLM (Weight.sobolev (-1/2)) (F a)=
          Z (WeightedCoeff.meanZeroWeightedLiftCLM (Weight.sobolev (-1)) a)) ∧
      (∀ b∈V, G b∈U ∧ Z (WeightedCoeff.meanZeroWeightedLiftCLM (Weight.sobolev (-1)) (G b))=
        WeightedCoeff.meanZeroWeightedLiftCLM (Weight.sobolev (-1/2)) b) ∧
      (∀ b∈V, deletedL2Conjugation b=b → deletedL2Conjugation (G b)=G b) ∧
      ∀ b∈V, deletedL2Conjugation b=b → ∃ q : PeriodOneRealHminusOne,
        q.val.val 0=0 ∧ q.val∈ball (0 : PeriodOneHminusOne) η ∧
          WeightedCoeff.meanZeroWeightedProjectionCLM (Weight.sobolev (-1)) q.val=G b ∧
          Z q.val=WeightedCoeff.meanZeroWeightedLiftCLM (Weight.sobolev (-1/2)) b := by
  obtain ⟨η,Z,U,V,G,hη,hZa,hZ0,_hcenter,hZr,hZp,hU,hV,h0U,h0V,hsub,himage,hbij,hFa,hGa,hleft,hright⟩ :=
    exists_hillHminus_native_meanZero_abelian_inverse
  let v := Weight.sobolev (-1)
  let w := Weight.sobolev (-1/2)
  let F := WeightedCoeff.meanZeroWeightedMap w
    (fun u => Z ((WeightedCoeff.weightIsometry v 2).symm u))
  have hF0 : F 0=0 := by
    change WeightedCoeff.meanZeroWeightedProjectionCLM w
      (Z ((WeightedCoeff.weightIsometry v 2).symm 0))=0
    rw [map_zero,hZ0,map_zero]
  have hconj := WeightedCoeff.weightedSource_meanZero_conjugation v w
    (Weight.sobolev_neg (-1)) (Weight.sobolev_neg (-1/2)) η hη Z hZa hZr
  have hFG (b : DeletedCoeff 2 0) (hb : b∈V) : F (G b)=b := by
    change WeightedCoeff.meanZeroWeightedProjectionCLM w
      (Z (WeightedCoeff.meanZeroWeightedLiftCLM v (G b)))=b
    rw [(hright b hb).2,WeightedCoeff.meanZeroWeightedProjection_lift]
  obtain ⟨W,hW,h0W,hWV,hreal⟩ := exists_real_preserving_inverse_neighborhood F G U V
    hU hV h0U h0V hF0 hGa.continuousOn hbij.injOn (fun a ha => (hleft a ha).1)
    (fun b hb => ⟨(hright b hb).1,hFG b hb⟩) η hsub hconj
  let A := U ∩ F ⁻¹' W
  have hA : IsOpen A := hFa.continuousOn.isOpen_inter_preimage hU hW
  have h0A : (0 : DeletedCoeff 2 0)∈A := ⟨h0U,by change F 0∈W; rwa [hF0]⟩
  have hGW (b : DeletedCoeff 2 0) (hb : b∈W) : G b∈A :=
    ⟨(hright b (hWV hb)).1,by change F (G b)∈W; rwa [hFG b (hWV hb)]⟩
  have hbijAW : Set.BijOn F A W := by
    refine ⟨fun a ha => ha.2,fun a ha b hb he => hbij.injOn ha.1 hb.1 he,?_⟩
    intro b hb
    exact ⟨G b,hGW b hb,hFG b (hWV hb)⟩
  refine ⟨η,Z,A,W,G,hη,hZa,hZ0,hZp,hA,hW,h0A,h0W,
    fun a ha => hsub ha.1,hbijAW.image_eq,hbijAW,hFa.mono inter_subset_left,hGa.mono hWV,
    fun a ha => hleft a ha.1,fun b hb => ⟨hGW b hb,(hright b (hWV hb)).2⟩,hreal,?_⟩
  intro b hb hJb
  let q := WeightedCoeff.meanZeroWeightedLiftCLM v (G b)
  have hJGb : periodOneL2Conjugation (G b).val=(G b).val :=
    (deletedL2Conjugation_fixed_iff (G b)).mp (hreal b hb hJb)
  have hqr : IsRealPeriodOneHminusOne q := by
    apply (WeightedCoeff.weightIsometry_fixed_iff_raw v (Weight.sobolev_neg (-1)) q).mp
    change periodOneL2Conjugation ((WeightedCoeff.weightIsometry v 2)
      ((WeightedCoeff.weightIsometry v 2).symm (G b).val))=
        (WeightedCoeff.weightIsometry v 2) ((WeightedCoeff.weightIsometry v 2).symm (G b).val)
    simpa only [LinearIsometryEquiv.apply_symm_apply] using hJGb
  have hqm : q.val 0=0 := by
    change (G b).val 0/(v 0 : ℂ)=0
    have hz : (G b).val 0=0 := (G b).property
    rw [hz,zero_div]
  have hqmem : q∈ball (0 : PeriodOneHminusOne) η := by
    simpa only [q,mem_ball_zero_iff,WeightedCoeff.meanZeroWeightedLift_norm] using
      hsub (hright b (hWV hb)).1
  exact ⟨⟨q,hqr⟩,hqm,hqmem,WeightedCoeff.meanZeroWeightedProjection_lift v (G b),(hright b (hWV hb)).2⟩

end NLS.Articles.KdVKdV2Frequencies
