import NLS.Articles.KdVKdV2Frequencies.GlobalRoughActionIsospectral
import NLS.Articles.KdVKdV2Frequencies.GlobalRoughAbelianOrigin

/-! The literal original H-minus-one source of the SAME fixed global weak
inverse. Its complete signed recovery and actual discriminant invariance are
retained in the normalized weak Hilbert target, with both signs and weights. -/
noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology NLS.KdV
namespace NLS.Articles.KdVKdV2Frequencies.GlobalRoughAbelianForwardData

/-- The actual original rough source of the fixed weak inverse. -/
def realWeakInverseSource (D : GlobalRoughAbelianForwardData) (z : physicalRealDeletedSubmodule) :
    PeriodOneHminusOne := WeightedCoeff.meanZeroWeightedLiftCLM (Weight.sobolev (-1))
      (D.realWeakHomeomorph.symm z).val

theorem realWeakInverseSource_real (D : GlobalRoughAbelianForwardData) (z : physicalRealDeletedSubmodule) :
    IsRealPeriodOneHminusOne (D.realWeakInverseSource z) :=
  (WeightedCoeff.meanZeroWeightedLift_real_iff _ (Weight.sobolev_neg (-1)) _).mpr
    (D.realWeakHomeomorph.symm z).property

@[simp] theorem realWeakInverseSource_zero_mode (D : GlobalRoughAbelianForwardData) (z : physicalRealDeletedSubmodule) :
    (D.realWeakInverseSource z).val 0=0 := WeightedCoeff.meanZeroWeightedLift_zero _ _

/-- Every raw signed coefficient of the SAME actual inverse is recovered. -/
theorem realWeakInverseSource_signed (D : GlobalRoughAbelianForwardData) (z : physicalRealDeletedSubmodule) :
    D.signed (D.realWeakInverseSource z)=WeightedCoeff.meanZeroWeightedLiftCLM (Weight.sobolev (-1/2)) z.val := by
  have hp : WeightedCoeff.meanZeroWeightedProjectionCLM (Weight.sobolev (-1/2))
      (D.signed (D.realWeakInverseSource z))=z.val :=
    congrArg Subtype.val (D.realWeakHomeomorph.apply_symm_apply z)
  have he := congrArg (WeightedCoeff.meanZeroWeightedLiftCLM (Weight.sobolev (-1/2))) hp
  rw [WeightedCoeff.meanZeroWeightedLift_projection _ _
    (D.signed_zero _ (D.real_mem_domain _ (D.realWeakInverseSource_real z)))] at he
  exact he

/-- Equal normalized signed products give equal ORIGINAL entire discriminants. -/
theorem realWeakInverseSource_discriminant_eq_of_products (D : GlobalRoughAbelianForwardData)
    (z w : physicalRealDeletedSubmodule)
    (h : ∀ n : ℕ+, z.val.val (n : ℤ)*z.val.val (-(n : ℤ))=w.val.val (n : ℤ)*w.val.val (-(n : ℤ))) :
    hillHminusDiscriminant (D.realWeakInverseSource z)=hillHminusDiscriminant (D.realWeakInverseSource w) := by
  apply funext
  apply D.discriminant_eq_of_signed_actions_eq _ _ (D.realWeakInverseSource_real z)
    (D.realWeakInverseSource_real w) (D.realWeakInverseSource_zero_mode z) (D.realWeakInverseSource_zero_mode w)
  intro n
  simp only [D.realWeakInverseSource_signed,WeightedCoeff.meanZeroWeightedLift_apply,div_mul_div_comm,h n]

/-- The actual inverse source has a full complex analytic germ at EVERY
real weak target, agreeing with the SAME global inverse on the whole real slice. -/
theorem realWeakInverseSource_has_complex_germ (D : GlobalRoughAbelianForwardData)
    (z : physicalRealDeletedSubmodule) :
    ∃ U : Set (DeletedCoeff 2 0), IsOpen U ∧ z.val∈U ∧
      ∃ G : DeletedCoeff 2 0 → PeriodOneHminusOne, AnalyticOnNhd ℂ G U ∧
        G z.val=D.realWeakInverseSource z ∧
        ∀ y : physicalRealDeletedSubmodule, y.val∈U → G y.val=D.realWeakInverseSource y := by
  obtain ⟨U,hU,hz,G,hG,hGz,hmatch⟩ := D.realWeakEquiv_symm_has_complex_germ z
  let L := WeightedCoeff.meanZeroWeightedLiftCLM (Weight.sobolev (-1))
  refine ⟨U,hU,hz,L ∘ G,?_,?_,?_⟩
  · intro y hy
    exact (L.analyticAt _).comp (hG y hy)
  · exact congrArg L hGz
  · intro y hy
    exact congrArg L (hmatch y hy)

@[simp] theorem realWeakInverseSource_zero (D : GlobalRoughAbelianForwardData) :
    D.realWeakInverseSource 0=0 := by
  have hF : D.realWeakHomeomorph 0=0 := by
    apply Subtype.ext
    change WeightedCoeff.meanZeroWeightedProjectionCLM (Weight.sobolev (-1/2))
      (D.signed (WeightedCoeff.meanZeroWeightedLiftCLM (Weight.sobolev (-1)) 0))=0
    simp only [map_zero,D.signed_at_origin]
  have he : D.realWeakHomeomorph.symm 0=0 := by
    simpa only [Homeomorph.symm_apply_apply] using (congrArg D.realWeakHomeomorph.symm hF).symm
  simp only [realWeakInverseSource,he,Submodule.coe_zero,map_zero]

/-- Applying the SAME weak inverse to the normalized signed forward output
recovers EVERY original real mean-zero rough source, coefficient for coefficient. -/
theorem realWeakInverseSource_of_signed (D : GlobalRoughAbelianForwardData)
    (q : PeriodOneHminusOne) (hq : IsRealPeriodOneHminusOne q) (hm : q.val 0=0) :
    let z : physicalRealDeletedSubmodule :=
      ⟨WeightedCoeff.meanZeroWeightedProjectionCLM (Weight.sobolev (-1/2)) (D.signed q),
        meanZeroWeightedProjection_real _ (Weight.sobolev_neg (-1/2)) _ (D.signed_real q hq)⟩
    D.realWeakInverseSource z=q := by
  intro z
  let a : physicalRealDeletedSubmodule :=
    ⟨WeightedCoeff.meanZeroWeightedProjectionCLM (Weight.sobolev (-1)) q,
      meanZeroWeightedProjection_real _ (Weight.sobolev_neg (-1)) q hq⟩
  have ha : WeightedCoeff.meanZeroWeightedLiftCLM (Weight.sobolev (-1)) a.val=q :=
    WeightedCoeff.meanZeroWeightedLift_projection _ q hm
  have hf : D.realWeakHomeomorph a=z := by
    apply Subtype.ext
    change WeightedCoeff.meanZeroWeightedProjectionCLM (Weight.sobolev (-1/2))
      (D.signed (WeightedCoeff.meanZeroWeightedLiftCLM (Weight.sobolev (-1)) a.val))=_
    rw [ha]
  rw [←hf,realWeakInverseSource,Homeomorph.symm_apply_apply]
  exact ha

end NLS.Articles.KdVKdV2Frequencies.GlobalRoughAbelianForwardData
