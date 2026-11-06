import NLS.Articles.KdVKdV2Frequencies.GlobalRoughSurjective
import NLS.Articles.KdVKdV2Frequencies.GlobalRoughAbelianInverseMatching
import NLS.SequenceSpaces.PhysicalRealDeletedHilbert

/-! # ONE global actual real analytic rough inverse

The actual physical real normalized Hilbert space is used on BOTH sides.
Global injectivity and surjectivity give a single equivalence. Every local
real-preserving complex inverse agrees with that SAME global inverse;
the bounded real projection transfers its analytic germs to the native
real Banach topology. No independent inverse choices are made by order.
-/
noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology NLS.KdV
open scoped ENNReal Classical
namespace NLS.Articles.KdVKdV2Frequencies.GlobalRoughAbelianForwardData

/-- The SAME actual global weak forward map in its physical real Hilbert
source and target, with the literal original weighted normalizations. -/
def realWeakForward (D : GlobalRoughAbelianForwardData) :
    physicalRealDeletedSubmodule → physicalRealDeletedSubmodule := fun a =>
  ⟨D.meanZeroForward a.val,by
    change deletedL2Conjugation (D.meanZeroForward a.val)=D.meanZeroForward a.val
    rw [←D.meanZeroForward_conjugation,a.property]⟩

@[simp] theorem realWeakForward_val (D : GlobalRoughAbelianForwardData)
    (a : physicalRealDeletedSubmodule) : (D.realWeakForward a).val=D.meanZeroForward a.val := rfl

theorem realWeakForward_bijective (D : GlobalRoughAbelianForwardData) :
    Function.Bijective D.realWeakForward := by
  constructor
  · intro a b he
    apply Subtype.ext
    apply D.meanZeroForward_injective_on_real a.val b.val
    · exact (WeightedCoeff.meanZeroWeightedLift_real_iff _ (Weight.sobolev_neg (-1)) a.val).mpr a.property
    · exact (WeightedCoeff.meanZeroWeightedLift_real_iff _ (Weight.sobolev_neg (-1)) b.val).mpr b.property
    · exact congrArg Subtype.val he
  · intro z
    obtain ⟨a,ha,hF⟩ := D.meanZeroForward_surjective_on_real z.val z.property
    exact ⟨⟨a,ha⟩,Subtype.ext hF⟩

/-- ONE fixed equivalence of the actual entire real rough source and
actual entire real weak target. -/
def realWeakEquiv (D : GlobalRoughAbelianForwardData) :
    physicalRealDeletedSubmodule ≃ physicalRealDeletedSubmodule :=
  Equiv.ofBijective D.realWeakForward D.realWeakForward_bijective

@[simp] theorem realWeakEquiv_apply (D : GlobalRoughAbelianForwardData)
    (a : physicalRealDeletedSubmodule) : D.realWeakEquiv a=D.realWeakForward a := rfl

theorem realWeakForward_analytic (D : GlobalRoughAbelianForwardData) :
    AnalyticOnNhd ℝ D.realWeakForward univ := by
  intro a _
  have hr := (WeightedCoeff.meanZeroWeightedLift_real_iff _ (Weight.sobolev_neg (-1)) a.val).mpr a.property
  have ha : a.val∈D.meanZeroDomain := D.real_mem_domain _ hr
  have h := analyticAt_physicalRealDeletedRestriction (D.meanZeroForward_analytic a.val ha)
  have he : physicalRealDeletedRestriction D.meanZeroForward=D.realWeakForward := by
    funext b
    exact physicalRealDeletedProjection_coe (D.realWeakForward b)
  rwa [he] at h

/-- At EVERY real target, one actual OPEN complex analytic inverse germ
agrees with the SAME global real inverse on its ENTIRE real target slice. -/
theorem realWeakEquiv_symm_has_complex_germ (D : GlobalRoughAbelianForwardData)
    (z : physicalRealDeletedSubmodule) :
    ∃ U : Set (DeletedCoeff 2 0), IsOpen U ∧ z.val∈U ∧
      ∃ G : DeletedCoeff 2 0 → DeletedCoeff 2 0, AnalyticOnNhd ℂ G U ∧
        G z.val=(D.realWeakEquiv.symm z).val ∧
        ∀ y : physicalRealDeletedSubmodule, y.val∈U → G y.val=(D.realWeakEquiv.symm y).val := by
  let a := D.realWeakEquiv.symm z
  have hr := (WeightedCoeff.meanZeroWeightedLift_real_iff _ (Weight.sobolev_neg (-1)) a.val).mpr a.property
  obtain ⟨U,hU,haU,G,hG,hGa,hd⟩ := D.exists_real_weak_inverse_germ a.val hr
  have hFa : D.meanZeroForward a.val=z.val := congrArg Subtype.val (D.realWeakEquiv.apply_symm_apply z)
  refine ⟨U,hU,hFa ▸ haU,G,hG,?_,?_⟩
  · rwa [hFa] at hGa
  · intro y hy
    have hJG : deletedL2Conjugation (G y.val)=G y.val :=
      (WeightedCoeff.meanZeroWeightedLift_real_iff _ (Weight.sobolev_neg (-1)) _).mp
        ((hd y.val hy).2.2.2 y.property)
    have hF : D.realWeakEquiv (⟨G y.val,hJG⟩ : physicalRealDeletedSubmodule)=y :=
      Subtype.ext (hd y.val hy).2.1
    have he := D.realWeakEquiv.injective (hF.trans (D.realWeakEquiv.apply_symm_apply y).symm)
    exact congrArg Subtype.val he

/-- The SAME global inverse is real analytic at EVERY actual weak target
in the physical real native Hilbert topology. -/
theorem realWeakEquiv_symm_analytic (D : GlobalRoughAbelianForwardData) :
    AnalyticOnNhd ℝ D.realWeakEquiv.symm univ := by
  intro z _
  obtain ⟨U,hU,hz,G,hG,_hGz,hmatch⟩ := D.realWeakEquiv_symm_has_complex_germ z
  apply (analyticAt_physicalRealDeletedRestriction (hG z.val hz)).congr
  filter_upwards [(hU.preimage continuous_subtype_val).mem_nhds hz] with y hy
  change physicalRealDeletedProjection (G y.val)=D.realWeakEquiv.symm y
  rw [hmatch y hy]
  exact physicalRealDeletedProjection_coe _

/-- The actual global real weak map as ONE homeomorphism, with BOTH
native topologies and both actual analytic directions. -/
def realWeakHomeomorph (D : GlobalRoughAbelianForwardData) :
    physicalRealDeletedSubmodule ≃ₜ physicalRealDeletedSubmodule where
  toEquiv := D.realWeakEquiv
  continuous_toFun := D.realWeakForward_analytic.continuous
  continuous_invFun := D.realWeakEquiv_symm_analytic.continuous

@[simp] theorem realWeakHomeomorph_apply (D : GlobalRoughAbelianForwardData)
    (a : physicalRealDeletedSubmodule) : D.realWeakHomeomorph a=D.realWeakForward a := rfl

/-- ANY actual real-preserving complex weak inverse chart agrees on its
ENTIRE real target with the SAME already-fixed global inverse. -/
theorem weak_chart_inverse_eq_global (D : GlobalRoughAbelianForwardData)
    (P : OpenPartialHomeomorph (DeletedCoeff 2 0) (DeletedCoeff 2 0))
    (hP : (P : DeletedCoeff 2 0 → DeletedCoeff 2 0)=D.meanZeroForward)
    (hreal : ∀ z∈P.target, deletedL2Conjugation z=z → deletedL2Conjugation (P.symm z)=P.symm z)
    (z : physicalRealDeletedSubmodule) (hz : z.val∈P.target) :
    P.symm z.val=(D.realWeakHomeomorph.symm z).val := by
  have hJ : deletedL2Conjugation (P.symm z.val)=P.symm z.val := hreal z.val hz z.property
  have hF : D.realWeakEquiv (⟨P.symm z.val,hJ⟩ : physicalRealDeletedSubmodule)=z := by
    apply Subtype.ext
    change D.meanZeroForward (P.symm z.val)=z.val
    rw [←hP,P.right_inv hz]
  have he := D.realWeakEquiv.injective (hF.trans (D.realWeakEquiv.apply_symm_apply z).symm)
  exact congrArg Subtype.val he

end NLS.Articles.KdVKdV2Frequencies.GlobalRoughAbelianForwardData
