import NLS.Fourier.PeriodicDistributionOrderZero
import NLS.Fourier.PeriodicL1Distribution
/-! # Order-zero distributions on the physical circle

Rescaling identifies continuous period-two functions isometrically with
continuous functions on the physical circle of period L. The original smooth
tests are dense, and order-zero distributions have unique continuous extensions.
Interval L1 functions act by the source's normalized integral and agree with
the existing tempered realization. The general complex-measure representation
in (A.2) is a separate assertion.
-/
noncomputable section
open Set Filter Topology MeasureTheory
open scoped SchwartzMap BoundedContinuousFunction
namespace NLS.Fourier.SmoothPeriodicTest
variable {L : ℝ} [Fact (0 < L)]

def physicalContinuousEquiv : C(AddCircle (2:ℝ),ℂ) ≃L[ℂ] C(AddCircle L,ℂ) where
  toFun g := g.comp (AddCircle.homeomorphAddCircle L 2 (Fact.out : 0 < L).ne' (by norm_num) : C(AddCircle L, AddCircle (2 : ℝ)))
  invFun g := g.comp ((AddCircle.homeomorphAddCircle L 2 (Fact.out : 0 < L).ne' (by norm_num)).symm : C(AddCircle (2 : ℝ), AddCircle L))
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv g := by ext x; simp
  right_inv g := by ext x; simp
  continuous_toFun := (ContinuousMap.compCLM ℂ ℂ _).continuous
  continuous_invFun := (ContinuousMap.compCLM ℂ ℂ _).continuous

theorem norm_physicalContinuousEquiv (g : C(AddCircle (2:ℝ),ℂ)) :
    ‖physicalContinuousEquiv (L := L) g‖ = ‖g‖ := by
  apply le_antisymm
  · exact (ContinuousMap.norm_le _ (norm_nonneg _)).mpr (fun x => g.norm_coe_le_norm _)
  · apply (ContinuousMap.norm_le _ (norm_nonneg _)).mpr
    intro x
    have h := (physicalContinuousEquiv (L := L) g).norm_coe_le_norm
      ((AddCircle.homeomorphAddCircle L 2 (Fact.out : 0 < L).ne' (by norm_num)).symm x)
    change ‖g ((AddCircle.homeomorphAddCircle L 2 (Fact.out : 0 < L).ne' (by norm_num))
      ((AddCircle.homeomorphAddCircle L 2 (Fact.out : 0 < L).ne' (by norm_num)).symm x))‖ ≤ _ at h
    simpa only [Homeomorph.apply_symm_apply] using h

def toContinuousCLM : SmoothPeriodicTest L →L[ℂ] C(AddCircle L,ℂ) :=
  physicalContinuousEquiv.toContinuousLinearMap.comp toContinuousTwoCLM

theorem toContinuousCLM_apply (f : SmoothPeriodicTest L) (x : ℝ) :
    toContinuousCLM f (x : AddCircle L) = f x := by
  have hL : 0 < L := Fact.out
  change toContinuousTwo f ((AddCircle.homeomorphAddCircle L 2 hL.ne' (by norm_num)) (x : AddCircle L)) = f x
  rw [AddCircle.homeomorphAddCircle_apply_mk,toContinuousTwo_apply]
  field_simp

theorem norm_toContinuousCLM (f : SmoothPeriodicTest L) :
    ‖toContinuousCLM f‖ = cNorm (Fact.out : 0 < L).ne' 0 f := by
  change ‖physicalContinuousEquiv (toContinuousTwo f)‖ = _
  rw [norm_physicalContinuousEquiv,norm_toContinuousTwo]

theorem denseRange_toContinuousCLM : DenseRange (toContinuousCLM (L := L)) :=
  physicalContinuousEquiv.surjective.denseRange.comp denseRange_toContinuousTwo physicalContinuousEquiv.continuous

namespace Distribution
/-- The order-zero extension theorem on the original physical circle. -/
theorem order_zero_iff_physical_extension (u : Distribution L) :
    u.order = 0 ↔ ∃! v : C(AddCircle L,ℂ) →L[ℂ] ℂ,
      ∀ f : SmoothPeriodicTest L, v (toContinuousCLM f) = u f := by
  have hiff : u.order = 0 ↔ u.HasOrderAtMost 0 := by
    rw [order_zero_iff_extension,hasOrderAtMost_zero_iff_extension]
  rw [hiff]
  constructor
  · rintro ⟨C,hC,hb⟩
    have hn : ∀ f, ‖u.toLinearMap f‖ ≤ C*‖toContinuousCLM (L := L) f‖ := by
      intro f
      rw [norm_toContinuousCLM]
      exact hb f
    let v := u.toLinearMap.extendOfNorm toContinuousCLM.toLinearMap
    have hv (f : SmoothPeriodicTest L) : v (toContinuousCLM f) = u f :=
      LinearMap.extendOfNorm_eq denseRange_toContinuousCLM ⟨C,hn⟩ f
    refine ⟨v,hv,?_⟩
    intro w hw
    apply DFunLike.coe_injective
    apply (denseRange_toContinuousCLM (L := L)).equalizer w.continuous v.continuous
    funext f
    exact (hw f).trans (hv f).symm
  · rintro ⟨v,hv,_⟩
    refine ⟨‖v‖+1,by positivity,?_⟩
    intro f
    rw [← hv f,← norm_toContinuousCLM]
    exact (v.le_opNorm _).trans (mul_le_mul_of_nonneg_right (by linarith) (norm_nonneg _))

/-- An interval L1 function defines the original periodic distribution. -/
def ofL1 (f : ℝ → ℂ) (hf : IntervalIntegrable f volume 0 L) : Distribution L :=
  (periodicL1Functional L f hf).comp toContinuousCLM

theorem ofL1_apply (f : ℝ → ℂ) (hf : IntervalIntegrable f volume 0 L) (g : SmoothPeriodicTest L) :
    ofL1 f hf g = (L:ℂ)⁻¹ * ∫ x in (0:ℝ)..L, f x*g x := by
  change periodicL1Functional L f hf (toContinuousCLM g) = _
  rw [periodicL1Functional_apply]
  simp only [toContinuousCLM_apply]

theorem ofL1_order (f : ℝ → ℂ) (hf : IntervalIntegrable f volume 0 L) : (ofL1 f hf).order = 0 := by
  apply (order_zero_iff_physical_extension _).mpr
  refine ⟨periodicL1Functional L f hf,fun _ => rfl,?_⟩
  intro v hv
  apply DFunLike.coe_injective
  apply (denseRange_toContinuousCLM (L := L)).equalizer v.continuous (periodicL1Functional L f hf).continuous
  exact funext hv

theorem ofL1_eq_ofTempered (f : ℝ → ℂ) (hf : IntervalIntegrable f volume 0 L) :
    ofL1 f hf = ofTempered (periodicL1Distribution L f hf) := by
  ext g
  rw [ofL1_apply]
  exact (periodicL1Distribution_smooth_action L f hf g g.smooth g.periodic).symm

theorem toTempered_ofL1 (f : ℝ → ℂ) (hf : IntervalIntegrable f volume 0 L) :
    (ofL1 f hf).toTempered = periodicL1Distribution L f hf := by
  rw [ofL1_eq_ofTempered,toTempered_ofTempered _ (periodicL1Distribution_periodic L f hf)]

theorem ofL1_coefficient (f : ℝ → ℂ) (hf : IntervalIntegrable f volume 0 L) (n : ℤ) :
    ofL1 f hf (mode (-n)) = intervalFourierCoefficient L f n := by
  rw [← toTempered_coefficient,toTempered_ofL1,periodicL1Distribution_coefficient]
end Distribution
end NLS.Fourier.SmoothPeriodicTest
