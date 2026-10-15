import NLS.Fourier.PeriodicDistributionFourierGrowth
import Mathlib.Analysis.Normed.Operator.Extend
/-! # Density and order-zero periodic distributions

Original smooth periodic tests are dense among continuous periodic functions.
An original distribution has least order zero precisely when it extends
uniquely and continuously in the uniform norm.
-/
noncomputable section
open Set Filter Topology
open scoped SchwartzMap BoundedContinuousFunction
namespace NLS.Fourier.SmoothPeriodicTest
variable {L : ℝ} [Fact (0 < L)]

/-- Continuous periodic functions are represented on the period-two circle by physical rescaling. -/
def toContinuousTwo (f : SmoothPeriodicTest L) : C(AddCircle (2:ℝ),ℂ) :=
  NLS.Fourier.periodizationCLM (smoothPeriodicTestLift (fun x => f ((L/2)*x)))

omit [Fact (0 < L)] in
theorem toContinuousTwo_apply (f : SmoothPeriodicTest L) (x : ℝ) :
    toContinuousTwo f (x : AddCircle (2:ℝ)) = f ((L/2)*x) :=
  periodization_smoothPeriodicTestLift _ (f.smooth.comp (by fun_prop)) (periodic_periodTwoDilation L _ f.periodic) x

def toContinuousTwoLM : SmoothPeriodicTest L →ₗ[ℂ] C(AddCircle (2:ℝ),ℂ) where
  toFun := toContinuousTwo
  map_add' f g := by
    ext y
    obtain ⟨x,rfl⟩ := QuotientAddGroup.mk_surjective y
    simp only [toContinuousTwo_apply,add_apply,ContinuousMap.add_apply]
  map_smul' c f := by
    ext y
    obtain ⟨x,rfl⟩ := QuotientAddGroup.mk_surjective y
    simp only [toContinuousTwo_apply,smul_apply,ContinuousMap.smul_apply,smul_eq_mul,RingHom.id_apply]

theorem norm_toContinuousTwo (f : SmoothPeriodicTest L) :
    ‖toContinuousTwo f‖ = cNorm (Fact.out : 0 < L).ne' 0 f := by
  have hL : 0 < L := Fact.out
  simp only [cNorm_apply,Nat.zero_add,Finset.sum_range_one]
  apply le_antisymm
  · apply (ContinuousMap.norm_le _ (norm_nonneg _)).mpr
    intro y
    obtain ⟨x,rfl⟩ := QuotientAddGroup.mk_surjective y
    rw [toContinuousTwo_apply]
    exact BoundedContinuousFunction.norm_coe_le_norm (derivative hL.ne' 0 f) ((L/2)*x)
  · apply (BoundedContinuousFunction.norm_le (norm_nonneg _)).mpr
    intro x
    have h := ContinuousMap.norm_coe_le_norm (toContinuousTwo f) (((L/2)⁻¹*x : ℝ) : AddCircle (2:ℝ))
    rw [toContinuousTwo_apply,mul_inv_cancel_left₀ (by positivity : L/2 ≠ 0)] at h
    exact h

def toContinuousTwoCLM : SmoothPeriodicTest L →L[ℂ] C(AddCircle (2:ℝ),ℂ) where
  toLinearMap := toContinuousTwoLM
  cont := by
    apply withSeminorms.continuous_normedSpace_rng _ toContinuousTwoLM
    refine ⟨{0},1,?_⟩
    simp only [Finset.sup_singleton,one_smul]
    intro f
    exact (norm_toContinuousTwo f).le

theorem toContinuousTwo_ofPeriodization (g : 𝓢(ℝ,ℂ)) :
    toContinuousTwo (ofPeriodization g : SmoothPeriodicTest L) = NLS.Fourier.periodizationCLM g := by
  have hL : 0 < L := Fact.out
  ext y
  obtain ⟨x,rfl⟩ := QuotientAddGroup.mk_surjective y
  rw [toContinuousTwo_apply]
  change NLS.Fourier.periodizationCLM g _ = _
  rw [inv_mul_cancel_left₀ (by positivity : L/2 ≠ 0)]

/-- Density of the actual smooth periodic functions in the uniform norm. -/
theorem denseRange_toContinuousTwo : DenseRange (toContinuousTwo (L := L)) := by
  apply NLS.Fourier.denseRange_periodization.mono
  rintro _ ⟨g,rfl⟩
  exact ⟨ofPeriodization g,toContinuousTwo_ofPeriodization g⟩

namespace Distribution
/-- An order-zero functional has a unique continuous extension to the continuous periodic functions. -/
theorem hasOrderAtMost_zero_iff_extension (u : Distribution L) :
    u.HasOrderAtMost 0 ↔ ∃! v : C(AddCircle (2:ℝ),ℂ) →L[ℂ] ℂ,
      ∀ f : SmoothPeriodicTest L, v (toContinuousTwo f) = u f := by
  constructor
  · rintro ⟨C,hC,hb⟩
    have hn : ∀ f, ‖u.toLinearMap f‖ ≤ C*‖toContinuousTwoLM (L := L) f‖ := by
      intro f
      change ‖u f‖ ≤ C*‖toContinuousTwo f‖
      rw [norm_toContinuousTwo]
      exact hb f
    let v := u.toLinearMap.extendOfNorm toContinuousTwoLM
    have hv (f : SmoothPeriodicTest L) : v (toContinuousTwo f) = u f :=
      LinearMap.extendOfNorm_eq denseRange_toContinuousTwo ⟨C,hn⟩ f
    refine ⟨v,hv,?_⟩
    intro w hw
    apply DFunLike.coe_injective
    apply (denseRange_toContinuousTwo (L := L)).equalizer w.continuous v.continuous
    funext f
    exact (hw f).trans (hv f).symm
  · rintro ⟨v,hv,_⟩
    refine ⟨‖v‖+1,by positivity,?_⟩
    intro f
    rw [← hv f,← norm_toContinuousTwo]
    exact (v.le_opNorm _).trans (mul_le_mul_of_nonneg_right (by linarith) (norm_nonneg _))

/-- The source's criterion uses the LEAST order, including the zero functional. -/
theorem order_zero_iff_extension (u : Distribution L) :
    u.order = 0 ↔ ∃! v : C(AddCircle (2:ℝ),ℂ) →L[ℂ] ℂ,
      ∀ f : SmoothPeriodicTest L, v (toContinuousTwo f) = u f := by
  rw [← hasOrderAtMost_zero_iff_extension]
  constructor
  · intro h
    simpa only [h] using u.hasOrderAtMost_order
  · intro h
    exact Nat.eq_zero_of_le_zero (order_le h)
end Distribution
end NLS.Fourier.SmoothPeriodicTest
