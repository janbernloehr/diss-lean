import NLS.SequenceSpaces.PeriodOneSobolevMiuraMap
import NLS.SequenceSpaces.PeriodOneMiuraLinearRegularity
import Mathlib.Analysis.Normed.Operator.Banach

/-! # The actual Miura Jacobian is invertible in the stronger Sobolev norms

The literal weak Jacobian and the native Sobolev Jacobian commute with
coefficient inclusions. Linear regularity transfers actual weak bijectivity
to EVERY eligible Sobolev order. The Banach inverse theorem supplies the
bounded inverse; a Neumann estimate verifies the needed weak bijectivity
for the actual large-mass construction.
-/
noncomputable section
set_option autoImplicit false
open Set Complex Filter Topology
open scoped ENNReal
namespace NLS

/-- The ACTUAL shifted Miura Jacobian from L2 to H-minus-one. -/
def periodOneMiuraJacobian (m : ℕ) (u : Coeff 2) : Coeff 2 →L[ℂ] PeriodOneHminusOne :=
  periodOneMassOperator m+(2 : ℂ) • periodOneMiuraProduct u

@[simp] theorem periodOneMiuraJacobian_apply (m : ℕ) (u v : Coeff 2) (n : ℤ) :
    (periodOneMiuraJacobian m u v).val n=
      periodOneMassSymbol m n*v n+2*(periodOneMiuraProduct u v).val n := by
  simp only [periodOneMiuraJacobian,_root_.add_apply,_root_.smul_apply,
    WeightedCoeff.add_val,WeightedCoeff.smul_val,periodOneMassOperator_apply]

/-- Strong and weak Jacobians are the SAME actual coefficient operator. -/
theorem periodOneSobolevMiuraJacobian_inclusion (m : ℕ) (t : ℝ) (ht : 0≤t)
    (a v : WeightedCoeff (Weight.sobolev t) 2) :
    WeightedCoeff.sobolevInclusion (by linarith : -1≤t-1)
      (periodOneSobolevMiuraJacobian m t ht a v)=
      periodOneMiuraJacobian m (WeightedCoeff.sobolevToL2 ht a) (WeightedCoeff.sobolevToL2 ht v) := by
  apply Subtype.ext
  funext n
  simp only [WeightedCoeff.sobolevInclusion_apply,periodOneSobolevMiuraJacobian_apply,
    periodOneMiuraJacobian_apply,periodOneMiuraProduct_apply,WeightedCoeff.sobolevToL2_apply]

/-- Actual weak bijectivity and the proved linear regularity yield
bijectivity in EVERY stronger native Sobolev pair. -/
theorem bijective_periodOneSobolevMiuraJacobian_of_weak
    (m : ℕ) (t : ℝ) (ht : 0≤t) (a : WeightedCoeff (Weight.sobolev t) 2)
    (hweak : Function.Bijective (periodOneMiuraJacobian m (WeightedCoeff.sobolevToL2 ht a))) :
    Function.Bijective (periodOneSobolevMiuraJacobian m t ht a) := by
  constructor
  · intro v w hvw
    have h := congrArg (WeightedCoeff.sobolevInclusion (by linarith : -1≤t-1)) hvw
    rw [periodOneSobolevMiuraJacobian_inclusion,periodOneSobolevMiuraJacobian_inclusion] at h
    have H := hweak.1 h
    apply Subtype.ext
    funext n
    simpa only [WeightedCoeff.sobolevToL2_apply] using congrArg (fun b : Coeff 2 => b n) H
  · intro f
    let F : PeriodOneHminusOne := WeightedCoeff.sobolevInclusion (by linarith : -1≤t-1) f
    obtain ⟨v,hv⟩ := hweak.2 F
    have he (n : ℤ) : periodOneMassSymbol m n*v n+
        2*(periodOneMiuraProduct (WeightedCoeff.sobolevToL2 ht a) v).val n=F.val n := by
      simpa only [periodOneMiuraJacobian_apply] using congrArg (fun p : PeriodOneHminusOne => p.val n) hv
    have ha : Memℓp (fun n => (Weight.sobolev ((t-1)+1) n : ℂ)*
        WeightedCoeff.sobolevToL2 ht a n) 2 := by
      simpa only [sub_add_cancel,WeightedCoeff.sobolevToL2_apply] using
        (show Memℓp (fun n => (Weight.sobolev t n : ℂ)*a.val n) 2 from a.property)
    have hf : Memℓp (fun n => (Weight.sobolev (t-1) n : ℂ)*F.val n) 2 := by
      simpa only [F,WeightedCoeff.sobolevInclusion_apply] using
        (show Memℓp (fun n => (Weight.sobolev (t-1) n : ℂ)*f.val n) 2 from f.property)
    have H := periodOneMiura_linearized_lift_mem_sobolev m (WeightedCoeff.sobolevToL2 ht a) v F
      he (t-1) (by linarith) ha hf
    have hmem : Memℓp (fun n => (Weight.sobolev t n : ℂ)*v n) 2 := by
      simpa only [sub_add_cancel] using H
    refine ⟨⟨v,hmem⟩,?_⟩
    apply Subtype.ext
    funext n
    have hh := he n
    exact (periodOneSobolevMiuraJacobian_apply m t ht a (⟨v,hmem⟩) n).trans (by
      simpa only [periodOneMiuraProduct_apply,WeightedCoeff.sobolevToL2_apply,F,
        WeightedCoeff.sobolevInclusion_apply] using hh)

/-- The bounded inverse is constructed only AFTER actual strong bijectivity. -/
def periodOneSobolevMiuraJacobianEquiv
    (m : ℕ) (t : ℝ) (ht : 0≤t) (a : WeightedCoeff (Weight.sobolev t) 2)
    (hweak : Function.Bijective (periodOneMiuraJacobian m (WeightedCoeff.sobolevToL2 ht a))) :
    WeightedCoeff (Weight.sobolev t) 2 ≃L[ℂ] WeightedCoeff (Weight.sobolev (t-1)) 2 :=
  ContinuousLinearEquiv.ofBijective (periodOneSobolevMiuraJacobian m t ht a)
    (LinearMap.ker_eq_bot.mpr (bijective_periodOneSobolevMiuraJacobian_of_weak m t ht a hweak).1)
    (LinearMap.range_eq_top.mpr (bijective_periodOneSobolevMiuraJacobian_of_weak m t ht a hweak).2)

@[simp] theorem periodOneSobolevMiuraJacobianEquiv_apply
    (m : ℕ) (t : ℝ) (ht : 0≤t) (a : WeightedCoeff (Weight.sobolev t) 2)
    (hweak : Function.Bijective (periodOneMiuraJacobian m (WeightedCoeff.sobolevToL2 ht a)))
    (v : WeightedCoeff (Weight.sobolev t) 2) :
    periodOneSobolevMiuraJacobianEquiv m t ht a hweak v=periodOneSobolevMiuraJacobian m t ht a v := rfl

/-- A concrete Neumann bound verifies weak bijectivity for the ACTUAL
large-mass shifted Miura construction; no inverse is assumed here. -/
theorem bijective_periodOneMiuraJacobian_of_small
    (m : ℕ) (u : Coeff 2) (hsmall : 2*‖periodOneMassKernel m‖*‖u‖<1) :
    Function.Bijective (periodOneMiuraJacobian m u) := by
  let D : Coeff 2 →L[ℂ] Coeff 2 := (2 : ℂ) • periodOneResolvedProduct m u
  have hD : ‖D‖≤2*‖periodOneMassKernel m‖*‖u‖ := by
    apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
    intro v
    change ‖(2 : ℂ) • periodOneResolvedProduct m u v‖≤_
    rw [norm_smul]
    norm_num only [norm_ofNat]
    have H := norm_periodOneResolvedProduct_le m u v
    nlinarith
  have hunit : IsUnit ((1 : Coeff 2 →L[ℂ] Coeff 2)+D) := by
    have H := isUnit_one_sub_of_norm_lt_one (x := -D)
      (by simpa only [norm_neg] using hD.trans_lt hsmall)
    simpa only [sub_neg_eq_add] using H
  have hb := ContinuousLinearMap.isUnit_iff_bijective.mp hunit
  have hnorm (v : Coeff 2) : ((1 : Coeff 2 →L[ℂ] Coeff 2)+D) v=
      periodOneMassInverse m (periodOneMiuraJacobian m u v) := by
    change v+(2 : ℂ) • periodOneResolvedProduct m u v=
      periodOneMassInverse m (periodOneMassOperator m v+(2 : ℂ) • periodOneMiuraProduct u v)
    rw [map_add,map_smul,periodOneMassInverse_operator]
    rfl
  constructor
  · intro v w hvw
    apply hb.1
    rw [hnorm,hnorm,hvw]
  · intro f
    obtain ⟨v,hv⟩ := hb.2 (periodOneMassInverse m f)
    refine ⟨v,periodOneMassInverse_injective m ?_⟩
    rw [←hnorm,hv]

end NLS
