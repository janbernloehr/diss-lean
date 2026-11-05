import NLS.MKdV.MiuraActionMoment
import NLS.MKdV.MiuraConstantActions
import NLS.ZakharovShabat.ScalarMeanCotangent

/-! # The actual physical mass trace for mKdV actions

The analytic native action moment has exactly the nonconstant mass
cotangent. Along each original real H¹ fixed-mean affine line its
difference from physical mass is constant. The constant profile has zero
positive actions, determining the remaining mean-square term.
-/
noncomputable section
open Set Filter Topology NLS.Poisson NLS.ZakharovShabat
open scoped ENNReal ComplexConjugate
namespace NLS.MKdV

def miuraH1Mass (a : ScalarDomain 2) : ℂ :=
  (1/2 : ℂ)*reflectedHilbertPairing (scalarInclusion a) (scalarInclusion a)

theorem analyticAt_miuraH1Mass (a : ScalarDomain 2) : AnalyticAt ℂ miuraH1Mass a :=
  analyticAt_const.mul ((reflectedHilbertPairing.analyticAt_bilinear _).comp₂
    (scalarInclusion.analyticAt a) (scalarInclusion.analyticAt a))

theorem hasFDerivAt_miuraH1Mass (a : ScalarDomain 2) :
    HasFDerivAt miuraH1Mass ((reflectedHilbertPairing (scalarInclusion a)).comp scalarInclusion) a := by
  have h := (reflectedHilbertPairing.hasFDerivAt_of_bilinear
    (scalarInclusion.hasFDerivAt (x := a)) (scalarInclusion.hasFDerivAt (x := a))).const_mul (1/2 : ℂ)
  convert! h using 1
  ext u
  change reflectedHilbertPairing (scalarInclusion a) (scalarInclusion u) =
    (1/2 : ℂ)*(reflectedHilbertPairing (scalarInclusion a) (scalarInclusion u)+
      reflectedHilbertPairing (scalarInclusion u) (scalarInclusion a))
  rw [reflectedHilbertPairing_comm (scalarInclusion u)]
  ring

theorem fderiv_miuraH1Mass_scalarMode (a : ScalarDomain 2) (k : ℤ) :
    fderiv ℂ miuraH1Mass a (scalarMode k 1) = a.val (-k) := by
  rw [(hasFDerivAt_miuraH1Mass a).fderiv,ContinuousLinearMap.comp_apply,scalarInclusion_scalarMode,
    reflectedHilbertPairing_comm,reflectedHilbertPairing_apply]
  simp [lp.single_apply,Pi.single_apply,scalarInclusion_apply]

/-- The actual mass and action moment have the same derivative on every fixed-mean tangent. -/
theorem fderiv_miuraMass_sub_actionMoment_zero_mean (a h : ScalarDomain 2)
    (ha : ∀ j, a.val j = conj (a.val (-j))) (hh : h.val 0 = 0) :
    fderiv ℂ (fun b => miuraH1Mass b-miuraH1ActionMoment b) a h = 0 := by
  rw [fderiv_fun_sub (analyticAt_miuraH1Mass a).differentiableAt
    (analyticAt_miuraH1ActionMoment a ha).differentiableAt]
  exact scalarCotangent_eq_zero_on_zero_mean (by simp)
    (fderiv ℂ miuraH1Mass a-fderiv ℂ miuraH1ActionMoment a)
    (by intro k hk; simp only [sub_apply,fderiv_miuraH1Mass_scalarMode,
      fderiv_miuraH1ActionMoment_scalarMode a ha k hk,sub_self]) h hh

/-- The physical mass is the signed-mean square plus the entire convergent first action moment. -/
theorem miuraH1Mass_eq_mean_sq_add_actionMoment (a : ScalarDomain 2)
    (ha : ∀ j, a.val j = conj (a.val (-j))) :
    miuraH1Mass a = (1/2 : ℂ)*(a.val 0)^2+miuraH1ActionMoment a := by
  let a₀ : ScalarDomain 2 := scalarMode 0 (a.val 0)
  have ha₀ : ∀ j, a₀.val j = conj (a₀.val (-j)) := by
    intro j
    change (scalarMode (p := 2) 0 (a.val 0)).val j = conj ((scalarMode (p := 2) 0 (a.val 0)).val (-j))
    by_cases hj : j = 0
    · subst j
      simpa only [scalarMode_apply,ite_true,neg_zero] using ha 0
    · simp [scalarMode_apply,hj]
  let v := a-a₀
  have hv : v.val 0 = 0 := by simp [v,a₀,scalarMode_apply]
  have hvreal : ∀ j, v.val j = conj (v.val (-j)) := by
    intro j
    change a.val j-a₀.val j = conj (a.val (-j)-a₀.val (-j))
    rw [map_sub,← ha j,← ha₀ j]
  let γ : ℝ → ScalarDomain 2 := fun t => a₀+(t : ℂ) • v
  have hγreal (t : ℝ) : ∀ j, (γ t).val j = conj ((γ t).val (-j)) := by
    intro j
    change a₀.val j+(t : ℂ)*v.val j = conj (a₀.val (-j)+(t : ℂ)*v.val (-j))
    rw [map_add,map_mul,Complex.conj_ofReal,← ha₀ j,← hvreal j]
  have hγd (t : ℝ) : HasDerivAt γ v t := by
    simpa only [γ,Complex.ofRealCLM_apply,Complex.ofReal_one,one_smul] using
      ((Complex.ofRealCLM.hasDerivAt (x := t)).smul_const v).const_add a₀
  have hd (t : ℝ) : HasDerivAt (fun r => miuraH1Mass (γ r)-miuraH1ActionMoment (γ r)) 0 t := by
    have hH := ((analyticAt_miuraH1Mass (γ t)).sub
      (analyticAt_miuraH1ActionMoment (γ t) (hγreal t))).differentiableAt.hasFDerivAt
    have hc := (hH.restrictScalars ℝ).comp_hasDerivAt t (hγd t)
    convert! hc using 1
    exact (fderiv_miuraMass_sub_actionMoment_zero_mean (γ t) v (hγreal t) hv).symm
  have he := is_const_of_deriv_eq_zero (fun t => (hd t).differentiableAt) (fun t => (hd t).deriv) 1 0
  have hγ0 : γ 0 = a₀ := by simp only [γ,Complex.ofReal_zero,zero_smul,add_zero]
  have hγ1 : γ 1 = a := by
    dsimp only [γ,v]
    rw [Complex.ofReal_one,one_smul]
    abel
  rw [hγ0,hγ1] at he
  have hd₀ : periodOneDerivative a₀ = 0 := by
    ext j
    rw [periodOneDerivative_apply]
    change 2*Complex.I*(Real.pi : ℂ)*j*(scalarMode (p := 2) 0 (a.val 0)).val j = 0
    by_cases hj : j = 0 <;> simp [scalarMode_apply,hj]
  have hG₀ : miuraH1ActionMoment a₀ = 0 := by
    rw [miuraH1ActionMoment,miuraH1ActionSequence_eq_zero_of_derivative_zero a₀ ha₀ hd₀,map_zero]
  have hM₀ : miuraH1Mass a₀ = (1/2 : ℂ)*(a.val 0)^2 := by
    rw [miuraH1Mass]
    change (1/2 : ℂ)*reflectedHilbertPairing (scalarInclusion (scalarMode 0 (a.val 0)))
      (scalarInclusion (scalarMode 0 (a.val 0))) = _
    simp [scalarInclusion_scalarMode,reflectedHilbertPairing_apply,lp.single_apply,Pi.single_apply,pow_two]
  rw [hG₀,hM₀,sub_zero] at he
  exact sub_eq_iff_eq_add.mp he

/-- The trace uses the independently defined native mass Hamiltonian K₁. -/
theorem miuraH1Mass_eq_nativeMiuraMass (a : ScalarDomain 2) :
    miuraH1Mass a = nativeMiuraMass 1 (miuraH1SobolevEquiv a) := by
  simp only [miuraH1Mass,nativeMiuraMass,sobolevOddKinetic,reflectedHilbertPairing_apply,
    Coeff.dualPairing_apply,Coeff.reflection_apply,hierarchySobolevJetL2_apply,
    hierarchySobolevInclusion_apply,pow_zero,one_mul,miuraH1SobolevEquiv_apply,scalarInclusion_apply]
  congr 1
  apply tsum_congr
  intro j
  ring

/-- On the physical real form, this is exactly half the original scalar L² norm squared. -/
theorem miuraH1Mass_eq_half_norm_sq (a : ScalarDomain 2)
    (ha : ∀ j, a.val j = conj (a.val (-j))) :
    miuraH1Mass a = (1/2 : ℂ)*((‖scalarInclusion a‖^2 : ℝ) : ℂ) := by
  have hpair : reflectedHilbertPairing (scalarInclusion a) (scalarInclusion a) =
      ((‖scalarInclusion a‖^2 : ℝ) : ℂ) := by
    calc
      _ = inner ℂ (scalarInclusion a) (scalarInclusion a) := by
        rw [reflectedHilbertPairing_apply,lp.inner_eq_tsum]
        apply tsum_congr
        intro j
        simp only [RCLike.inner_apply',starRingEnd_apply,scalarInclusion_apply]
        change a.val j*a.val (-j) = conj (a.val j)*a.val j
        have h := ha (-j)
        simp only [neg_neg] at h
        rw [h]
        ring
      _ = _ := by rw [inner_self_eq_norm_sq_to_K]; norm_cast
  exact congrArg (fun z : ℂ => (1/2 : ℂ)*z) hpair

/-- The actions and the literal signed mean determine the original scalar L² norm. -/
theorem miuraL2_norm_sq_eq_actions_mean (a : ScalarDomain 2)
    (ha : ∀ j, a.val j = conj (a.val (-j))) :
    ‖scalarInclusion a‖^2 = (a.val 0).re^2+2*(miuraH1ActionMoment a).re := by
  have him : (a.val 0).im = 0 := by
    have h := congrArg Complex.im (ha 0)
    simp only [neg_zero,Complex.conj_im] at h
    linarith
  have h := congrArg Complex.re (miuraH1Mass_eq_mean_sq_add_actionMoment a ha)
  rw [miuraH1Mass_eq_half_norm_sq a ha] at h
  have hre : ((a.val 0)^2).re = (a.val 0).re^2 := by
    simp [pow_two,Complex.mul_re,him]
  norm_num [Complex.mul_re,hre] at h
  rw [← Complex.ofReal_pow,Complex.ofReal_re] at h
  linarith

/-- Literal first action trace, with convergence and all original physical contour coordinates. -/
theorem hasSum_miuraMKdVActions_mass (a : ScalarDomain 2)
    (ha : ∀ j, a.val j = conj (a.val (-j))) :
    HasSum (fun n : ℕ => (2*(Real.pi : ℂ)*(n+1))*miuraMKdVAction a ha (n+1))
      (miuraH1Mass a-(1/2 : ℂ)*(a.val 0)^2) := by
  have h := hasSum_miuraH1ActionMoment_physical a ha
  rwa [miuraH1Mass_eq_mean_sq_add_actionMoment a ha,add_sub_cancel_left]

end NLS.MKdV
