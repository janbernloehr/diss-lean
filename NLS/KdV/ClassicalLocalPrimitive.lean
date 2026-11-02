import NLS.KdV.ClassicalDiscriminant
import NLS.ComplexAnalysis.LocalAnalyticSquareRoot
import Mathlib.Analysis.SpecialFunctions.Complex.Analytic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp

/-! # Local analytic primitives of the actual Hill discriminant

Away from the periodic/antiperiodic branch locus, construct both a
prescribed analytic root and a logarithm of the actual Floquet multiplier.
The logarithm is jointly analytic in energy and continuous potential. Its
hyperbolic cosine and energy derivative have the physical normalization.
These local charts do not yet select a globally normalized gap primitive.
-/
noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology NLS.ZakharovShabat
namespace NLS.KdV

/-- The actual periodic/antiperiodic radicand in the energy variable. -/
def classicalHillRadicand (p : ℂ × NLS.LinearVolterra.Curve ℂ) : ℂ :=
  classicalHillDiscriminant p.2 p.1 ^ 2 - 4

theorem analyticOnNhd_classicalHillRadicand :
    AnalyticOnNhd ℂ classicalHillRadicand univ :=
  (analyticOnNhd_classicalHillDiscriminant_joint.pow 2).sub analyticOnNhd_const

private theorem exists_local_analytic_logarithm
    {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (f : E → ℂ) (a : E) (hf : AnalyticAt ℂ f a) (hfa : f a ≠ 0) :
    ∃ V : Set E, IsOpen V ∧ a ∈ V ∧ ∃ F : E → ℂ,
      AnalyticOnNhd ℂ F V ∧ F a = log (f a) ∧ ∀ b ∈ V, exp (F b) = f b := by
  let g : E → ℂ := fun b => f b / f a
  have hg : AnalyticAt ℂ g a := hf.div_const
  have hga : g a = 1 := div_self hfa
  have hslit : g a ∈ slitPlane := by rw [hga]; simp
  let F : E → ℂ := fun b => log (g b) + log (f a)
  have hF : AnalyticAt ℂ F a := ((analyticAt_clog hslit).comp (f := g) hg).add analyticAt_const
  have hgood : ∀ᶠ b in 𝓝 a, AnalyticAt ℂ F b ∧ g b ∈ slitPlane :=
    hF.eventually_analyticAt.and (hg.continuousAt.preimage_mem_nhds (isOpen_slitPlane.mem_nhds hslit))
  obtain ⟨V,hsub,hV,ha⟩ := _root_.mem_nhds_iff.mp hgood
  refine ⟨V,hV,ha,F,(fun b hb => (hsub hb).1),?_,?_⟩
  · simp [F,hga]
  intro b hb
  dsimp only [F]
  rw [exp_add,exp_log (slitPlane_ne_zero (hsub hb).2),exp_log hfa]
  exact div_mul_cancel₀ (f b) hfa

private theorem multiplier_product (D r : ℂ) (hsq : r^2 = D^2-4) :
    ((D+r)/2)*((D-r)/2) = 1 := by
  linear_combination -hsq/4

/-- The exact energy derivative follows from the constructed trace and
sheet identities, on the actual open chart. -/
theorem hasDerivAt_classicalHill_local_primitive
    (V : Set (ℂ × NLS.LinearVolterra.Curve ℂ)) (hV : IsOpen V)
    (r F : ℂ × NLS.LinearVolterra.Curve ℂ → ℂ)
    (hF : AnalyticOnNhd ℂ F V)
    (hcosh : ∀ a ∈ V, 2*cosh (F a) = classicalHillDiscriminant a.2 a.1)
    (hsinh : ∀ a ∈ V, 2*sinh (F a) = r a)
    (a : ℂ × NLS.LinearVolterra.Curve ℂ) (ha : a ∈ V) (hr : r a ≠ 0) :
    HasDerivAt (fun z => F (z,a.2))
      (deriv (classicalHillDiscriminant a.2) a.1 / r a) a.1 := by
  have hFa : AnalyticAt ℂ (fun z => F (z,a.2)) a.1 :=
    (hF a ha).comp (f := fun z : ℂ => (z,a.2)) (analyticAt_id.prod analyticAt_const)
  have hdF := hFa.differentiableAt.hasDerivAt
  have hc := ((Complex.hasDerivAt_cosh (F a)).comp a.1 hdF).const_mul 2
  have hmap : Continuous (fun z : ℂ => (z,a.2)) := continuous_id.prodMk continuous_const
  have he : classicalHillDiscriminant a.2 =ᶠ[𝓝 a.1]
      (fun z => 2*cosh (F (z,a.2))) := by
    filter_upwards [hmap.continuousAt.preimage_mem_nhds (hV.mem_nhds ha)] with z hz
    exact (hcosh (z,a.2) hz).symm
  have hd := (hc.congr_of_eventuallyEq he).deriv
  have hderiv : deriv (fun z => F (z,a.2)) a.1 =
      deriv (classicalHillDiscriminant a.2) a.1 / r a := by
    apply (eq_div_iff hr).mpr
    rw [hd,← hsinh a ha]
    ring
  rwa [hderiv] at hdF

/-- A local branch of the primitive, constructed from the actual scalar
discriminant, with an arbitrary prescribed nonzero square-root sheet. -/
theorem exists_classicalHill_local_primitive
    (p : ℂ × NLS.LinearVolterra.Curve ℂ) (w : ℂ) (hw : w ≠ 0)
    (hbase : classicalHillRadicand p = w^2) :
    ∃ V : Set (ℂ × NLS.LinearVolterra.Curve ℂ), IsOpen V ∧ p ∈ V ∧
      ∃ r F : ℂ × NLS.LinearVolterra.Curve ℂ → ℂ,
        AnalyticOnNhd ℂ r V ∧ AnalyticOnNhd ℂ F V ∧ r p = w ∧
        F p = log ((classicalHillDiscriminant p.2 p.1+w)/2) ∧
        ∀ a ∈ V, r a ≠ 0 ∧ r a^2 = classicalHillRadicand a ∧
          exp (F a) = (classicalHillDiscriminant a.2 a.1+r a)/2 ∧
          2*cosh (F a) = classicalHillDiscriminant a.2 a.1 ∧
          2*sinh (F a) = r a ∧
          HasDerivAt (fun z => F (z,a.2))
            (deriv (classicalHillDiscriminant a.2) a.1 / r a) a.1 := by
  obtain ⟨U,hU,hpU,r,hr,hrp,hsq⟩ := ComplexAnalysis.exists_local_analytic_squareRoot
    classicalHillRadicand p w (analyticOnNhd_classicalHillRadicand p (mem_univ _)) hw hbase
  let M : ℂ × NLS.LinearVolterra.Curve ℂ → ℂ :=
    fun a => (classicalHillDiscriminant a.2 a.1+r a)/2
  have hM : AnalyticOnNhd ℂ M U :=
    ((analyticOnNhd_classicalHillDiscriminant_joint.mono (subset_univ _)).add hr).div_const
  have hprod (a) (ha : a ∈ U) : M a * ((classicalHillDiscriminant a.2 a.1-r a)/2) = 1 :=
    multiplier_product _ _ (hsq a ha).2
  have hM0 : M p ≠ 0 := by
    intro hz
    have h := hprod p hpU
    rw [hz,zero_mul] at h
    exact zero_ne_one h
  obtain ⟨W,hW,hpW,F,hF,hFp,hFM⟩ := exists_local_analytic_logarithm M p (hM p hpU) hM0
  have hcosh (a) (ha : a ∈ U ∩ W) : 2*cosh (F a) = classicalHillDiscriminant a.2 a.1 := by
    have he : exp (F a) = M a := hFM a ha.2
    have hneg : exp (-F a) = (classicalHillDiscriminant a.2 a.1-r a)/2 := by
      apply mul_left_cancel₀ (exp_ne_zero (F a))
      rw [← exp_add,add_neg_cancel,exp_zero,he,hprod a ha.1]
    rw [cosh,he,hneg]
    dsimp only [M]
    ring
  have hsinh (a) (ha : a ∈ U ∩ W) : 2*sinh (F a) = r a := by
    have he : exp (F a) = M a := hFM a ha.2
    have hneg : exp (-F a) = (classicalHillDiscriminant a.2 a.1-r a)/2 := by
      apply mul_left_cancel₀ (exp_ne_zero (F a))
      rw [← exp_add,add_neg_cancel,exp_zero,he,hprod a ha.1]
    rw [sinh,he,hneg]
    dsimp only [M]
    ring
  refine ⟨U ∩ W,hU.inter hW,⟨hpU,hpW⟩,r,F,hr.mono inter_subset_left,
    hF.mono inter_subset_right,hrp,?_,?_⟩
  · simpa only [M,hrp] using hFp
  intro a ha
  exact ⟨(hsq a ha.1).1,(hsq a ha.1).2,hFM a ha.2,hcosh a ha,hsinh a ha,
    hasDerivAt_classicalHill_local_primitive (U ∩ W) (hU.inter hW) r F
      (hF.mono inter_subset_right) hcosh hsinh a ha (hsq a ha.1).1⟩

/-- Every point off the actual branch locus has a jointly analytic
primitive chart; no root or primitive is supplied as an assumption. -/
theorem exists_classicalHill_local_primitive_of_radicand_ne_zero
    (p : ℂ × NLS.LinearVolterra.Curve ℂ) (hp : classicalHillRadicand p ≠ 0) :
    ∃ V : Set (ℂ × NLS.LinearVolterra.Curve ℂ), IsOpen V ∧ p ∈ V ∧
      ∃ r F : ℂ × NLS.LinearVolterra.Curve ℂ → ℂ,
        AnalyticOnNhd ℂ r V ∧ AnalyticOnNhd ℂ F V ∧
        ∀ a ∈ V, r a ≠ 0 ∧ r a^2 = classicalHillRadicand a ∧
          exp (F a) = (classicalHillDiscriminant a.2 a.1+r a)/2 ∧
          2*cosh (F a) = classicalHillDiscriminant a.2 a.1 ∧
          2*sinh (F a) = r a ∧
          HasDerivAt (fun z => F (z,a.2))
            (deriv (classicalHillDiscriminant a.2) a.1 / r a) a.1 := by
  let w := Complex.sqrt (classicalHillRadicand p)
  have hwsq : w^2 = classicalHillRadicand p := by
    have h := Complex.cpow_nat_inv_pow (classicalHillRadicand p) (Nat.succ_ne_zero 1)
    norm_num at h
    simpa only [w,Complex.sqrt,one_div] using h
  have hw : w ≠ 0 := by
    intro hz
    apply hp
    rw [← hwsq,hz]
    norm_num
  obtain ⟨V,hV,hpV,r,F,hr,hF,_,_,hspec⟩ :=
    exists_classicalHill_local_primitive p w hw hwsq.symm
  exact ⟨V,hV,hpV,r,F,hr,hF,hspec⟩

end NLS.KdV
