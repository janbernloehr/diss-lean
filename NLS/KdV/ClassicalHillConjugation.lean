import NLS.KdV.ClassicalHillFlow
import NLS.KdV.ClassicalFreePrimitive
import Mathlib.Analysis.Calculus.Deriv.Star

/-! # Conjugation of the actual scalar Hill flow

Real continuous potentials give Schwarz symmetry of the actual energy
discriminant. The proof uses scalar IVP uniqueness, with the physical
position and derivative both conjugated. No real-type ZS assumption is
made for the constant-upper pair.
-/
noncomputable section
set_option autoImplicit false
open Set Complex NLS.LinearVolterra
open scoped ComplexConjugate
namespace NLS.KdV

theorem classicalHillFlow_conj (q : Curve ℂ) (hq : ∀ t, (q t).im = 0)
    (lambda : ℂ) (v : ℂ × ℂ) (t : Icc (0 : ℝ) 1) :
    classicalHillFlow q (conj lambda) (conj v.1,conj v.2) t =
      (conj (classicalHillFlow q lambda v t).1,conj (classicalHillFlow q lambda v t).2) := by
  have hY : Continuous (classicalHillFlow q lambda v) := continuous_solution _ _
  apply Eq.symm
  apply solution_unique (classicalHillCoefficientCurve q (conj lambda))
    (conj v.1,conj v.2)
    (fun x => (conj (classicalHillFlow q lambda v x).1,conj (classicalHillFlow q lambda v x).2))
    (hY.fst.star.prodMk hY.snd.star).continuousOn (by simp) _ t.property
  intro s _
  have hd := hasDerivAt_classicalHillFlow q lambda v s
  have hf : HasDerivAt (fun x : ℝ => (classicalHillFlow q lambda v x).1)
      (classicalHillFlow q lambda v s).2 s.val := by
    simpa using! HasFDerivAt.hasDerivAt hd.fst
  have hg : HasDerivAt (fun x : ℝ => (classicalHillFlow q lambda v x).2)
      ((q s-lambda)*(classicalHillFlow q lambda v s).1) s.val := by
    simpa using! HasFDerivAt.hasDerivAt hd.snd
  have hqconj : conj (q s) = q s := by
    apply Complex.ext <;> simp only [conj_re,conj_im,hq,neg_zero]
  change HasDerivAt _ (conj (classicalHillFlow q lambda v s).2,
    (q s-conj lambda)*conj (classicalHillFlow q lambda v s).1) s.val
  have hp := hf.star.prodMk hg.star
  change HasDerivAt
    (fun x : ℝ => (conj (classicalHillFlow q lambda v x).1,conj (classicalHillFlow q lambda v x).2))
    (conj (classicalHillFlow q lambda v s).2,
      conj ((q s-lambda)*(classicalHillFlow q lambda v s).1)) s.val at hp
  simpa only [map_mul,map_sub,hqconj] using hp

/-- Schwarz symmetry of the jointly entire physical energy trace. -/
theorem classicalHillDiscriminant_conj (q : Curve ℂ) (hq : ∀ t, (q t).im = 0)
    (lambda : ℂ) : classicalHillDiscriminant q (conj lambda) =
      conj (classicalHillDiscriminant q lambda) := by
  have ht : (1 : ℝ) ∈ Icc (0 : ℝ) 1 := by constructor <;> norm_num
  have h1 := classicalHillFlow_conj q hq lambda (1,0) ⟨1,ht⟩
  have h2 := classicalHillFlow_conj q hq lambda (0,1) ⟨1,ht⟩
  simp only [map_one,map_zero] at h1 h2
  rw [← classicalHillFlow_trace q (conj lambda),← classicalHillFlow_trace q lambda,
    h1,h2,map_add]

theorem classicalHillRadicand_conj (q : Curve ℂ) (hq : ∀ t, (q t).im = 0)
    (lambda : ℂ) : classicalHillRadicand (conj lambda,q) =
      conj (classicalHillRadicand (lambda,q)) := by
  simp only [classicalHillRadicand,classicalHillDiscriminant_conj q hq,
    map_sub,map_pow,map_ofNat]

/-- The free energy square root respects conjugation on its slit domain. -/
theorem classicalHillFreePrimitive_conj (lambda : ℂ) (hlambda : lambda ∈ slitPlane) :
    classicalHillFreePrimitive (conj lambda) = -conj (classicalHillFreePrimitive lambda) := by
  have hs : Complex.sqrt (conj lambda) = conj (Complex.sqrt lambda) := by
    simpa only [Complex.sqrt,map_inv₀,map_ofNat] using
      Complex.conj_cpow lambda (2⁻¹ : ℂ) (slitPlane_arg_ne_pi hlambda)
  simp only [classicalHillFreePrimitive,hs,map_mul,map_neg,conj_I]
  ring

theorem classicalHillFreeRoot_conj (lambda : ℂ) (hlambda : lambda ∈ slitPlane) :
    classicalHillFreeRoot (conj lambda) = -conj (classicalHillFreeRoot lambda) := by
  simp only [classicalHillFreeRoot,classicalHillFreePrimitive_conj lambda hlambda,
    sinh_neg,sinh_conj,map_mul,map_ofNat]
  ring

end NLS.KdV
