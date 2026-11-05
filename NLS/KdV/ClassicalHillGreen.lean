import NLS.KdV.ClassicalHillSpectrum
import NLS.ZakharovShabat.ClassicalSolutionInjectivity
import Mathlib.Analysis.Calculus.Deriv.Star

/-! # The actual scalar Hill Green identity and spectral reality

The shared scalar IVP state gives the literal position and derivative.
For real continuous q, the imaginary Green identity excludes nonreal
energies at every unit-modulus Floquet multiplier. No NLS real-type
condition on (-1,-q) and no assumed Hill self-adjointness are used.
-/
noncomputable section
set_option autoImplicit false
open Set Complex Filter Topology MeasureTheory intervalIntegral NLS.ZakharovShabat
open NLS.LinearVolterra
open scoped ComplexConjugate
namespace NLS.KdV

theorem continuous_classicalHillFlow (q : Curve ℂ) (lambda : ℂ) (v : ℂ × ℂ) :
    Continuous (classicalHillFlow q lambda v) := continuous_solution _ _

theorem classicalHillFlow_eq_zero_imp_initial_eq_zero (q : Curve ℂ) (lambda : ℂ)
    (v : ℂ × ℂ) (t : Icc (0 : ℝ) 1) (he : classicalHillFlow q lambda v t = 0) : v = 0 := by
  obtain ⟨z,rfl⟩ := IsAlgClosed.exists_pow_nat_eq lambda (by norm_num : 0 < 2)
  rw [classicalHillFlow_eq_constantUpper q z v t] at he
  have hs : classicalSolution (constantUpperPotential q) z (constantUpperInitialVector z v) t = 0 :=
    constantUpperStateMap_injective z (he.trans (map_zero _).symm)
  have hv := classicalSolution_eq_zero_imp_initial_eq_zero _ _ _ t hs
  have h := congrArg (constantUpperStateMap z) hv
  simpa only [constantUpperStateMap_initialVector,map_zero] using h

/-- Every nonzero scalar state has a nonzero position somewhere in the
interior; this does not require reality or a boundary condition. -/
theorem exists_classicalHillFlow_position_ne_zero (q : Curve ℂ) (lambda : ℂ)
    (v : ℂ × ℂ) (hv : v ≠ 0) :
    ∃ x ∈ Ioo (0 : ℝ) 1, (classicalHillFlow q lambda v x).1 ≠ 0 := by
  by_contra h
  push Not at h
  let c : ℝ := 1/2
  have hc : c ∈ Ioo (0 : ℝ) 1 := by norm_num [c]
  have he : (fun x => (classicalHillFlow q lambda v x).1) =ᶠ[𝓝 c] (fun _ => (0 : ℂ)) := by
    filter_upwards [Ioo_mem_nhds hc.1 hc.2] with x hx
    exact h x hx
  have hd : HasDerivAt (fun x : ℝ => (classicalHillFlow q lambda v x).1)
      (classicalHillFlow q lambda v c).2 c := by
    simpa using! HasFDerivAt.hasDerivAt
      (hasDerivAt_classicalHillFlow q lambda v ⟨c,hc.1.le,hc.2.le⟩).fst
  have hg : (classicalHillFlow q lambda v c).2 = 0 := by
    have hz := he.deriv_eq
    rw [hd.deriv] at hz
    simpa only [deriv_const] using hz
  exact hv (classicalHillFlow_eq_zero_imp_initial_eq_zero q lambda v ⟨c,hc.1.le,hc.2.le⟩
    (Prod.ext (h c hc) hg))

/-- The physical position has strictly positive L2 mass for a nonzero
initial state, with the actual Lebesgue interval normalization. -/
theorem integral_classicalHillFlow_position_normSq_pos (q : Curve ℂ) (lambda : ℂ)
    (v : ℂ × ℂ) (hv : v ≠ 0) :
    0 < ∫ x in (0 : ℝ)..1, normSq (classicalHillFlow q lambda v x).1 := by
  obtain ⟨x,hx,hne⟩ := exists_classicalHillFlow_position_ne_zero q lambda v hv
  have hc : Continuous (fun x : ℝ => normSq (classicalHillFlow q lambda v x).1) :=
    continuous_normSq.comp (continuous_classicalHillFlow q lambda v).fst
  have hi := integral_lt_integral_of_continuousOn_of_le_of_exists_lt (by norm_num : (0 : ℝ) < 1)
    continuous_const.continuousOn hc.continuousOn (fun x _ => normSq_nonneg _)
    ⟨x,Ioo_subset_Icc_self hx,normSq_pos.mpr hne⟩
  simpa only [intervalIntegral.integral_zero] using hi

/-- The derivative of the imaginary boundary pairing is the exact
imaginary energy coefficient times the position mass density. -/
theorem hasDerivAt_classicalHillGreen_im (q : Curve ℂ) (lambda : ℂ) (v : ℂ × ℂ)
    (hq : ∀ t, (q t).im = 0) (t : Icc (0 : ℝ) 1) :
    HasDerivAt (fun x : ℝ => (conj (classicalHillFlow q lambda v x).1 *
      (classicalHillFlow q lambda v x).2).im)
      (-lambda.im * normSq (classicalHillFlow q lambda v t).1) t.val := by
  have hd := hasDerivAt_classicalHillFlow q lambda v t
  have hf : HasDerivAt (fun x : ℝ => (classicalHillFlow q lambda v x).1)
      (classicalHillFlow q lambda v t).2 t.val := by
    simpa using! HasFDerivAt.hasDerivAt hd.fst
  have hg : HasDerivAt (fun x : ℝ => (classicalHillFlow q lambda v x).2)
      ((q t-lambda)*(classicalHillFlow q lambda v t).1) t.val := by
    simpa using! HasFDerivAt.hasDerivAt hd.snd
  have hp := Complex.imCLM.hasFDerivAt.comp_hasDerivAt t.val (hf.star.mul hg)
  change HasDerivAt (fun x : ℝ => (conj (classicalHillFlow q lambda v x).1 *
      (classicalHillFlow q lambda v x).2).im)
    (conj (classicalHillFlow q lambda v t).2 * (classicalHillFlow q lambda v t).2 +
      conj (classicalHillFlow q lambda v t).1 * ((q t-lambda)*(classicalHillFlow q lambda v t).1)).im t.val at hp
  convert! hp using 1
  simp only [add_im,mul_im,mul_re,conj_re,conj_im,
    sub_re,sub_im,hq t,normSq_apply]
  ring

/-- The actual scalar Green identity, before imposing endpoint data. -/
theorem classicalHillGreen_im_identity (q : Curve ℂ) (lambda : ℂ) (v : ℂ × ℂ)
    (hq : ∀ t, (q t).im = 0) :
    -lambda.im * (∫ x in (0 : ℝ)..1, normSq (classicalHillFlow q lambda v x).1) =
      (conj (classicalHillFlow q lambda v 1).1 * (classicalHillFlow q lambda v 1).2).im -
        (conj v.1*v.2).im := by
  have hY := continuous_classicalHillFlow q lambda v
  have hB : Continuous (fun x : ℝ => (conj (classicalHillFlow q lambda v x).1 *
      (classicalHillFlow q lambda v x).2).im) := continuous_im.comp (hY.fst.star.mul hY.snd)
  have hmass : Continuous (fun x : ℝ => -lambda.im * normSq (classicalHillFlow q lambda v x).1) :=
    continuous_const.mul (continuous_normSq.comp hY.fst)
  have hi := integral_eq_sub_of_hasDerivAt_of_le (by norm_num : (0 : ℝ) ≤ 1) hB.continuousOn
    (fun x (hx : x ∈ Ioo (0 : ℝ) 1) => hasDerivAt_classicalHillGreen_im q lambda v hq
      ⟨x,hx.1.le,hx.2.le⟩) (hmass.intervalIntegrable 0 1)
  simpa only [intervalIntegral.integral_const_mul,classicalHillFlow_zero] using hi

/-- Every unit-modulus Floquet multiplier of a real continuous Hill
potential has real energy, including periodic and antiperiodic data. -/
theorem classicalHillFlow_energy_im_eq_zero_of_unit_multiplier
    (q : Curve ℂ) (hq : ∀ t, (q t).im = 0) (lambda σ : ℂ) (hσ : ‖σ‖ = 1)
    (v : ℂ × ℂ) (hv : v ≠ 0) (hend : classicalHillFlow q lambda v 1 = σ • v) :
    lambda.im = 0 := by
  have hi := classicalHillGreen_im_identity q lambda v hq
  have hs : conj σ*σ = 1 := by
    rw [mul_comm,Complex.mul_conj,normSq_eq_norm_sq,hσ]
    norm_num
  have hb : conj (σ*v.1)*(σ*v.2) = conj v.1*v.2 := by
    rw [map_mul]
    calc
      _ = (conj σ*σ)*(conj v.1*v.2) := by ring
      _ = _ := by rw [hs,one_mul]
  rw [hend] at hi
  simp only [Prod.smul_fst,Prod.smul_snd,smul_eq_mul,hb,sub_self] at hi
  have hm := integral_classicalHillFlow_position_normSq_pos q lambda v hv
  exact neg_eq_zero.mp ((mul_eq_zero.mp hi).resolve_right hm.ne')

end NLS.KdV
