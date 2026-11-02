import NLS.KdV.ClassicalHillPrimitiveSheets

/-! # Reflection of the free-normalized Hill primitive

The source-continuation domain is conjugation invariant at real continuous
potentials. Connected source paths and the free value determine the root
sign and logarithm uniquely. Hence reflection holds for the constructed
primitive, without choosing a new principal logarithm at each energy.
-/
noncomputable section
set_option autoImplicit false
open Set Complex Filter Topology NLS.LinearVolterra NLS.ComplexAnalysis
open scoped ComplexConjugate
namespace NLS.KdV

private theorem real_scaled_potential (q : Curve ℂ) (hq : ∀ t, (q t).im = 0) (s : ℝ) :
    ∀ t, (((s : ℂ) • q) t).im = 0 := by
  intro t
  simp only [ContinuousMap.smul_apply,smul_eq_mul,mul_im,ofReal_re,ofReal_im,hq t,
    mul_zero,zero_mul,add_zero]

/-- Reflection preserves the full constructed source domain at a real
potential, also at admissible real energies. -/
theorem mem_classicalHillContinuationDomain_conj
    (q : Curve ℂ) (hq : ∀ t, (q t).im = 0) (lambda : ℂ)
    (ht : (lambda,q) ∈ classicalHillContinuationDomain) :
    (conj lambda,q) ∈ classicalHillContinuationDomain := by
  intro s hs
  have h := ht s hs
  simp only [sourceSegmentMap,zero_add,sub_zero] at h ⊢
  constructor
  · rcases mem_slitPlane_iff.mp h.1 with hre | him
    · exact mem_slitPlane_iff.mpr (Or.inl (by simpa only [conj_re] using hre))
    · exact mem_slitPlane_iff.mpr (Or.inr (by simpa only [conj_im,neg_ne_zero] using him))
  · rw [classicalHillRadicand_conj _ (real_scaled_potential q hq s)]
    intro hz
    apply h.2
    simpa only [conj_conj,map_zero] using congrArg conj hz

private theorem continuousOn_source_path
    (f : ℂ × Curve ℂ → ℂ) (hf : ContinuousOn f classicalHillContinuationDomain)
    (lambda : ℂ) (q : Curve ℂ) (ht : (lambda,q) ∈ classicalHillContinuationDomain) :
    ContinuousOn (fun s : ℝ => f (lambda,(s : ℂ) • q)) (Icc (0 : ℝ) 1) := by
  apply hf.comp (by fun_prop)
  intro s hs
  simpa only [sourceSegmentMap,zero_add,sub_zero] using
    classicalHillContinuationDomain_segment (lambda,q) ht s hs

/-- The continued square root has the free-normalized reflected sign
on the entire admissible source domain at real continuous potentials. -/
theorem classicalHillContinuedRoot_conj
    (q : Curve ℂ) (hq : ∀ t, (q t).im = 0) (lambda : ℂ)
    (ht : (lambda,q) ∈ classicalHillContinuationDomain) :
    classicalHillContinuedRoot (conj lambda,q) = -conj (classicalHillContinuedRoot (lambda,q)) := by
  have htc := mem_classicalHillContinuationDomain_conj q hq lambda ht
  have hpath (z : ℂ) (hz : (z,q) ∈ classicalHillContinuationDomain)
      (s : ℝ) (hs : s ∈ Icc (0 : ℝ) 1) :
      (z,(s : ℂ) • q) ∈ classicalHillContinuationDomain := by
    simpa only [sourceSegmentMap,zero_add,sub_zero] using
      classicalHillContinuationDomain_segment (z,q) hz s hs
  have hc := continuousOn_source_path _ analyticOnNhd_classicalHillContinuedRoot.continuousOn lambda q ht
  have hcc := continuousOn_source_path _ analyticOnNhd_classicalHillContinuedRoot.continuousOn (conj lambda) q htc
  have he := isPreconnected_Icc.eq_of_sq_eq hcc hc.star.neg (by
    intro s hs
    change classicalHillContinuedRoot (conj lambda,(s : ℂ) • q)^2 =
      (-conj (classicalHillContinuedRoot (lambda,(s : ℂ) • q)))^2
    rw [classicalHillContinuedRoot_sq _ (hpath _ htc s hs),neg_sq,← map_pow,
      classicalHillContinuedRoot_sq _ (hpath _ ht s hs),
      classicalHillRadicand_conj _ (real_scaled_potential q hq s)]) (by
    intro s hs
    change -conj (classicalHillContinuedRoot (lambda,(s : ℂ) • q)) ≠ 0
    intro hz
    apply classicalHillContinuedRoot_ne_zero _ (hpath _ ht s hs)
    simpa only [conj_conj,map_zero] using congrArg conj (neg_eq_zero.mp hz))
    (y := (0 : ℝ)) (by constructor <;> norm_num) (by
      change classicalHillContinuedRoot (conj lambda,((0 : ℝ) : ℂ) • q) =
        -conj (classicalHillContinuedRoot (lambda,((0 : ℝ) : ℂ) • q))
      rw [ofReal_zero,zero_smul ℂ q,classicalHillContinuedRoot_base,classicalHillContinuedRoot_base]
      exact classicalHillFreeRoot_conj lambda (classicalHillContinuationDomain_subset ht).1)
  have he1 := he (by constructor <;> norm_num : (1 : ℝ) ∈ Icc 0 1)
  change classicalHillContinuedRoot (conj lambda,((1 : ℝ) : ℂ) • q) =
    -conj (classicalHillContinuedRoot (lambda,((1 : ℝ) : ℂ) • q)) at he1
  simpa only [ofReal_one,one_smul] using he1

/-- The primitive itself reflects with the canonical free sign, on all
admissible energies at any real continuous potential. -/
theorem classicalHillContinuedPrimitive_conj
    (q : Curve ℂ) (hq : ∀ t, (q t).im = 0) (lambda : ℂ)
    (ht : (lambda,q) ∈ classicalHillContinuationDomain) :
    classicalHillContinuedPrimitive (conj lambda,q) =
      -conj (classicalHillContinuedPrimitive (lambda,q)) := by
  have htc := mem_classicalHillContinuationDomain_conj q hq lambda ht
  have hpath (z : ℂ) (hz : (z,q) ∈ classicalHillContinuationDomain)
      (s : ℝ) (hs : s ∈ Icc (0 : ℝ) 1) :
      (z,(s : ℂ) • q) ∈ classicalHillContinuationDomain := by
    simpa only [sourceSegmentMap,zero_add,sub_zero] using
      classicalHillContinuationDomain_segment (z,q) hz s hs
  have hc := continuousOn_source_path _ analyticOnNhd_classicalHillContinuedPrimitive.continuousOn lambda q ht
  have hcc := continuousOn_source_path _ analyticOnNhd_classicalHillContinuedPrimitive.continuousOn (conj lambda) q htc
  have he := continuousLogarithms_eqOn
    (fun s : ℝ => classicalHillContinuedPrimitive (conj lambda,(s : ℂ) • q))
    (fun s : ℝ => -conj (classicalHillContinuedPrimitive (lambda,(s : ℂ) • q)))
    (Icc (0 : ℝ) 1) isPreconnected_Icc hcc hc.star.neg (by
      intro s hs
      have hsreal := real_scaled_potential q hq s
      have htr := classicalHillContinuedPrimitive_trace _ (hpath _ ht s hs)
      rw [exp_classicalHillContinuedPrimitive _ (hpath _ htc s hs)]
      dsimp only [classicalHillContinuedMultiplier]
      rw [classicalHillDiscriminant_conj _ hsreal,
        classicalHillContinuedRoot_conj _ hsreal lambda (hpath _ ht s hs)]
      change (conj (classicalHillDiscriminant ((s : ℂ) • q) lambda) -
        conj (classicalHillContinuedRoot (lambda,(s : ℂ) • q)))/2 = _
      have hexp (z : ℂ) : (2*cosh z-2*sinh z)/2 = exp (-z) := by
        rw [show (2*cosh z-2*sinh z)/2 = cosh z-sinh z by ring,cosh_sub_sinh]
      have heq : (classicalHillDiscriminant ((s : ℂ) • q) lambda -
          classicalHillContinuedRoot (lambda,(s : ℂ) • q))/2 =
          exp (-classicalHillContinuedPrimitive (lambda,(s : ℂ) • q)) := by
        rw [← htr.1,← htr.2,hexp]
      simpa only [map_div₀,map_sub,map_ofNat,← exp_conj,map_neg] using congrArg conj heq)
    0 (by constructor <;> norm_num) (by
      simp only [ofReal_zero,zero_smul ℂ q,classicalHillContinuedPrimitive_base]
      exact classicalHillFreePrimitive_conj lambda (classicalHillContinuationDomain_subset ht).1)
  simpa only [ofReal_one,one_smul] using he (by constructor <;> norm_num : (1 : ℝ) ∈ Icc 0 1)

/-- At an admissible real energy the canonical primitive is purely
imaginary. This concerns the actual source domain; no gap is filled by
asserting that its two boundary branches already agree. -/
theorem classicalHillContinuedPrimitive_re_eq_zero_of_im_eq_zero
    (q : Curve ℂ) (hq : ∀ t, (q t).im = 0) (lambda : ℂ) (him : lambda.im = 0)
    (ht : (lambda,q) ∈ classicalHillContinuationDomain) :
    (classicalHillContinuedPrimitive (lambda,q)).re = 0 := by
  have hc : conj lambda = lambda := by
    apply Complex.ext <;> simp only [conj_re,conj_im,him,neg_zero]
  have h := congrArg Complex.re (classicalHillContinuedPrimitive_conj q hq lambda ht)
  rw [hc] at h
  simp only [neg_re,conj_re] at h
  linarith

/-- The continued actual Floquet multiplier has unit modulus at each
admissible real energy of a real continuous potential. -/
theorem norm_classicalHillContinuedMultiplier_eq_one_of_im_eq_zero
    (q : Curve ℂ) (hq : ∀ t, (q t).im = 0) (lambda : ℂ) (him : lambda.im = 0)
    (ht : (lambda,q) ∈ classicalHillContinuationDomain) :
    ‖classicalHillContinuedMultiplier (lambda,q)‖ = 1 := by
  rw [← exp_classicalHillContinuedPrimitive (lambda,q) ht,norm_exp,
    classicalHillContinuedPrimitive_re_eq_zero_of_im_eq_zero q hq lambda him ht,Real.exp_zero]

end NLS.KdV
