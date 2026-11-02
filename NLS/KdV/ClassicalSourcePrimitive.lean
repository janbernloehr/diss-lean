import NLS.KdV.ClassicalFreePrimitive
import NLS.KdV.ClassicalHillSpectrum
import NLS.ComplexAnalysis.ParametricSourceLogDomain
import NLS.ComplexAnalysis.ContinuousLogarithmUnique

/-! # Actual Hill primitives continued from the free potential

Two logarithmic source integrals first continue the canonical free root,
then the free primitive. The resulting single joint open domain contains
every source segment along which the actual radicand stays nonzero and
the energy stays in the slit plane. The normalization is fixed exactly
on the whole free slice, with no undetermined logarithm period.

Coverage of canonical gap complements and moment descent to actions are
not asserted: their spectral estimates and endpoint matching remain needed.
-/
noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology NLS.ComplexAnalysis
namespace NLS.KdV

/-- The joint nonvanishing domain before source continuation. -/
def classicalHillRootDomain : Set (ℂ × NLS.LinearVolterra.Curve ℂ) :=
  {t | t.1 ∈ slitPlane ∧ classicalHillRadicand t ≠ 0}

theorem isOpen_classicalHillRootDomain : IsOpen classicalHillRootDomain :=
  (isOpen_slitPlane.preimage continuous_fst).inter
    (isOpen_ne_fun analyticOnNhd_classicalHillRadicand.continuous continuous_const)

/-- Every point of the straight potential segment must avoid the actual
branch locus. This is one explicit complex open joint domain. -/
def classicalHillContinuationDomain : Set (ℂ × NLS.LinearVolterra.Curve ℂ) :=
  sourceSegmentDomain 0 classicalHillRootDomain

theorem isOpen_classicalHillContinuationDomain : IsOpen classicalHillContinuationDomain :=
  isOpen_sourceSegmentDomain 0 _ isOpen_classicalHillRootDomain

theorem classicalHillContinuationDomain_subset :
    classicalHillContinuationDomain ⊆ classicalHillRootDomain :=
  sourceSegmentDomain_end 0 _

/-- Membership is the absence of actual scalar periodic and antiperiodic
solutions at every point of the straight potential segment. -/
theorem mem_classicalHillContinuationDomain_iff
    (t : ℂ × NLS.LinearVolterra.Curve ℂ) :
    t ∈ classicalHillContinuationDomain ↔ t.1 ∈ slitPlane ∧
      ∀ s ∈ Icc (0 : ℝ) 1,
        ¬ ((∃ v : ℂ × ℂ, v ≠ 0 ∧ classicalHillFlow ((s : ℂ) • t.2) t.1 v 1 = v) ∨
          (∃ v : ℂ × ℂ, v ≠ 0 ∧ classicalHillFlow ((s : ℂ) • t.2) t.1 v 1 = -v)) := by
  constructor
  · intro ht
    refine ⟨(classicalHillContinuationDomain_subset ht).1,?_⟩
    intro s hs
    have h := (ht s hs).2
    simpa only [sourceSegmentMap,zero_add,sub_zero,ne_eq,classicalHillRadicand_eq_zero_iff] using h
  · rintro ⟨hslit,hne⟩ s hs
    refine ⟨hslit,?_⟩
    simpa only [sourceSegmentMap,zero_add,sub_zero,ne_eq,classicalHillRadicand_eq_zero_iff] using hne s hs

theorem classicalHillContinuationDomain_segment
    (t : ℂ × NLS.LinearVolterra.Curve ℂ) (ht : t ∈ classicalHillContinuationDomain)
    (s : ℝ) (hs : s ∈ Icc (0 : ℝ) 1) :
    sourceSegmentMap 0 ((s : ℂ),t) ∈ classicalHillContinuationDomain := by
  intro r hr
  have hrs : r*s ∈ Icc (0 : ℝ) 1 :=
    ⟨mul_nonneg hr.1 hs.1, mul_le_one₀ hr.2 hs.1 hs.2⟩
  simpa only [sourceSegmentMap,zero_add,sub_zero,smul_smul,← ofReal_mul] using ht (r*s) hrs

private theorem continuationDomain_idempotent :
    sourceSegmentDomain 0 classicalHillContinuationDomain = classicalHillContinuationDomain := by
  apply Subset.antisymm (sourceSegmentDomain_end 0 _)
  intro t ht s hs
  exact classicalHillContinuationDomain_segment t ht s hs

/-- The root sheet is transported by half the radicand's logarithmic
source increment. -/
def classicalHillContinuedRoot (t : ℂ × NLS.LinearVolterra.Curve ℂ) : ℂ :=
  classicalHillFreeRoot t.1 * exp (parametricSourceLogIncrement classicalHillRadicand 0 t / 2)

theorem analyticOnNhd_classicalHillContinuedRoot :
    AnalyticOnNhd ℂ classicalHillContinuedRoot classicalHillContinuationDomain := by
  intro t ht
  have hroot := (analyticOnNhd_classicalHillFreeRoot t.1
    (classicalHillContinuationDomain_subset ht).1).comp
      (f := fun t : ℂ × NLS.LinearVolterra.Curve ℂ => t.1) analyticAt_fst
  have hlog := analyticOnNhd_parametricSourceLogIncrement_segmentDomain classicalHillRadicand 0
    classicalHillRootDomain isOpen_classicalHillRootDomain
    (analyticOnNhd_classicalHillRadicand.mono (subset_univ _)) (fun _ h => h.2) t ht
  exact hroot.mul ((hlog.div_const).cexp)

@[simp] theorem classicalHillContinuedRoot_base (z : ℂ) :
    classicalHillContinuedRoot (z,0) = classicalHillFreeRoot z := by
  simp [classicalHillContinuedRoot]

theorem classicalHillContinuedRoot_sq (t : ℂ × NLS.LinearVolterra.Curve ℂ)
    (ht : t ∈ classicalHillContinuationDomain) :
    classicalHillContinuedRoot t ^ 2 = classicalHillRadicand t := by
  have he : exp (parametricSourceLogIncrement classicalHillRadicand 0 t / 2)^2 =
      exp (parametricSourceLogIncrement classicalHillRadicand 0 t) := by
    rw [pow_two,← exp_add]
    congr 1
    ring
  rw [classicalHillContinuedRoot,mul_pow,he,classicalHillFreeRoot_sq,mul_comm]
  exact exp_parametricSourceLogIncrement_mul_of_segment classicalHillRadicand classicalHillRootDomain 0
    (analyticOnNhd_classicalHillRadicand.mono (subset_univ _)) (fun _ h => h.2) t ht

theorem classicalHillContinuedRoot_ne_zero (t : ℂ × NLS.LinearVolterra.Curve ℂ)
    (ht : t ∈ classicalHillContinuationDomain) : classicalHillContinuedRoot t ≠ 0 := by
  intro hz
  apply (classicalHillContinuationDomain_subset ht).2
  rw [← classicalHillContinuedRoot_sq t ht,hz]
  norm_num

/-- The actual multiplier belonging to the continued root sheet. -/
def classicalHillContinuedMultiplier (t : ℂ × NLS.LinearVolterra.Curve ℂ) : ℂ :=
  (classicalHillDiscriminant t.2 t.1+classicalHillContinuedRoot t)/2

theorem analyticOnNhd_classicalHillContinuedMultiplier :
    AnalyticOnNhd ℂ classicalHillContinuedMultiplier classicalHillContinuationDomain :=
  ((analyticOnNhd_classicalHillDiscriminant_joint.mono (subset_univ _)).add
    analyticOnNhd_classicalHillContinuedRoot).div_const

theorem classicalHillContinuedMultiplier_product (t : ℂ × NLS.LinearVolterra.Curve ℂ)
    (ht : t ∈ classicalHillContinuationDomain) :
    classicalHillContinuedMultiplier t *
      ((classicalHillDiscriminant t.2 t.1-classicalHillContinuedRoot t)/2) = 1 := by
  have h := classicalHillContinuedRoot_sq t ht
  dsimp only [classicalHillRadicand] at h
  dsimp only [classicalHillContinuedMultiplier]
  linear_combination -h/4

theorem classicalHillContinuedMultiplier_ne_zero (t : ℂ × NLS.LinearVolterra.Curve ℂ)
    (ht : t ∈ classicalHillContinuationDomain) : classicalHillContinuedMultiplier t ≠ 0 := by
  intro hz
  have h := classicalHillContinuedMultiplier_product t ht
  rw [hz,zero_mul] at h
  exact zero_ne_one h

/-- The free primitive is continued without choosing any new principal
logarithm on the spectral domain. -/
def classicalHillContinuedPrimitive : ℂ × NLS.LinearVolterra.Curve ℂ → ℂ :=
  parametricSourceLogExtension classicalHillContinuedMultiplier 0 classicalHillFreePrimitive

theorem analyticOnNhd_classicalHillContinuedPrimitive :
    AnalyticOnNhd ℂ classicalHillContinuedPrimitive classicalHillContinuationDomain := by
  rw [← continuationDomain_idempotent]
  apply analyticOnNhd_parametricSourceLogExtension _ _ _ _
    isOpen_classicalHillContinuationDomain analyticOnNhd_classicalHillContinuedMultiplier
    classicalHillContinuedMultiplier_ne_zero
  intro z hz
  exact analyticOnNhd_classicalHillFreePrimitive z (classicalHillContinuationDomain_subset hz).1

@[simp] theorem classicalHillContinuedPrimitive_base (z : ℂ) :
    classicalHillContinuedPrimitive (z,0) = classicalHillFreePrimitive z :=
  parametricSourceLogExtension_base _ _ _ _

theorem exp_classicalHillContinuedPrimitive (t : ℂ × NLS.LinearVolterra.Curve ℂ)
    (ht : t ∈ classicalHillContinuationDomain) :
    exp (classicalHillContinuedPrimitive t) = classicalHillContinuedMultiplier t := by
  apply exp_parametricSourceLogExtension _ _ _ classicalHillContinuationDomain
    analyticOnNhd_classicalHillContinuedMultiplier classicalHillContinuedMultiplier_ne_zero
    (fun z _ => ?_) t
    (by rwa [continuationDomain_idempotent])
  simpa only [classicalHillContinuedMultiplier,classicalHillContinuedRoot_base] using
    exp_classicalHillFreePrimitive z

theorem classicalHillContinuedPrimitive_trace (t : ℂ × NLS.LinearVolterra.Curve ℂ)
    (ht : t ∈ classicalHillContinuationDomain) :
    2*cosh (classicalHillContinuedPrimitive t) = classicalHillDiscriminant t.2 t.1 ∧
      2*sinh (classicalHillContinuedPrimitive t) = classicalHillContinuedRoot t := by
  have he := exp_classicalHillContinuedPrimitive t ht
  have hneg : exp (-classicalHillContinuedPrimitive t) =
      (classicalHillDiscriminant t.2 t.1-classicalHillContinuedRoot t)/2 := by
    apply mul_left_cancel₀ (exp_ne_zero (classicalHillContinuedPrimitive t))
    rw [← exp_add,add_neg_cancel,exp_zero,he,classicalHillContinuedMultiplier_product t ht]
  constructor
  · rw [cosh,he,hneg]
    dsimp only [classicalHillContinuedMultiplier]
    ring
  · rw [sinh,he,hneg]
    dsimp only [classicalHillContinuedMultiplier]
    ring

theorem hasDerivAt_classicalHillContinuedPrimitive
    (t : ℂ × NLS.LinearVolterra.Curve ℂ) (ht : t ∈ classicalHillContinuationDomain) :
    HasDerivAt (fun z => classicalHillContinuedPrimitive (z,t.2))
      (deriv (classicalHillDiscriminant t.2) t.1 / classicalHillContinuedRoot t) t.1 :=
  hasDerivAt_classicalHill_local_primitive _ isOpen_classicalHillContinuationDomain _ _
    analyticOnNhd_classicalHillContinuedPrimitive
    (fun a ha => (classicalHillContinuedPrimitive_trace a ha).1)
    (fun a ha => (classicalHillContinuedPrimitive_trace a ha).2) t ht
    (classicalHillContinuedRoot_ne_zero t ht)

/-- The complete joint differential has the same logarithmic-root
formula, for arbitrary simultaneous energy and potential directions. -/
theorem hasFDerivAt_classicalHillContinuedPrimitive
    (t : ℂ × NLS.LinearVolterra.Curve ℂ) (ht : t ∈ classicalHillContinuationDomain) :
    HasFDerivAt classicalHillContinuedPrimitive
      ((classicalHillContinuedRoot t)⁻¹ •
        fderiv ℂ (fun a : ℂ × NLS.LinearVolterra.Curve ℂ => classicalHillDiscriminant a.2 a.1) t) t := by
  have hF := analyticOnNhd_classicalHillContinuedPrimitive t ht
  have he : (fun a => 2*cosh (classicalHillContinuedPrimitive a)) =ᶠ[𝓝 t]
      (fun a : ℂ × NLS.LinearVolterra.Curve ℂ => classicalHillDiscriminant a.2 a.1) := by
    filter_upwards [isOpen_classicalHillContinuationDomain.mem_nhds ht] with a ha
    exact (classicalHillContinuedPrimitive_trace a ha).1
  have hd := (((hF.differentiableAt.hasFDerivAt.ccosh).const_smul (2 : ℂ)).congr_of_eventuallyEq he.symm).fderiv
  rw [smul_smul,(classicalHillContinuedPrimitive_trace t ht).2] at hd
  have hc : (classicalHillContinuedRoot t)⁻¹ •
      fderiv ℂ (fun a : ℂ × NLS.LinearVolterra.Curve ℂ => classicalHillDiscriminant a.2 a.1) t =
        fderiv ℂ classicalHillContinuedPrimitive t := by
    rw [hd,smul_smul,inv_mul_cancel₀ (classicalHillContinuedRoot_ne_zero t ht),one_smul]
  rw [hc]
  exact hF.differentiableAt.hasFDerivAt

/-- Agreement with the continued sheet and one free value fixes the
primitive on a whole connected overlap, without an additive period. -/
theorem classicalHillContinuedPrimitive_unique
    (F : ℂ × NLS.LinearVolterra.Curve ℂ → ℂ)
    (S : Set (ℂ × NLS.LinearVolterra.Curve ℂ)) (hS : IsPreconnected S)
    (hsub : S ⊆ classicalHillContinuationDomain) (hF : ContinuousOn F S)
    (hcosh : ∀ t ∈ S, 2*cosh (F t) = classicalHillDiscriminant t.2 t.1)
    (hsinh : ∀ t ∈ S, 2*sinh (F t) = classicalHillContinuedRoot t)
    (z : ℂ) (hz : (z,0) ∈ S) (hbase : F (z,0) = classicalHillFreePrimitive z) :
    EqOn F classicalHillContinuedPrimitive S := by
  apply continuousLogarithms_eqOn F classicalHillContinuedPrimitive S hS hF
    (analyticOnNhd_classicalHillContinuedPrimitive.continuousOn.mono hsub) _ (z,0) hz
    (by simpa only [classicalHillContinuedPrimitive_base] using hbase)
  intro t ht
  rw [exp_classicalHillContinuedPrimitive t (hsub ht),← cosh_add_sinh,
    classicalHillContinuedMultiplier,← hcosh t ht,← hsinh t ht]
  ring

/-- Compact spectral contours admit one common complex potential
neighborhood inside the constructed continuation domain. -/
theorem exists_classicalHillContinuation_neighborhood
    (K : Set ℂ) (hK : IsCompact K) (q : NLS.LinearVolterra.Curve ℂ)
    (hKq : ∀ z ∈ K, (z,q) ∈ classicalHillContinuationDomain) :
    ∃ V : Set (NLS.LinearVolterra.Curve ℂ), IsOpen V ∧ q ∈ V ∧
      K ×ˢ V ⊆ classicalHillContinuationDomain := by
  have hsub : K ×ˢ {q} ⊆ classicalHillContinuationDomain := by
    rintro ⟨z,a⟩ ⟨hz,ha⟩
    obtain rfl := mem_singleton_iff.mp ha
    exact hKq z hz
  obtain ⟨U,V,_,hV,hKU,hqV,hUV⟩ := generalized_tube_lemma hK isCompact_singleton
    isOpen_classicalHillContinuationDomain hsub
  exact ⟨V,hV,hqV (mem_singleton q),fun t ht => hUV ⟨hKU ht.1,ht.2⟩⟩

end NLS.KdV
