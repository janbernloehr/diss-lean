import NLS.ComplexAnalysis.ParametricSourceLogDomain
import NLS.ComplexAnalysis.ContinuousLogarithmUnique
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp

/-! # Free-normalized primitives of analytic trace families

This abstracts the two source-log continuations used for the continuous
Hill discriminant. The source can be any complex normed space. The first
continuation selects the radicand root; the second fixes the primitive
without an additive logarithm period. No coverage of a spectral cut
complement is assumed or asserted.
-/

noncomputable section
open Set Complex Filter Topology
namespace NLS.ComplexAnalysis

structure TracePrimitiveFamily (A : Type) [NormedAddCommGroup A] [NormedSpace ℂ A] where
  trace : ℂ × A → ℂ
  analytic_trace : AnalyticOnNhd ℂ trace univ
  freePrimitive : ℂ → ℂ
  freeDomain : Set ℂ
  isOpen_freeDomain : IsOpen freeDomain
  analytic_freePrimitive : AnalyticOnNhd ℂ freePrimitive freeDomain
  free_trace : ∀ z, 2*cosh (freePrimitive z) = trace (z,0)

namespace TracePrimitiveFamily
variable {A : Type} [NormedAddCommGroup A] [NormedSpace ℂ A]
variable (f : TracePrimitiveFamily A)

def radicand (t : ℂ × A) : ℂ := f.trace t ^ 2 - 4

theorem analytic_radicand : AnalyticOnNhd ℂ f.radicand univ :=
  (f.analytic_trace.pow 2).sub analyticOnNhd_const

def freeRoot (z : ℂ) : ℂ := 2*sinh (f.freePrimitive z)

theorem analytic_freeRoot : AnalyticOnNhd ℂ f.freeRoot f.freeDomain := by
  intro z hz
  exact analyticAt_const.mul (Complex.analyticAt_sinh.comp (f.analytic_freePrimitive z hz))

theorem freeRoot_sq (z : ℂ) : f.freeRoot z ^ 2 = f.radicand (z,0) := by
  dsimp only [radicand]
  rw [← f.free_trace]
  dsimp only [freeRoot]
  linear_combination -4*cosh_sq_sub_sinh_sq (f.freePrimitive z)

theorem exp_freePrimitive (z : ℂ) :
    exp (f.freePrimitive z) = (f.trace (z,0)+f.freeRoot z)/2 := by
  rw [← f.free_trace]
  dsimp only [freeRoot]
  rw [← cosh_add_sinh]
  ring

def rootDomain : Set (ℂ × A) := {t | t.1 ∈ f.freeDomain ∧ f.radicand t ≠ 0}

theorem isOpen_rootDomain : IsOpen f.rootDomain :=
  (f.isOpen_freeDomain.preimage continuous_fst).inter
    (isOpen_ne_fun f.analytic_radicand.continuous continuous_const)

def continuationDomain : Set (ℂ × A) := sourceSegmentDomain 0 f.rootDomain

theorem isOpen_continuationDomain : IsOpen f.continuationDomain :=
  isOpen_sourceSegmentDomain 0 _ f.isOpen_rootDomain

theorem continuationDomain_subset : f.continuationDomain ⊆ f.rootDomain :=
  sourceSegmentDomain_end 0 _

theorem continuationDomain_segment (t : ℂ × A) (ht : t ∈ f.continuationDomain)
    (s : ℝ) (hs : s ∈ Icc (0 : ℝ) 1) :
    sourceSegmentMap 0 ((s : ℂ),t) ∈ f.continuationDomain := by
  intro r hr
  have hrs : r*s ∈ Icc (0 : ℝ) 1 :=
    ⟨mul_nonneg hr.1 hs.1, mul_le_one₀ hr.2 hs.1 hs.2⟩
  simpa only [sourceSegmentMap,zero_add,sub_zero,smul_smul,← ofReal_mul] using ht (r*s) hrs

theorem continuationDomain_idempotent :
    sourceSegmentDomain 0 f.continuationDomain = f.continuationDomain := by
  apply Subset.antisymm (sourceSegmentDomain_end 0 _)
  intro t ht s hs
  exact f.continuationDomain_segment t ht s hs

def root (t : ℂ × A) : ℂ :=
  f.freeRoot t.1 * exp (parametricSourceLogIncrement f.radicand 0 t / 2)

theorem analytic_root : AnalyticOnNhd ℂ f.root f.continuationDomain := by
  intro t ht
  have hroot := (f.analytic_freeRoot t.1 (f.continuationDomain_subset ht).1).comp
    (f := fun t : ℂ × A => t.1) analyticAt_fst
  have hlog := analyticOnNhd_parametricSourceLogIncrement_segmentDomain f.radicand 0
    f.rootDomain f.isOpen_rootDomain (f.analytic_radicand.mono (subset_univ _))
    (fun _ h => h.2) t ht
  exact hroot.mul ((hlog.div_const).cexp)

@[simp] theorem root_base (z : ℂ) : f.root (z,0) = f.freeRoot z := by
  simp [root]

theorem root_sq (t : ℂ × A) (ht : t ∈ f.continuationDomain) :
    f.root t ^ 2 = f.radicand t := by
  have he : exp (parametricSourceLogIncrement f.radicand 0 t / 2)^2 =
      exp (parametricSourceLogIncrement f.radicand 0 t) := by
    rw [pow_two,← exp_add]
    congr 1
    ring
  rw [root,mul_pow,he,f.freeRoot_sq,mul_comm]
  exact exp_parametricSourceLogIncrement_mul_of_segment f.radicand f.rootDomain 0
    (f.analytic_radicand.mono (subset_univ _)) (fun _ h => h.2) t ht

theorem root_ne_zero (t : ℂ × A) (ht : t ∈ f.continuationDomain) : f.root t ≠ 0 := by
  intro hz
  apply (f.continuationDomain_subset ht).2
  rw [← f.root_sq t ht,hz]
  norm_num

def multiplier (t : ℂ × A) : ℂ := (f.trace t+f.root t)/2

theorem analytic_multiplier : AnalyticOnNhd ℂ f.multiplier f.continuationDomain :=
  ((f.analytic_trace.mono (subset_univ _)).add f.analytic_root).div_const

theorem multiplier_product (t : ℂ × A) (ht : t ∈ f.continuationDomain) :
    f.multiplier t * ((f.trace t-f.root t)/2) = 1 := by
  have h := f.root_sq t ht
  dsimp only [radicand] at h
  dsimp only [multiplier]
  linear_combination -h/4

theorem multiplier_ne_zero (t : ℂ × A) (ht : t ∈ f.continuationDomain) :
    f.multiplier t ≠ 0 := by
  intro hz
  have h := f.multiplier_product t ht
  rw [hz,zero_mul] at h
  exact zero_ne_one h

def primitive : ℂ × A → ℂ :=
  parametricSourceLogExtension f.multiplier 0 f.freePrimitive

theorem analytic_primitive : AnalyticOnNhd ℂ f.primitive f.continuationDomain := by
  rw [← f.continuationDomain_idempotent]
  apply analyticOnNhd_parametricSourceLogExtension _ _ _ _
    f.isOpen_continuationDomain f.analytic_multiplier f.multiplier_ne_zero
  intro z hz
  exact f.analytic_freePrimitive z (f.continuationDomain_subset hz).1

@[simp] theorem primitive_base (z : ℂ) : f.primitive (z,0) = f.freePrimitive z :=
  parametricSourceLogExtension_base _ _ _ _

theorem exp_primitive (t : ℂ × A) (ht : t ∈ f.continuationDomain) :
    exp (f.primitive t) = f.multiplier t := by
  apply exp_parametricSourceLogExtension _ _ _ f.continuationDomain
    f.analytic_multiplier f.multiplier_ne_zero (fun z _ => ?_) t
    (by rwa [f.continuationDomain_idempotent])
  simpa only [multiplier,f.root_base] using f.exp_freePrimitive z

theorem primitive_trace (t : ℂ × A) (ht : t ∈ f.continuationDomain) :
    2*cosh (f.primitive t) = f.trace t ∧ 2*sinh (f.primitive t) = f.root t := by
  have he := f.exp_primitive t ht
  have hneg : exp (-f.primitive t) = (f.trace t-f.root t)/2 := by
    apply mul_left_cancel₀ (exp_ne_zero (f.primitive t))
    rw [← exp_add,add_neg_cancel,exp_zero,he,f.multiplier_product t ht]
  constructor
  · rw [cosh,he,hneg]
    dsimp only [multiplier]
    ring
  · rw [sinh,he,hneg]
    dsimp only [multiplier]
    ring

theorem hasFDerivAt_primitive (t : ℂ × A) (ht : t ∈ f.continuationDomain) :
    HasFDerivAt f.primitive ((f.root t)⁻¹ • fderiv ℂ f.trace t) t := by
  have hF := f.analytic_primitive t ht
  have he : (fun a => 2*cosh (f.primitive a)) =ᶠ[𝓝 t] f.trace := by
    filter_upwards [f.isOpen_continuationDomain.mem_nhds ht] with a ha
    exact (f.primitive_trace a ha).1
  have hd := (((hF.differentiableAt.hasFDerivAt.ccosh).const_smul (2 : ℂ)).congr_of_eventuallyEq he.symm).fderiv
  rw [smul_smul,(f.primitive_trace t ht).2] at hd
  have hc : (f.root t)⁻¹ • fderiv ℂ f.trace t = fderiv ℂ f.primitive t := by
    rw [hd,smul_smul,inv_mul_cancel₀ (f.root_ne_zero t ht),one_smul]
  rw [hc]
  exact hF.differentiableAt.hasFDerivAt

theorem hasDerivAt_primitive (t : ℂ × A) (ht : t ∈ f.continuationDomain) :
    HasDerivAt (fun z => f.primitive (z,t.2))
      (deriv (fun z => f.trace (z,t.2)) t.1 / f.root t) t.1 := by
  have hFa : AnalyticAt ℂ (fun z => f.primitive (z,t.2)) t.1 :=
    (f.analytic_primitive t ht).comp
    (f := fun z : ℂ => (z,t.2)) (analyticAt_id.prod analyticAt_const)
  have hdF := hFa.differentiableAt.hasDerivAt
  have hc := ((Complex.hasDerivAt_cosh (f.primitive t)).comp t.1 hdF).const_mul 2
  have hmap : Continuous (fun z : ℂ => (z,t.2)) := continuous_id.prodMk continuous_const
  have he : (fun z => f.trace (z,t.2)) =ᶠ[𝓝 t.1]
      (fun z => 2*cosh (f.primitive (z,t.2))) := by
    filter_upwards [hmap.continuousAt.preimage_mem_nhds
      (f.isOpen_continuationDomain.mem_nhds ht)] with z hz
    exact (f.primitive_trace (z,t.2) hz).1.symm
  have hd := (hc.congr_of_eventuallyEq he).deriv
  have hderiv : deriv (fun z => f.primitive (z,t.2)) t.1 =
      deriv (fun z => f.trace (z,t.2)) t.1 / f.root t := by
    apply (eq_div_iff (f.root_ne_zero t ht)).mpr
    rw [hd,← (f.primitive_trace t ht).2]
    ring
  rwa [hderiv] at hdF

theorem primitive_unique (F : ℂ × A → ℂ) (S : Set (ℂ × A)) (hS : IsPreconnected S)
    (hsub : S ⊆ f.continuationDomain) (hF : ContinuousOn F S)
    (hcosh : ∀ t ∈ S, 2*cosh (F t) = f.trace t)
    (hsinh : ∀ t ∈ S, 2*sinh (F t) = f.root t)
    (z : ℂ) (hz : (z,0) ∈ S) (hbase : F (z,0) = f.freePrimitive z) :
    EqOn F f.primitive S := by
  apply continuousLogarithms_eqOn F f.primitive S hS hF
    (f.analytic_primitive.continuousOn.mono hsub) _ (z,0) hz
    (by simpa only [f.primitive_base] using hbase)
  intro t ht
  rw [f.exp_primitive t (hsub ht),← cosh_add_sinh,
    multiplier,← hcosh t ht,← hsinh t ht]
  ring

theorem exists_continuation_neighborhood (K : Set ℂ) (hK : IsCompact K) (q : A)
    (hKq : ∀ z ∈ K, (z,q) ∈ f.continuationDomain) :
    ∃ V : Set A, IsOpen V ∧ q ∈ V ∧ K ×ˢ V ⊆ f.continuationDomain := by
  have hsub : K ×ˢ {q} ⊆ f.continuationDomain := by
    rintro ⟨z,a⟩ ⟨hz,ha⟩
    obtain rfl := mem_singleton_iff.mp ha
    exact hKq z hz
  obtain ⟨U,V,_,hV,hKU,hqV,hUV⟩ := generalized_tube_lemma hK isCompact_singleton
    f.isOpen_continuationDomain hsub
  exact ⟨V,hV,hqV (mem_singleton q),fun t ht => hUV ⟨hKU ht.1,ht.2⟩⟩

end TracePrimitiveFamily
end NLS.ComplexAnalysis
