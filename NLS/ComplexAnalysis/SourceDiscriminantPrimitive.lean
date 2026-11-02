import NLS.ComplexAnalysis.ParametricSourceLogDomain
import Mathlib.Analysis.SpecialFunctions.Complex.Analytic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp

/-! # Free-normalized source continuation for an analytic discriminant

The construction depends only on an actual analytic discriminant and its
free trace. Two logarithmic source integrals construct the root and then
the primitive. The source is an arbitrary complex Banach space.
-/
noncomputable section
open Set Complex Filter Topology
namespace NLS.ComplexAnalysis
variable (A : Type) [NormedAddCommGroup A] [NormedSpace ℂ A]

structure SourceDiscriminantData where
  discriminant : ℂ × A → ℂ
  energyDomain : Set ℂ
  freePrimitive : ℂ → ℂ
  energyDomain_open : IsOpen energyDomain
  discriminant_analytic : AnalyticOnNhd ℂ discriminant univ
  freePrimitive_analytic : AnalyticOnNhd ℂ freePrimitive energyDomain
  free_trace : ∀ z ∈ energyDomain, 2*cosh (freePrimitive z) = discriminant (z,0)

namespace SourceDiscriminantData
variable {A} (D : SourceDiscriminantData A)

def radicand (t : ℂ × A) : ℂ := D.discriminant t ^ 2-4
def rootDomain : Set (ℂ × A) := {t | t.1 ∈ D.energyDomain ∧ D.radicand t ≠ 0}
def continuationDomain : Set (ℂ × A) := sourceSegmentDomain 0 D.rootDomain
def freeRoot (z : ℂ) : ℂ := 2*sinh (D.freePrimitive z)
def root (t : ℂ × A) : ℂ :=
  D.freeRoot t.1 * exp (parametricSourceLogIncrement D.radicand 0 t / 2)
def multiplier (t : ℂ × A) : ℂ := (D.discriminant t+D.root t)/2
def primitive : ℂ × A → ℂ :=
  parametricSourceLogExtension D.multiplier 0 D.freePrimitive

theorem radicand_analytic : AnalyticOnNhd ℂ D.radicand univ :=
  (D.discriminant_analytic.pow 2).sub analyticOnNhd_const

theorem rootDomain_open : IsOpen D.rootDomain :=
  (D.energyDomain_open.preimage continuous_fst).inter
    (isOpen_ne_fun D.radicand_analytic.continuous continuous_const)

theorem continuationDomain_open : IsOpen D.continuationDomain :=
  isOpen_sourceSegmentDomain 0 _ D.rootDomain_open

theorem continuationDomain_subset : D.continuationDomain ⊆ D.rootDomain :=
  sourceSegmentDomain_end 0 _

theorem continuationDomain_segment (t : ℂ × A) (ht : t ∈ D.continuationDomain)
    (s : ℝ) (hs : s ∈ Icc (0 : ℝ) 1) :
    sourceSegmentMap 0 ((s : ℂ),t) ∈ D.continuationDomain := by
  intro r hr
  have hrs : r*s ∈ Icc (0 : ℝ) 1 :=
    ⟨mul_nonneg hr.1 hs.1,mul_le_one₀ hr.2 hs.1 hs.2⟩
  simpa only [sourceSegmentMap,zero_add,sub_zero,smul_smul,← ofReal_mul] using ht (r*s) hrs

theorem continuationDomain_idempotent :
    sourceSegmentDomain 0 D.continuationDomain = D.continuationDomain := by
  apply Subset.antisymm (sourceSegmentDomain_end 0 _)
  intro t ht s hs
  exact D.continuationDomain_segment t ht s hs

theorem freeRoot_analytic : AnalyticOnNhd ℂ D.freeRoot D.energyDomain := by
  intro z hz
  exact analyticAt_const.mul (Complex.analyticAt_sinh.comp (D.freePrimitive_analytic z hz))

theorem freeRoot_sq (z : ℂ) (hz : z ∈ D.energyDomain) :
    D.freeRoot z ^ 2 = D.radicand (z,0) := by
  dsimp only [radicand]
  rw [← D.free_trace z hz]
  dsimp only [freeRoot]
  linear_combination -4*cosh_sq_sub_sinh_sq (D.freePrimitive z)

theorem root_analytic : AnalyticOnNhd ℂ D.root D.continuationDomain := by
  intro t ht
  have hfree := (D.freeRoot_analytic t.1 (D.continuationDomain_subset ht).1).comp
    (f := Prod.fst) analyticAt_fst
  have hlog := analyticOnNhd_parametricSourceLogIncrement_segmentDomain D.radicand 0
    D.rootDomain D.rootDomain_open (D.radicand_analytic.mono (subset_univ _))
    (fun _ h => h.2) t ht
  exact hfree.mul ((hlog.div_const).cexp)

@[simp] theorem root_base (z : ℂ) : D.root (z,0) = D.freeRoot z := by simp [root]

theorem root_sq (t : ℂ × A) (ht : t ∈ D.continuationDomain) :
    D.root t ^ 2 = D.radicand t := by
  have he : exp (parametricSourceLogIncrement D.radicand 0 t / 2)^2 =
      exp (parametricSourceLogIncrement D.radicand 0 t) := by
    rw [pow_two,← exp_add]
    congr 1
    ring
  rw [root,mul_pow,he,D.freeRoot_sq t.1 (D.continuationDomain_subset ht).1,mul_comm]
  exact exp_parametricSourceLogIncrement_mul_of_segment D.radicand D.rootDomain 0
    (D.radicand_analytic.mono (subset_univ _)) (fun _ h => h.2) t ht

theorem root_ne_zero (t : ℂ × A) (ht : t ∈ D.continuationDomain) : D.root t ≠ 0 := by
  intro hz
  apply (D.continuationDomain_subset ht).2
  rw [← D.root_sq t ht,hz]
  norm_num

theorem multiplier_analytic : AnalyticOnNhd ℂ D.multiplier D.continuationDomain :=
  ((D.discriminant_analytic.mono (subset_univ _)).add D.root_analytic).div_const

theorem multiplier_product (t : ℂ × A) (ht : t ∈ D.continuationDomain) :
    D.multiplier t * ((D.discriminant t-D.root t)/2) = 1 := by
  have h := D.root_sq t ht
  dsimp only [radicand] at h
  dsimp only [multiplier]
  linear_combination -h/4

theorem multiplier_ne_zero (t : ℂ × A) (ht : t ∈ D.continuationDomain) :
    D.multiplier t ≠ 0 := by
  intro hz
  have h := D.multiplier_product t ht
  rw [hz,zero_mul] at h
  exact zero_ne_one h

theorem primitive_analytic : AnalyticOnNhd ℂ D.primitive D.continuationDomain := by
  rw [← D.continuationDomain_idempotent]
  apply analyticOnNhd_parametricSourceLogExtension _ _ _ _
    D.continuationDomain_open D.multiplier_analytic D.multiplier_ne_zero
  intro z hz
  exact D.freePrimitive_analytic z (D.continuationDomain_subset hz).1

@[simp] theorem primitive_base (z : ℂ) : D.primitive (z,0) = D.freePrimitive z :=
  parametricSourceLogExtension_base _ _ _ _

theorem exp_primitive (t : ℂ × A) (ht : t ∈ D.continuationDomain) :
    exp (D.primitive t) = D.multiplier t := by
  apply exp_parametricSourceLogExtension _ _ _ D.continuationDomain
    D.multiplier_analytic D.multiplier_ne_zero (fun z hz => ?_) t
    (by rwa [D.continuationDomain_idempotent])
  dsimp only [multiplier]
  rw [D.root_base,← D.free_trace z (D.continuationDomain_subset hz).1]
  dsimp only [freeRoot]
  rw [← cosh_add_sinh]
  ring

theorem primitive_trace (t : ℂ × A) (ht : t ∈ D.continuationDomain) :
    2*cosh (D.primitive t) = D.discriminant t ∧
      2*sinh (D.primitive t) = D.root t := by
  have he := D.exp_primitive t ht
  have hneg : exp (-D.primitive t) = (D.discriminant t-D.root t)/2 := by
    apply mul_left_cancel₀ (exp_ne_zero (D.primitive t))
    rw [← exp_add,add_neg_cancel,exp_zero,he,D.multiplier_product t ht]
  constructor
  · rw [cosh,he,hneg]
    dsimp only [multiplier]
    ring
  · rw [sinh,he,hneg]
    dsimp only [multiplier]
    ring

theorem primitive_hasFDerivAt (t : ℂ × A) (ht : t ∈ D.continuationDomain) :
    HasFDerivAt D.primitive ((D.root t)⁻¹ • fderiv ℂ D.discriminant t) t := by
  have hF := D.primitive_analytic t ht
  have he : (fun a => 2*cosh (D.primitive a)) =ᶠ[𝓝 t] D.discriminant := by
    filter_upwards [D.continuationDomain_open.mem_nhds ht] with a ha
    exact (D.primitive_trace a ha).1
  have hd := (((hF.differentiableAt.hasFDerivAt.ccosh).const_smul (2 : ℂ)).congr_of_eventuallyEq he.symm).fderiv
  rw [smul_smul,(D.primitive_trace t ht).2] at hd
  have hc : (D.root t)⁻¹ • fderiv ℂ D.discriminant t = fderiv ℂ D.primitive t := by
    rw [hd,smul_smul,inv_mul_cancel₀ (D.root_ne_zero t ht),one_smul]
  rw [hc]
  exact hF.differentiableAt.hasFDerivAt

end SourceDiscriminantData
end NLS.ComplexAnalysis
