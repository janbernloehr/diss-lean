import NLS.KdV.HillHminusOneMiuraEnergyPeriods
import NLS.ZakharovShabat.EvenPositivePeriodCircle
import Mathlib.Analysis.Complex.SqrtDeriv

/-! # Actual Hill energy roots on rough Miura charts

The actual NLS canonical product, evaluated at the principal shifted
frequency, is a nonvanishing analytic square root of the independently
glued rough Hill radicand. Its domain and its exact value on positive
frequency discs are proved, rather than a sign or root being assumed.
-/
noncomputable section
open Set Metric Complex
open NLS.ComplexAnalysis NLS.ZakharovShabat
namespace NLS.KdV

theorem square_mem_slitPlane_of_re_pos (z : ℂ) (hz : 0 < z.re) : z^2 ∈ slitPlane := by
  rw [mem_slitPlane_iff]
  by_cases hi : z.im = 0
  · left
    simp only [pow_two,mul_re,hi,mul_zero,sub_zero]
    positivity
  · right
    have he : (z^2).im = (2*z.re)*z.im := by simp only [pow_two,mul_im];ring
    rw [he]
    exact mul_ne_zero (by positivity) hi

namespace HillHminusMiuraChart

def energyRoot (C : HillHminusMiuraChart) (q : PeriodOneHminusOne) (energy : ℂ) : ℂ :=
  sourceCanonicalRoot (by simp) (by norm_num) (C.criticalSource q) (sqrt (energy+C.energyShift))

def energyRootDomain (C : HillHminusMiuraChart) (q : PeriodOneHminusOne) : Set ℂ :=
  {energy | energy+C.energyShift ∈ slitPlane ∧
    sqrt (energy+C.energyShift) ∈ sourceCanonicalRootDomain (by simp) (by norm_num) (C.criticalSource q)}

def energyRootJointDomain (C : HillHminusMiuraChart) (V : Set PeriodOneHminusOne) :
    Set (ℂ × PeriodOneHminusOne) := {t | t.2 ∈ V ∧ t.1 ∈ C.energyRootDomain t.2}

theorem energyRoot_sq (C : HillHminusMiuraChart) (q : PeriodOneHminusOne) (hq : q ∈ C.domain)
    (energy : ℂ) (he : energy ∈ C.energyRootDomain q) :
    C.energyRoot q energy ^ 2 = hillHminusDiscriminant q energy ^ 2-4 := by
  rw [energyRoot,sourceCanonicalRoot_sq_eq_discriminant_sq_sub_four (by simp) (by norm_num)
    (C.criticalSource q) _ he.2]
  have ht := C.trace_shifted_square q hq (sqrt (energy+C.energyShift))
  rw [sq_sqrt,add_sub_cancel_right] at ht
  rw [← ht]

theorem energyRoot_ne_zero (C : HillHminusMiuraChart) (q : PeriodOneHminusOne)
    (energy : ℂ) (he : energy ∈ C.energyRootDomain q) : C.energyRoot q energy ≠ 0 :=
  sourceCanonicalRoot_ne_zero_off_gaps (by simp) (by norm_num) (C.criticalSource q) _ he.2

theorem energyRoot_shifted_square (C : HillHminusMiuraChart) (q : PeriodOneHminusOne)
    (z : ℂ) (hz : 0 < z.re) :
    C.energyRoot q (z^2-C.energyShift) =
      sourceCanonicalRoot (by simp) (by norm_num) (C.criticalSource q) z := by
  simp only [energyRoot,sub_add_cancel,sqrt_sq_of_re_pos z hz]

theorem shifted_square_mem_energyRootDomain (C : HillHminusMiuraChart) (q : PeriodOneHminusOne)
    (z : ℂ) (hz : 0 < z.re)
    (hroot : z ∈ sourceCanonicalRootDomain (by simp) (by norm_num) (C.criticalSource q)) :
    z^2-C.energyShift ∈ C.energyRootDomain q := by
  simp only [energyRootDomain,mem_ofPred_eq,sub_add_cancel,sqrt_sq_of_re_pos z hz]
  exact ⟨square_mem_slitPlane_of_re_pos z hz,hroot⟩

theorem energyRoot_joint (C : HillHminusMiuraChart)
    {W₀ W : Set (CoeffPair 2)} {s : (n : ℤ) → CoeffPair 2 → DeletedCoeff 2 n}
    (H : SourceTheorem12_1Data (by simp) (by norm_num) W₀ W s)
    {V : Set PeriodOneHminusOne} (hV : IsOpen V) (hVC : V ⊆ C.domain)
    (hVW : ∀ q ∈ V, C.criticalSource q ∈ W) :
    IsOpen (C.energyRootJointDomain V) ∧
      AnalyticOnNhd ℂ (fun t : ℂ × PeriodOneHminusOne => C.energyRoot t.2 t.1)
        (C.energyRootJointDomain V) := by
  have hroot := H.previous.previous.previous.criticalOffsets.previous.previous.joint
  let B : Set (ℂ × PeriodOneHminusOne) := {t | t.2 ∈ V ∧ t.1+C.energyShift ∈ slitPlane}
  let T : ℂ × PeriodOneHminusOne → ℂ × CoeffPair 2 :=
    fun t => (sqrt (t.1+C.energyShift),C.criticalSource t.2)
  have hBo : IsOpen B := (hV.preimage continuous_snd).inter
    (isOpen_slitPlane.preimage (continuous_fst.add continuous_const))
  have hsqrt : AnalyticOnNhd ℂ sqrt slitPlane := differentiableOn_sqrt.analyticOnNhd isOpen_slitPlane
  have hT : AnalyticOnNhd ℂ T B := by
    intro t ht
    have hs := (hsqrt (t.1+C.energyShift) ht.2).comp
      (f := fun t : ℂ × PeriodOneHminusOne => t.1+C.energyShift)
      (analyticAt_fst.add analyticAt_const)
    have hq := (C.analyticOnNhd_criticalSource t.2 (hVC ht.1)).comp
      (f := fun t : ℂ × PeriodOneHminusOne => t.2) analyticAt_snd
    exact hs.prod hq
  have heq : C.energyRootJointDomain V = B ∩
      T ⁻¹' sourceCanonicalRootJointDomain (by simp) (by norm_num) W₀ := by
    ext t
    constructor
    · intro ht
      exact ⟨⟨ht.1,ht.2.1⟩,H.subset (hVW t.2 ht.1),ht.2.2⟩
    · intro ht
      exact ⟨ht.1.1,ht.1.2,ht.2.2⟩
  refine ⟨?_,?_⟩
  · rw [heq]
    exact hT.continuousOn.isOpen_inter_preimage hBo hroot.1
  · intro t ht
    have ht' : t ∈ B ∩ T ⁻¹' sourceCanonicalRootJointDomain (by simp) (by norm_num) W₀ := heq ▸ ht
    exact (hroot.2 (T t) ht'.2).comp (f := T) (hT t ht'.1)

end HillHminusMiuraChart
end NLS.KdV
