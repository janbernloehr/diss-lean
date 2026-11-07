import NLS.FunctionalAnalysis.ComplexAbsoluteContinuity
import NLS.FunctionalAnalysis.LinearVolterra
import Mathlib.MeasureTheory.Integral.IntervalIntegral.LebesgueDifferentiationThm

/-! # Integral equations for absolutely continuous interval curves -/
noncomputable section
open Set MeasureTheory Filter Topology
namespace NLS.FunctionalAnalysis
open NLS.LinearVolterra
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

/-- A genuine AC curve with a specified integrable weak derivative satisfies
the full initial-value integral equation, including both endpoints. -/
theorem curve_eq_initial_add_integral_of_ac (w : Curve E) (g : ℝ → E)
    (hw : AbsolutelyContinuousOnInterval (extend w) 0 1)
    (hg : IntervalIntegrable g volume 0 1)
    (hd : ∀ᵐ x ∂volume.restrict (Ioc (0:ℝ) 1), HasDerivAt (extend w) (g x) x)
    (t : Icc (0:ℝ) 1) :
    w t = w ⟨0,by constructor <;> norm_num⟩+∫ x in (0:ℝ)..t.val, g x := by
  have hs : uIcc (0:ℝ) t.val ⊆ Icc (0:ℝ) 1 := by
    rw [uIcc_of_le t.property.1]
    exact Icc_subset_Icc le_rfl t.property.2
  have hglobal : ∀ᵐ x : ℝ, x ∈ uIcc (0:ℝ) t.val → HasDerivAt (extend w) (g x) x := by
    rw [ae_restrict_iff' measurableSet_Ioc] at hd
    filter_upwards [hd, (show ∀ᵐ x : ℝ, x ≠ (0:ℝ) by simp [ae_iff])] with x hx hx0
    intro hxt
    have hx1 := hs hxt
    exact hx ⟨lt_of_le_of_ne hx1.1 (Ne.symm hx0), hx1.2⟩
  have hi := integral_eq_sub_of_ac_of_ae_hasDerivAt
    (hw.mono (by simpa using hs)) (hg.mono_set (by simpa only [uIcc_of_le (by norm_num : (0:ℝ) ≤ 1)] using hs)) hglobal
  rw [hi, extend_coe w t, extend_coe w ⟨0,by constructor <;> norm_num⟩]
  abel

/-- An actual integral equation with an integrable right-hand side supplies
both absolute continuity and the specified weak derivative. -/
theorem curve_integral_regularity (w : Curve E) (c : E) (g : ℝ → E)
    (hg : IntervalIntegrable g volume 0 1)
    (he : ∀ t : Icc (0:ℝ) 1, w t = c+∫ x in (0:ℝ)..t.val, g x) :
    AbsolutelyContinuousOnInterval (extend w) 0 1 ∧
      ∀ᵐ x ∂volume.restrict (Ioc (0:ℝ) 1), HasDerivAt (extend w) (g x) x := by
  constructor
  · have ha := absolutelyContinuousOnInterval_const_add
      (absolutelyContinuousOnInterval_integral hg (by simp : (0:ℝ) ∈ uIcc 0 1)) c
    apply absolutelyContinuousOnInterval_congr ha
    intro t ht
    have ht' : t ∈ Icc (0:ℝ) 1 := by simpa using ht
    simpa only [NLS.LinearVolterra.extend, projIcc_of_mem _ ht'] using (he ⟨t,ht'⟩).symm
  · rw [ae_restrict_iff' measurableSet_Ioc]
    have hn : ∀ᵐ x : ℝ ∂volume, x ≠ 1 := by simp [ae_iff]
    filter_upwards [hg.ae_hasDerivAt_integral, hn] with x hx hn hmem
    have hx' : x ∈ Ioo (0:ℝ) 1 := ⟨hmem.1, lt_of_le_of_ne hmem.2 hn⟩
    have hd := (hx (by simpa only [uIcc_of_le (show (0:ℝ) ≤ 1 by norm_num)] using
      Ioc_subset_Icc_self hmem) 0 (by simp)).const_add c
    apply hd.congr_of_eventuallyEq
    filter_upwards [Ioo_mem_nhds hx'.1 hx'.2] with y hy
    have hy' : y ∈ Icc (0:ℝ) 1 := Ioo_subset_Icc_self hy
    simpa only [NLS.LinearVolterra.extend, projIcc_of_mem _ hy'] using he ⟨y,hy'⟩

end NLS.FunctionalAnalysis
