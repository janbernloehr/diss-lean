import NLS.KdV.ClassicalHillGreen
import NLS.ComplexAnalysis.ScalarSineDuhamel

noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology MeasureTheory
open NLS.ComplexAnalysis NLS.LinearVolterra NLS.FunctionalAnalysis NLS.ZakharovShabat
open scoped ENNReal

namespace NLS.KdV



theorem classicalHillFlow_sine_duhamel (q : Curve ℂ) (z : ℂ) (hz : z ≠ 0) (v : ℂ × ℂ)
    (t : Icc (0 : ℝ) 1) :
    (classicalHillFlow q (z^2) v t).1 = cos (z*t.val)*v.1 + sin (z*t.val)/z*v.2 +
      ∫ s in (0 : ℝ)..t.val, sin (z*((t.val-s : ℝ) : ℂ))/z*extend q s*
        (classicalHillFlow q (z^2) v s).1 := by
  have hc := continuous_classicalHillFlow q (z^2) v
  have h := scalar_sine_duhamel (extend q) (fun s => (classicalHillFlow q (z^2) v s).1)
    (fun s => (classicalHillFlow q (z^2) v s).2) z hz t.val t.property.1
    (continuous_extend q) hc.fst hc.snd ?_ ?_
  · simpa only [classicalHillFlow_zero] using h
  · intro s hs
    have hs' : s ∈ Icc (0 : ℝ) 1 := ⟨hs.1,hs.2.trans t.property.2⟩
    simpa using! HasFDerivAt.hasDerivAt
      (hasDerivAt_classicalHillFlow q (z^2) v ⟨s,hs'⟩).fst
  · intro s hs
    have hs' : s ∈ Icc (0 : ℝ) 1 := ⟨hs.1,hs.2.trans t.property.2⟩
    simpa [NLS.LinearVolterra.extend,projIcc_of_mem _ hs'] using!
      HasFDerivAt.hasDerivAt (hasDerivAt_classicalHillFlow q (z^2) v ⟨s,hs'⟩).snd

theorem classicalHillFlow_cosine_duhamel (q : Curve ℂ) (z : ℂ) (v : ℂ × ℂ)
    (t : Icc (0 : ℝ) 1) :
    (classicalHillFlow q (z^2) v t).2 = -z*sin (z*t.val)*v.1 + cos (z*t.val)*v.2 +
      ∫ s in (0 : ℝ)..t.val, cos (z*((t.val-s : ℝ) : ℂ))*extend q s*
        (classicalHillFlow q (z^2) v s).1 := by
  have hc := continuous_classicalHillFlow q (z^2) v
  have h := scalar_cosine_duhamel (extend q) (fun s => (classicalHillFlow q (z^2) v s).1)
    (fun s => (classicalHillFlow q (z^2) v s).2) z t.val t.property.1
    (continuous_extend q) hc.fst hc.snd ?_ ?_
  · simpa only [classicalHillFlow_zero] using h
  · intro s hs
    have hs' : s ∈ Icc (0 : ℝ) 1 := ⟨hs.1,hs.2.trans t.property.2⟩
    simpa using! HasFDerivAt.hasDerivAt
      (hasDerivAt_classicalHillFlow q (z^2) v ⟨s,hs'⟩).fst
  · intro s hs
    have hs' : s ∈ Icc (0 : ℝ) 1 := ⟨hs.1,hs.2.trans t.property.2⟩
    simpa [NLS.LinearVolterra.extend,projIcc_of_mem _ hs'] using!
      HasFDerivAt.hasDerivAt (hasDerivAt_classicalHillFlow q (z^2) v ⟨s,hs'⟩).snd

end NLS.KdV
