import NLS.ZakharovShabat.L2WholeLinePeriodAbsoluteContinuity
import NLS.ZakharovShabat.L2WholeLineODEIntegrability
import NLS.FunctionalAnalysis.ComplexAbsoluteContinuity

/-! # The original integral equation and absolute continuity on the whole line

The closed-period fundamental theorem assembles through all positive and
negative integer seams. The resulting single Volterra identity proves
absolute continuity on every compact interval of the real line.
-/
noncomputable section
set_option autoImplicit false
open Set MeasureTheory Filter
open NLS.FunctionalAnalysis
namespace NLS.ZakharovShabat

/-- The original physical right-hand side integrates to the solution
increment on each positive or negative closed integer period. -/
theorem l2WholeLineSolution_period_integral (u : IntervalPairL2) (z : ℂ)
    (v : Fin 2 → ℂ) (n : ℤ) (s : Icc (0 : ℝ) 1) :
    (∫ t in (n : ℝ)..s.val+n, classicalODECoefficient (l2WholeLinePotential u t) z
      (l2WholeLineSolution u z v t)) =
      l2WholeLineSolution u z v (s.val+n)-l2WholeLineSolution u z v n := by
  have hac : AbsolutelyContinuousOnInterval (fun t : ℝ => l2WholeLineSolution u z v (t+n)) 0 s.val :=
    (absolutelyContinuousOnInterval_l2WholeLineSolution_period u z v n).mono
      (uIcc_subset_uIcc (by simp) (by simp))
  have hi : IntervalIntegrable (fun t : ℝ => classicalODECoefficient
      (l2WholeLinePotential u (t+n)) z (l2WholeLineSolution u z v (t+n))) volume 0 s.val := by
    rw [IntervalIntegrable.comp_add_right_iff
      (f := fun t => classicalODECoefficient (l2WholeLinePotential u t) z (l2WholeLineSolution u z v t))
      (a := 0) (b := s.val) (c := (n : ℝ)) (by finiteness)]
    simpa only [zero_add] using intervalIntegrable_l2WholeLineODE u z v (n : ℝ) (s.val+n)
  have hd : ∀ᵐ t : ℝ, t ∈ uIcc 0 s.val →
      HasDerivAt (fun x : ℝ => l2WholeLineSolution u z v (x+n))
        (classicalODECoefficient (l2WholeLinePotential u (t+n)) z
          (l2WholeLineSolution u z v (t+n))) t := by
    have h := (measurePreserving_add_right volume (n : ℝ)).quasiMeasurePreserving.ae
      (ae_hasDerivAt_l2WholeLineSolution u z v)
    filter_upwards [h] with t ht
    intro _
    exact ht.comp_add_const t (n : ℝ)
  have h := integral_eq_sub_of_ac_of_ae_hasDerivAt hac hi hd
  have he := intervalIntegral.integral_comp_add_right (a := (0 : ℝ)) (b := s.val)
    (fun t => classicalODECoefficient (l2WholeLinePotential u t) z
      (l2WholeLineSolution u z v t)) (n : ℝ)
  simpa only [zero_add] using he.symm.trans h

private theorem constant_of_closed_periods {E : Type*} (f : ℝ → E)
    (hf : ∀ n : ℤ, ∀ s : Icc (0 : ℝ) 1, f (s.val+n) = f n) (t : ℝ) : f t = f 0 := by
  have hn (n : ℤ) : f (n : ℝ) = f 0 := by
    induction n using Int.induction_on with
    | zero => simp
    | succ n ih =>
      simpa only [Int.cast_add,Int.cast_one,add_comm] using
        (hf n ⟨1,by constructor <;> norm_num⟩).trans ih
    | pred n ih =>
      have he := hf (-(n : ℤ)-1) ⟨1,by constructor <;> norm_num⟩
      have hh : (1 : ℝ)+(↑(-(n : ℤ)-1) : ℝ) = -(n : ℝ) := by push_cast; ring
      rw [hh] at he
      exact he.symm.trans (by simpa only [Int.cast_neg,Int.cast_natCast] using ih)
  have h := hf ⌊t⌋ ⟨Int.fract t,Int.fract_nonneg t,(Int.fract_lt_one t).le⟩
  simpa only [Int.fract_add_floor] using h.trans (hn ⌊t⌋)

/-- The actual continuation satisfies one Volterra identity for every
real time, including negative times and all integer seams. -/
theorem l2WholeLineSolution_eq_integral (u : IntervalPairL2) (z : ℂ)
    (v : Fin 2 → ℂ) (t : ℝ) :
    l2WholeLineSolution u z v t = (v 0,v 1)+
      ∫ s in (0 : ℝ)..t, classicalODECoefficient (l2WholeLinePotential u s) z
        (l2WholeLineSolution u z v s) := by
  let G : ℝ → ℂ × ℂ := fun s => classicalODECoefficient (l2WholeLinePotential u s) z
    (l2WholeLineSolution u z v s)
  have h := constant_of_closed_periods (fun t => l2WholeLineSolution u z v t-∫ s in (0 : ℝ)..t, G s)
    (fun n s => ?_) t
  · simpa only [intervalIntegral.integral_same,sub_zero,l2WholeLineSolution_zero,
      sub_eq_iff_eq_add] using h
  · have hs := intervalIntegral.integral_add_adjacent_intervals
      (intervalIntegrable_l2WholeLineODE u z v 0 n)
      (intervalIntegrable_l2WholeLineODE u z v n (s.val+n))
    change l2WholeLineSolution u z v (s.val+n)-(∫ s in (0 : ℝ)..s.val+n, G s) = _
    change (∫ s in (0 : ℝ)..n, G s)+(∫ r in (n : ℝ)..s.val+n, G r) =
      ∫ r in (0 : ℝ)..s.val+n, G r at hs
    rw [← hs]
    have hp := l2WholeLineSolution_period_integral u z v n s
    change (∫ r in (n : ℝ)..s.val+n, G r) = _ at hp
    rw [hp]
    abel

/-- The same physical integral identity holds between any two real times. -/
theorem l2WholeLineSolution_eq_integral_between (u : IntervalPairL2) (z : ℂ)
    (v : Fin 2 → ℂ) (a b : ℝ) :
    l2WholeLineSolution u z v b = l2WholeLineSolution u z v a+
      ∫ t in a..b, classicalODECoefficient (l2WholeLinePotential u t) z
        (l2WholeLineSolution u z v t) := by
  rw [l2WholeLineSolution_eq_integral u z v b,l2WholeLineSolution_eq_integral u z v a,
    ← intervalIntegral.integral_add_adjacent_intervals
      (intervalIntegrable_l2WholeLineODE u z v 0 a) (intervalIntegrable_l2WholeLineODE u z v a b)]
  abel

/-- The actual physical solution is absolutely continuous on every
compact real interval, including intervals that cross integer seams. -/
theorem absolutelyContinuousOnInterval_l2WholeLineSolution
    (u : IntervalPairL2) (z : ℂ) (v : Fin 2 → ℂ) (a b : ℝ) :
    AbsolutelyContinuousOnInterval (l2WholeLineSolution u z v) a b := by
  have ha := absolutelyContinuousOnInterval_const_add
    (absolutelyContinuousOnInterval_integral (intervalIntegrable_l2WholeLineODE u z v a b)
      (c := a) (by simp)) (l2WholeLineSolution u z v a)
  apply absolutelyContinuousOnInterval_congr ha
  intro t _
  exact (l2WholeLineSolution_eq_integral_between u z v a t).symm

end NLS.ZakharovShabat
