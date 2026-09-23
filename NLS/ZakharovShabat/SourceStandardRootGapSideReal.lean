import NLS.ZakharovShabat.SourceStandardRootGapSideMidpoint
import Mathlib.Analysis.Complex.SqrtDeriv

/-!
# Complete real-gap boundary formula for the normalized standard root

For a positive real half-gap `d`, the limits from the two sides of
the segment `τ + d[-1,1]` are `∓i d √(1-t²)` at every `-1 ≤ t ≤ 1`.
The interior follows from the positive, negative, and midpoint branch
calculations. At the endpoints, the radicand vanishes and the principal
square root is continuous.
-/

noncomputable section
open Complex Filter
open scoped Topology

namespace NLS.ZakharovShabat

private theorem real_gap_upper_interior (τ : ℂ) (d t : ℝ)
    (hd : 0 < d) (htl : -1 < t) (htr : t < 1) :
    Tendsto (fun ε : ℝ =>
      normalizedStandardRoot τ ((2*(d:ℂ))^2)
        (τ+(d:ℂ)*((t:ℂ)+(ε:ℂ)*I)))
      (𝓝[>] (0:ℝ))
      (𝓝 (-(d:ℂ)*I*(Real.sqrt (1-t^2):ℂ))) := by
  rcases lt_trichotomy t 0 with htneg | htz | htpos
  · exact normalizedStandardRoot_tendsto_gap_upper_neg τ d t hd htl htneg
  · subst t
    simpa using normalizedStandardRoot_tendsto_gap_upper_zero τ d hd
  · exact normalizedStandardRoot_tendsto_gap_upper_pos τ d t hd htpos htr

private theorem real_gap_lower_interior (τ : ℂ) (d t : ℝ)
    (hd : 0 < d) (htl : -1 < t) (htr : t < 1) :
    Tendsto (fun ε : ℝ =>
      normalizedStandardRoot τ ((2*(d:ℂ))^2)
        (τ+(d:ℂ)*((t:ℂ)-(ε:ℂ)*I)))
      (𝓝[>] (0:ℝ))
      (𝓝 ((d:ℂ)*I*(Real.sqrt (1-t^2):ℂ))) := by
  rcases lt_trichotomy t 0 with htneg | htz | htpos
  · exact normalizedStandardRoot_tendsto_gap_lower_neg τ d t hd htl htneg
  · subst t
    convert normalizedStandardRoot_tendsto_gap_lower_zero τ d hd using 1
    · funext ε
      congr 1
      simp only [ofReal_zero]
      ring
    · norm_num
  · exact normalizedStandardRoot_tendsto_gap_lower_pos τ d t hd htpos htr

private theorem root_continuous_endpoint (τ : ℂ) (d t : ℝ)
    (hd : 0 < d) (htsq : t^2=1) :
    ContinuousAt (normalizedStandardRoot τ ((2*(d:ℂ))^2))
      (τ+(d:ℂ)*(t:ℂ)) := by
  let z0 : ℂ := τ+(d:ℂ)*(t:ℂ)
  let q : ℂ → ℂ := fun z => 1-(2*(d:ℂ))^2/(4*(τ-z)^2)
  have hdC : (d:ℂ) ≠ 0 := by exact_mod_cast ne_of_gt hd
  have htne : t ≠ 0 := by nlinarith [htsq]
  have htC : (t:ℂ) ≠ 0 := by exact_mod_cast htne
  have htc : (t:ℂ)^2=1 := by exact_mod_cast htsq
  have hdiff : τ-z0 = -(d:ℂ)*(t:ℂ) := by simp [z0]
  have hz : τ-z0 ≠ 0 := by
    rw [hdiff]
    exact mul_ne_zero (neg_ne_zero.mpr hdC) htC
  have hzero : q z0 = 0 := by
    simp only [q]
    rw [hdiff]
    simp only [neg_sq, mul_pow, htc, mul_one]
    field_simp
    norm_num
  have hqc : ContinuousAt q z0 := by
    unfold q
    fun_prop (disch := simp [hz])
  have hsc : ContinuousAt Complex.sqrt (q z0) := by
    rw [hzero]
    exact Complex.continuousAt_sqrt (Or.inl (by simp))
  have hr : ContinuousAt (normalizedStandardRoot τ ((2*(d:ℂ))^2)) z0 := by
    unfold normalizedStandardRoot
    exact (continuousAt_const.sub continuousAt_id).mul (hsc.comp hqc)
  exact hr

private theorem root_tendsto_endpoint (τ : ℂ) (d t s : ℝ)
    (hd : 0 < d) (htsq : t^2=1) :
    Tendsto (fun ε : ℝ => normalizedStandardRoot τ ((2*(d:ℂ))^2)
      (τ+(d:ℂ)*((t:ℂ)+(s:ℂ)*(ε:ℂ)*I)))
      (𝓝[>] (0:ℝ)) (𝓝 (0:ℂ)) := by
  have hpath : Tendsto (fun ε : ℝ =>
      τ+(d:ℂ)*((t:ℂ)+(s:ℂ)*(ε:ℂ)*I)) (𝓝[>] (0:ℝ))
      (𝓝 (τ+(d:ℂ)*(t:ℂ))) := by
    have hc : ContinuousAt (fun ε : ℝ =>
      τ+(d:ℂ)*((t:ℂ)+(s:ℂ)*(ε:ℂ)*I)) 0 := by fun_prop
    simpa using hc.tendsto.mono_left nhdsWithin_le_nhds
  have hlim := (root_continuous_endpoint τ d t hd htsq).tendsto.comp hpath
  have hval : normalizedStandardRoot τ ((2*(d:ℂ))^2)
      (τ+(d:ℂ)*(t:ℂ)) = 0 := by
    let q : ℂ := 1-(2*(d:ℂ))^2/(4*(τ-(τ+(d:ℂ)*(t:ℂ)))^2)
    have hdC : (d:ℂ) ≠ 0 := by exact_mod_cast ne_of_gt hd
    have htc : (t:ℂ)^2=1 := by exact_mod_cast htsq
    have hq : q = 0 := by
      simp only [q]
      have hdiff : τ-(τ+(d:ℂ)*(t:ℂ)) = -(d:ℂ)*(t:ℂ) := by ring
      rw [hdiff]
      simp only [neg_sq, mul_pow, htc, mul_one]
      field_simp
      norm_num
    unfold normalizedStandardRoot
    change (τ-(τ+(d:ℂ)*(t:ℂ)))*Complex.sqrt q = 0
    rw [hq]
    simp
  rw [hval] at hlim
  exact hlim

/-- The upper boundary value in (2.12) for a positive real gap,
including its midpoint and endpoints. -/
theorem normalizedStandardRoot_tendsto_gap_upper_real (τ : ℂ) (d t : ℝ)
    (hd : 0 < d) (htl : -1 ≤ t) (htr : t ≤ 1) :
    Tendsto (fun ε : ℝ => normalizedStandardRoot τ ((2*(d:ℂ))^2)
      (τ+(d:ℂ)*((t:ℂ)+(ε:ℂ)*I))) (𝓝[>] (0:ℝ))
      (𝓝 (-(d:ℂ)*I*(Real.sqrt (1-t^2):ℂ))) := by
  rcases lt_or_eq_of_le htl with hlt | hleft
  · rcases lt_or_eq_of_le htr with hrt | hright
    · exact real_gap_upper_interior τ d t hd hlt hrt
    · subst t
      simpa using root_tendsto_endpoint τ d 1 1 hd (by norm_num)
  · have ht : t = -1 := hleft.symm
    subst t
    simpa using root_tendsto_endpoint τ d (-1) 1 hd (by norm_num)

/-- The lower boundary value in (2.12) for a positive real gap,
including its midpoint and endpoints. -/
theorem normalizedStandardRoot_tendsto_gap_lower_real (τ : ℂ) (d t : ℝ)
    (hd : 0 < d) (htl : -1 ≤ t) (htr : t ≤ 1) :
    Tendsto (fun ε : ℝ => normalizedStandardRoot τ ((2*(d:ℂ))^2)
      (τ+(d:ℂ)*((t:ℂ)-(ε:ℂ)*I))) (𝓝[>] (0:ℝ))
      (𝓝 ((d:ℂ)*I*(Real.sqrt (1-t^2):ℂ))) := by
  rcases lt_or_eq_of_le htl with hlt | hleft
  · rcases lt_or_eq_of_le htr with hrt | hright
    · exact real_gap_lower_interior τ d t hd hlt hrt
    · subst t
      have h := root_tendsto_endpoint τ d 1 (-1) hd (by norm_num)
      convert h using 1
      · funext ε
        congr 1
        push_cast
        ring
      · norm_num
  · have ht : t = -1 := hleft.symm
    subst t
    have h := root_tendsto_endpoint τ d (-1) (-1) hd (by norm_num)
    convert h using 1
    · funext ε
      congr 1
      push_cast
      ring
    · norm_num

end NLS.ZakharovShabat
