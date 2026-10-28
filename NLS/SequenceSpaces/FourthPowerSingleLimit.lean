import NLS.SequenceSpaces.Basic
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-! # Convergence of a fourth-power sum concentrated at one index -/
noncomputable section
open Filter Topology
namespace NLS

/-- Vanishing fourth-power error implies convergence to the specified scalar. -/
theorem tendsto_of_fourthPowerError {α : Type*} {l : Filter α} (f : α → ℝ) (c : ℝ)
    (h : Tendsto (fun x => (f x-c)^4) l (𝓝 0)) : Tendsto f l (𝓝 c) := by
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  have h' := h.sqrt.sqrt
  have he (x : ℝ) : Real.sqrt (Real.sqrt (x^4)) = |x| := by
    rw [show x^4=(x^2)^2 by ring,Real.sqrt_sq (sq_nonneg x),Real.sqrt_sq_eq_abs]
  simpa only [he,Real.sqrt_zero,Real.norm_eq_abs] using h'

/-- A summable fourth-power error controls the full sum and its distinguished term. -/
theorem fourthPowerSum_bounds_single (f e : ℤ → ℝ) (n : ℤ) (c : ℝ)
    (hf : ∀ k, 0 ≤ f k)
    (hbound : ∀ k, |f k-(if k=n then c else 0)| ≤ e k)
    (hs : Summable (fun k => (e k)^4)) :
    Summable (fun k => (f k)^4) ∧
    (f n)^4 ≤ ∑' k, (f k)^4 ∧
    (∑' k, (f k)^4) ≤ (f n)^4+∑' k, (e k)^4 ∧
    (f n-c)^4 ≤ ∑' k, (e k)^4 := by
  have hsingle : Summable (fun k : ℤ => if k=n then (f n)^4 else 0) := (hasSum_ite_eq n ((f n)^4)).summable
  have hnon (k : ℤ) : 0 ≤ (f k)^4 := by positivity
  have hdom (k : ℤ) : (f k)^4 ≤ (if k=n then (f n)^4 else 0)+(e k)^4 := by
    by_cases hk : k=n
    · subst k
      simp only [if_true]
      linarith [show 0 ≤ (e n)^4 by positivity]
    · simp only [if_neg hk,zero_add]
      have hb := hbound k
      simp only [if_neg hk,sub_zero,abs_of_nonneg (hf k)] at hb
      exact pow_le_pow_left₀ (hf k) hb 4
  have hfS := (hsingle.add hs).of_nonneg_of_le hnon hdom
  refine ⟨hfS,hfS.le_tsum n (fun k _ => hnon k),?_,?_⟩
  · have h := hfS.tsum_le_tsum hdom (hsingle.add hs)
    simpa only [hsingle.tsum_add hs,tsum_ite_eq] using h
  · have hb := hbound n
    simp only [if_true] at hb
    have hp := pow_le_pow_left₀ (abs_nonneg _) hb 4
    rw [← abs_pow,abs_of_nonneg (show 0 ≤ (f n-c)^4 by positivity)] at hp
    exact hp.trans (hs.le_tsum n (fun _ _ => by positivity))

/-- Concentration at one index transfers a vanishing infinite error sum to the actual fourth-power sum. -/
theorem fourthPowerSum_tendsto_single {α : Type*} {l : Filter α}
    (f e : α → ℤ → ℝ) (n : ℤ) (c : ℝ)
    (hb : ∀ᶠ x in l, (∀ k, 0 ≤ f x k) ∧ (∀ k, 0 ≤ e x k) ∧
      (∀ k, |f x k-(if k=n then c else 0)| ≤ e x k) ∧
      Summable (fun k => (e x k)^4))
    (ht : Tendsto (fun x => ∑' k, (e x k)^4) l (𝓝 0)) :
    Tendsto (fun x => ∑' k, (f x k)^4) l (𝓝 (c^4)) := by
  have hb' : ∀ᶠ x in l,
      (f x n)^4 ≤ ∑' k, (f x k)^4 ∧
      (∑' k, (f x k)^4) ≤ (f x n)^4+∑' k, (e x k)^4 ∧
      (f x n-c)^4 ≤ ∑' k, (e x k)^4 := by
    filter_upwards [hb] with x hx
    exact (fourthPowerSum_bounds_single (f x) (e x) n c hx.1 hx.2.2.1 hx.2.2.2).2
  have herr : Tendsto (fun x => (f x n-c)^4) l (𝓝 0) :=
    squeeze_zero' (Eventually.of_forall (fun _ => by positivity))
      (hb'.mono (fun _ h => h.2.2)) ht
  have hpoint := (tendsto_of_fourthPowerError (fun x => f x n) c herr).pow 4
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' hpoint (by simpa using hpoint.add ht)
    (hb'.mono (fun _ h => h.1)) (hb'.mono (fun _ h => h.2.1))

end NLS
