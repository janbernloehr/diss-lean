import NLS.SequenceSpaces.WeightedFrequencyRemainders
import NLS.SequenceSpaces.PositiveOneExtension
import NLS.SequenceSpaces.SobolevRatioTail

/-! Removing the literal leading action term from weighted frequency
estimates, with proper positive-index enumeration and exact tail orders. -/
noncomputable section
open Set Filter Topology Complex
open scoped ENNReal
namespace NLS.Coeff

theorem weighted_remove_linear_counterterm_bound
    (w c : ℝ) (hw : 0<w) (hc : 0≤c) (a b : ℂ) :
    w*‖b‖≤w*‖b+(c:ℂ)*(a/(w:ℂ))‖+c*‖a‖ := by
  have he : b=(b+(c:ℂ)*(a/(w:ℂ)))-(c:ℂ)*(a/(w:ℂ)) := by ring
  have hn : w*‖(c:ℂ)*(a/(w:ℂ))‖=c*‖a‖ := by
    rw [norm_mul,norm_div,Complex.norm_real,Real.norm_of_nonneg hc,
      Complex.norm_real,Real.norm_of_nonneg hw.le]
    field_simp
  calc
    _ ≤ w*(‖b+(c:ℂ)*(a/(w:ℂ))‖+‖(c:ℂ)*(a/(w:ℂ))‖) :=
      mul_le_mul_of_nonneg_left (by simpa only [← he] using norm_sub_le (b+(c:ℂ)*(a/(w:ℂ))) ((c:ℂ)*(a/(w:ℂ)))) hw.le
    _ = _ := by rw [mul_add,hn]

theorem tendsto_norm_enumerated_positive (e : ℤ ≃ ℕ+) (a : Coeff 1) :
    Tendsto (fun n : ℕ => ‖a (e.symm ⟨n+1,by omega⟩)‖) atTop (𝓝 0) := by
  have h := tendsto_norm_positive_apply (positiveOneExtendCoeff e a)
  apply h.congr'
  exact Filter.Eventually.of_forall (fun n => by
    have he : positiveIndexInjection e (e.symm ⟨n+1,by omega⟩)=((n+1:ℕ):ℤ) := by
      exact congrArg (fun j : ℕ+ => (j:ℤ)) (e.apply_symm_apply (⟨n+1,by omega⟩:ℕ+))
    change ‖positiveOneExtendFunction e a ((n+1:ℕ):ℤ)‖=_
    rw [← he,positiveOneExtendFunction_index])

theorem tendsto_positive_weighted_sobolev_mono
    (s r : ℝ) (hsr : s≤r) (f : ℕ+ → ℂ)
    (h : Tendsto (fun n : ℕ => Weight.sobolev r ((n+1:ℕ):ℤ)*‖f ⟨n+1,by omega⟩‖) atTop (𝓝 0)) :
    Tendsto (fun n : ℕ => Weight.sobolev s ((n+1:ℕ):ℤ)*‖f ⟨n+1,by omega⟩‖) atTop (𝓝 0) :=
  squeeze_zero (fun _ => mul_nonneg ((Weight.sobolev s).positive _).le (norm_nonneg _))
    (fun _ => mul_le_mul_of_nonneg_right (Weight.sobolev_mono hsr _) (norm_nonneg _)) h

theorem exists_uniform_strict_sobolev_frequency_tail
    {E : Type*} (U : Set E) (f : ℕ+ → E → ℂ) (s r : ℝ) (hsr : s<r)
    (K : ℕ) (M : ℝ) (hM : 0≤M)
    (hb : ∀ a∈U, ∀ n : ℕ+, K≤(n:ℤ).natAbs → Weight.sobolev r (n:ℤ)*‖f n a‖≤M) :
    ∀ ε > (0:ℝ), ∃ N : ℕ, ∀ a∈U, ∀ n : ℕ+, N≤(n:ℤ).natAbs →
      Weight.sobolev s (n:ℤ)*‖f n a‖≤ε := by
  intro ε hε
  obtain ⟨L,hL⟩ := Weight.exists_sobolev_ratio_tail s r hsr (div_pos hε (by linarith : 0<M+1))
  refine ⟨max K L,?_⟩
  intro a ha n hn
  have hr := (hL (n:ℤ) ((le_max_right _ _).trans hn)).le
  have hwr : 0<Weight.sobolev r (n:ℤ) := (Weight.sobolev r).positive (n:ℤ)
  calc
    _ = (Weight.sobolev s (n:ℤ)/Weight.sobolev r (n:ℤ))*
        (Weight.sobolev r (n:ℤ)*‖f n a‖) := by field_simp
    _ ≤ (ε/(M+1))*M := mul_le_mul hr (hb a ha n ((le_max_left _ _).trans hn))
      (by positivity) (by positivity)
    _ ≤ ε := by rw [div_mul_eq_mul_div];apply (div_le_iff₀ (by linarith : 0<M+1)).mpr;nlinarith

theorem tendsto_positive_weighted_of_uniform_tail
    {E : Type*} (U : Set E) (f : ℕ+ → E → ℂ) (w : ℤ → ℝ)
    (hw : ∀ n : ℕ+, 0≤w (n:ℤ))
    (hb : ∀ ε > (0:ℝ), ∃ K : ℕ, ∀ a∈U, ∀ n : ℕ+, K≤(n:ℤ).natAbs → w (n:ℤ)*‖f n a‖≤ε)
    (a : E) (ha : a∈U) :
    Tendsto (fun m : ℕ => w ((m+1:ℕ):ℤ)*‖f ⟨m+1,by omega⟩ a‖) atTop (𝓝 0) := by
  apply Metric.tendsto_atTop.mpr
  intro ε hε
  obtain ⟨K,hK⟩ := hb (ε/2) (half_pos hε)
  refine ⟨K,?_⟩
  intro m hm
  let p : ℕ+ := ⟨m+1,by omega⟩
  have hp : K≤(p:ℤ).natAbs := by change K≤m+1;omega
  have h := hK a ha p hp
  have hn : 0≤w ((m+1:ℕ):ℤ)*‖f ⟨m+1,by omega⟩ a‖ := mul_nonneg (hw p) (norm_nonneg (f p a))
  rw [dist_zero_right,Real.norm_eq_abs,abs_of_nonneg hn]
  exact h.trans_lt (half_lt_self hε)

end NLS.Coeff
