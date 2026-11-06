import NLS.FunctionalAnalysis.NeumannCompositionBound
import Mathlib.Topology.Sequences

noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology
open scoped ENNReal ComplexConjugate Classical

namespace NLS



variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]

/-- Norm convergence to a bijective operator gives genuine nearby
inverses with one common norm bound. -/
theorem eventually_exists_inverse_bound_of_tendsto_bijective
    {ι : Type*} {l : Filter ι} (T : ι → E →L[ℂ] E) (S : E →L[ℂ] E)
    (hT : Tendsto T l (𝓝 S)) (hS : Function.Bijective S) :
    ∃ C : ℝ, 1≤C ∧ ∀ᶠ i in l, ∃ R : E →L[ℂ] E,
      (T i).comp R=ContinuousLinearMap.id ℂ E ∧
        R.comp (T i)=ContinuousLinearMap.id ℂ E ∧ ‖R‖≤C := by
  let e := ContinuousLinearEquiv.ofBijective S (LinearMap.ker_eq_bot.mpr hS.1) (LinearMap.range_eq_top.mpr hS.2)
  let R0 := e.symm.toContinuousLinearMap
  let B : ℝ := ‖R0‖+1
  have hB : 0<B := by dsimp only [B];positivity
  have hR : ‖R0‖≤B := by dsimp only [B];linarith
  have hSR : S.comp R0=ContinuousLinearMap.id ℂ E := by ext x;exact e.apply_symm_apply x
  have hRS : R0.comp S=ContinuousLinearMap.id ℂ E := by ext x;exact e.symm_apply_apply x
  refine ⟨2*B,by dsimp only [B];nlinarith [norm_nonneg R0],?_⟩
  filter_upwards [Metric.tendsto_nhds.mp hT (1/(2*B)) (by positivity)] with i hi
  have hd : ‖S-T i‖≤1/(2*B) := by
    rw [norm_sub_rev]
    exact (show ‖T i-S‖<1/(2*B) by simpa only [dist_eq_norm] using hi).le
  have hnear : ‖R0.comp (S-T i)‖≤(1/2 : ℝ) := by
    apply (ContinuousLinearMap.opNorm_comp_le _ _).trans
    apply (mul_le_mul hR hd (norm_nonneg _) hB.le).trans_eq
    field_simp
  obtain ⟨R,hTR,hRT,hbound⟩ := exists_inverse_norm_le_two_mul_of_composition_near (T i) S R0 hSR hRS hnear
  exact ⟨R,hTR,hRT,hbound.trans (by linarith)⟩

theorem eventually_lower_bound_of_tendsto_bijective
    {ι : Type*} {l : Filter ι} (T : ι → E →L[ℂ] E) (S : E →L[ℂ] E)
    (hT : Tendsto T l (𝓝 S)) (hS : Function.Bijective S) :
    ∃ C : ℝ, 1≤C ∧ ∀ᶠ i in l, ∀ x : E, ‖x‖≤C*‖T i x‖ := by
  obtain ⟨C,hC,he⟩ := eventually_exists_inverse_bound_of_tendsto_bijective T S hT hS
  refine ⟨C,hC,he.mono ?_⟩
  intro i hi x
  obtain ⟨R,_,hRT,hR⟩ := hi
  have hx : R (T i x)=x := by
    have hh := congrArg (fun A : E →L[ℂ] E => A x) hRT
    exact hh
  calc
    ‖x‖=‖R (T i x)‖ := congrArg norm hx.symm
    _ ≤ ‖R‖*‖T i x‖ := R.le_opNorm _
    _ ≤ C*‖T i x‖ := mul_le_mul_of_nonneg_right hR (norm_nonneg _)

/-- Compactness turns sequential norm limits with bijective limits into
a common large-index lower bound for every parameter in the compact set. -/
theorem exists_uniform_eventual_lower_bound_of_compact_norm_limits
    {X : Type*} [PseudoMetricSpace X] (K : Set X) (hK : IsCompact K)
    (T : ℕ → X → E →L[ℂ] E) (S : X → E →L[ℂ] E)
    (hS : ∀ x∈K, Function.Bijective (S x))
    (hlim : ∀ n : ℕ → ℕ, (∀ i, 1≤n i) → Tendsto n atTop atTop →
      ∀ a : ℕ → X, (∀ i, a i∈K) → ∀ a0∈K, Tendsto a atTop (𝓝 a0) →
        Tendsto (fun i => T (n i) (a i)) atTop (𝓝 (S a0))) :
    ∃ N : ℕ, ∃ C : ℝ, 1≤N ∧ 1≤C ∧ ∀ n : ℕ, N≤n → ∀ a∈K, ∀ x : E,
      ‖x‖≤C*‖T n a x‖ := by
  by_contra! h
  have hw (j : ℕ) : ∃ n : ℕ, j+1≤n ∧ ∃ a∈K, ∃ x : E,
      ((j : ℝ)+1)*‖T n a x‖<‖x‖ := by
    exact h (j+1) ((j : ℝ)+1) (by omega) (by linarith [Nat.cast_nonneg (α := ℝ) j])
  choose n hn a ha x hbad using hw
  obtain ⟨a0,ha0,φ,hφ,hconv⟩ := hK.tendsto_subseq ha
  have hni : Tendsto (fun i => n (φ i)) atTop atTop := by
    have hnlim : Tendsto n atTop atTop := tendsto_atTop_mono (fun j => (Nat.le_succ j).trans (hn j)) tendsto_id
    exact hnlim.comp hφ.tendsto_atTop
  have hlim0 := hlim (fun i => n (φ i)) (fun i => by have hh := hn (φ i);omega) hni
    (fun i => a (φ i)) (fun i => ha (φ i)) a0 ha0 hconv
  obtain ⟨C,hC,hbound⟩ := eventually_lower_bound_of_tendsto_bijective _ _ hlim0 (hS a0 ha0)
  have hφReal : Tendsto (fun i => (φ i : ℝ)+1) atTop atTop := by
    apply tendsto_atTop_mono (fun i => le_add_of_nonneg_right (by norm_num : (0 : ℝ)≤1))
    exact (tendsto_natCast_atTop_atTop : Tendsto (fun j : ℕ => (j : ℝ)) atTop atTop).comp hφ.tendsto_atTop
  have he : ∀ᶠ i in atTop, C≤(φ i : ℝ)+1 := hφReal.eventually (eventually_ge_atTop C)
  obtain ⟨i,hi,hiC⟩ := (hbound.and he).exists
  have hh := hi (x (φ i))
  have hmul := mul_le_mul_of_nonneg_right hiC (norm_nonneg (T (n (φ i)) (a (φ i)) (x (φ i))))
  linarith [hbad (φ i)]

end NLS
