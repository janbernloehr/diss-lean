import NLS.SequenceSpaces.FourierRealTorusExample
import Mathlib.Topology.Algebra.Module.Basic

/-! The physical weighted c0 condition is a proper closed real subspace
of the endpoint infinity space. Its complement is open and dense. -/
noncomputable section
open Set Filter Topology
open scoped ENNReal
namespace NLS.WeightedCoeff

theorem positiveWeightedC0_iff_tendsto (w : Weight) (a : fourierRealZeroSubmodule w ⊤) :
    PositiveWeightedC0 w a ↔
      Tendsto (fun n : ℕ => (w n:ℂ)*a.val.val.val n) atTop (𝓝 0) := by
  unfold PositiveWeightedC0
  rw [Metric.tendsto_atTop]
  simp only [dist_zero_right,norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos (w.positive _)]

def positiveWeightedC0Submodule (w : Weight) : Submodule ℝ (fourierRealZeroSubmodule w ⊤) where
  carrier := {a | PositiveWeightedC0 w a}
  zero_mem' := by
    change PositiveWeightedC0 w 0
    rw [positiveWeightedC0_iff_tendsto]
    change Tendsto (fun n : ℕ => (w n:ℂ)*0) atTop (𝓝 0)
    simpa only [mul_zero] using (tendsto_const_nhds (x := (0:ℂ)))
  add_mem' := by
    intro a b ha hb
    change PositiveWeightedC0 w a at ha
    change PositiveWeightedC0 w b at hb
    change PositiveWeightedC0 w (a+b)
    rw [positiveWeightedC0_iff_tendsto] at ha hb ⊢
    change Tendsto (fun n : ℕ => (w n:ℂ)*(a.val.val.val n+b.val.val.val n)) atTop (𝓝 0)
    simp only [mul_add]
    simpa only [zero_add] using ha.add hb
  smul_mem' := by
    intro c a ha
    change PositiveWeightedC0 w a at ha
    change PositiveWeightedC0 w (c • a)
    rw [positiveWeightedC0_iff_tendsto] at ha ⊢
    change Tendsto (fun n : ℕ => (w n:ℂ)*((c:ℂ)*a.val.val.val n)) atTop (𝓝 0)
    simpa only [mul_left_comm,mul_zero] using ha.const_mul (c:ℂ)

theorem fourierReal_weighted_norm_sub_le_dist (w : Weight)
    (a b : fourierRealZeroSubmodule w ⊤) (k : ℤ) :
    w k*‖a.val.val.val k-b.val.val.val k‖≤dist a b := by
  have h := (le_div_iff₀ (w.positive k)).mp (norm_apply_le w ⊤ (a.val.val-b.val.val) k)
  rw [dist_eq_norm]
  change w k*‖a.val.val.val k-b.val.val.val k‖≤‖a.val.val-b.val.val‖
  simpa only [sub_val,mul_comm] using h

theorem isClosed_positiveWeightedC0Submodule (w : Weight) :
    IsClosed (positiveWeightedC0Submodule w : Set (fourierRealZeroSubmodule w ⊤)) := by
  apply isClosed_of_closure_subset
  intro a ha
  change PositiveWeightedC0 w a
  intro ε hε
  obtain ⟨b,hb,hclose⟩ := Metric.mem_closure_iff.mp ha (ε/2) (by positivity)
  change PositiveWeightedC0 w b at hb
  obtain ⟨N,hN⟩ := hb (ε/2) (by positivity)
  refine ⟨N,?_⟩
  intro n hn
  have hdiff := (fourierReal_weighted_norm_sub_le_dist w a b (n:ℤ)).trans_lt hclose
  have hsmall := hN n hn
  have htri := mul_le_mul_of_nonneg_left (norm_le_norm_sub_add (a.val.val.val (n:ℤ))
    (b.val.val.val (n:ℤ))) (w.positive (n:ℤ)).le
  nlinarith

theorem isOpen_not_positiveWeightedC0 (w : Weight) :
    IsOpen {a : fourierRealZeroSubmodule w ⊤ | ¬PositiveWeightedC0 w a} :=
  (isClosed_positiveWeightedC0Submodule w).isOpen_compl

theorem dense_not_positiveWeightedC0 (w : Weight) (hw : ∀ k, w (-k)=w k) :
    Dense {a : fourierRealZeroSubmodule w ⊤ | ¬PositiveWeightedC0 w a} := by
  change Dense (positiveWeightedC0Submodule w : Set (fourierRealZeroSubmodule w ⊤))ᶜ
  rw [← interior_eq_empty_iff_dense_compl]
  apply Set.eq_empty_iff_forall_notMem.mpr
  intro a ha
  have heq := (positiveWeightedC0Submodule w).eq_top_of_nonempty_interior' ⟨a,ha⟩
  have hmem : realInverseWeightCoefficients w hw ∈ positiveWeightedC0Submodule w := by
    rw [heq]
    trivial
  exact not_positiveWeightedC0_realInverseWeightCoefficients w hw hmem

end NLS.WeightedCoeff
