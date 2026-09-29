import NLS.SequenceSpaces.OperatorDiagonal
import Mathlib.Topology.Algebra.Monoid

/-!
# Norm convergence of diagonal operators

Coordinatewise diagonal convergence and eventual uniform decay toward
one constant imply convergence of the diagonal symbols in `ℓ∞`.
The corresponding diagonal multipliers then converge in operator norm.
-/

noncomputable section
open Filter Topology Metric
open scoped ENNReal
namespace NLS.Coeff
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- A bounded-symbol perturbation controls the operator-norm change
of the corresponding diagonal multiplier. -/
theorem norm_multiplierCLM_sub_le (u v : Coeff ⊤) :
    ‖multiplierCLM (p := p) u - multiplierCLM v‖ ≤ ‖u-v‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
  intro a
  have heq : ((multiplierCLM (p := p) u - multiplierCLM (p := p) v) :
      Coeff p →L[ℂ] Coeff p) a = multiplier (u-v) a := by
    ext m
    simp only [sub_apply,multiplierCLM_apply,
      lp.coeFn_sub,Pi.sub_apply,multiplier_apply]
    ring
  rw [heq]
  exact norm_multiplier_le (u-v) a

/-- Coordinatewise limits and one eventual uniform constant tail
force convergence of diagonal symbols in the supremum norm. -/
theorem tendsto_operatorDiagonalSymbol_of_uniform_constantTail
    {α : Type*} (l : Filter α) [NeBot l]
    (T : α → Coeff p →L[ℂ] Coeff p)
    (S : Coeff p →L[ℂ] Coeff p) (z : ℂ)
    (hentry : ∀ m : ℤ,
      Tendsto (fun i => (T i (lp.single p m 1)) m) l
        (𝓝 ((S (lp.single p m 1)) m)))
    (htail : ∀ ε : ℝ, 0 < ε → ∃ K : ℕ,
      ∀ᶠ i in l, ∀ m : ℤ, K ≤ m.natAbs →
        ‖(T i (lp.single p m 1)) m-z‖ < ε) :
    Tendsto (fun i => operatorDiagonalSymbol (T i)) l
      (𝓝 (operatorDiagonalSymbol S)) := by
  classical
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  obtain ⟨K,hK⟩ := htail (ε/4) (by positivity)
  let s : Finset ℤ := Finset.Icc (-(K : ℤ)) (K : ℤ)
  have hStail (m : ℤ) (hm : K ≤ m.natAbs) :
      ‖(S (lp.single p m 1)) m-z‖ ≤ ε/4 := by
    apply le_of_tendsto ((hentry m).sub_const z).norm
    filter_upwards [hK] with i hi
    exact (hi m hm).le
  have hhead : ∀ᶠ i in l, ∀ m ∈ s,
      ‖(T i (lp.single p m 1)) m-(S (lp.single p m 1)) m‖ < ε/2 := by
    rw [Finset.eventually_all]
    intro m hm
    simpa only [dist_eq_norm] using
      Metric.tendsto_nhds.mp (hentry m) (ε/2) (half_pos hε)
  filter_upwards [hK,hhead] with i hi hh
  rw [dist_eq_norm]
  have hnorm : ‖operatorDiagonalSymbol (T i)-operatorDiagonalSymbol S‖ ≤ ε/2 := by
    apply lp.norm_le_of_forall_le (by positivity)
    intro m
    change ‖(T i (lp.single p m 1)) m-(S (lp.single p m 1)) m‖ ≤ ε/2
    by_cases hm : m ∈ s
    · exact (hh m hm).le
    · have hmK : K ≤ m.natAbs := by
        simp only [s,Finset.mem_Icc] at hm
        omega
      have htri :
          ‖(T i (lp.single p m 1)) m-(S (lp.single p m 1)) m‖ ≤
            ‖(T i (lp.single p m 1)) m-z‖+
              ‖(S (lp.single p m 1)) m-z‖ := by
        calc
          _ = ‖((T i (lp.single p m 1)) m-z)-
              ((S (lp.single p m 1)) m-z)‖ := by congr 1; ring
          _ ≤ _ := norm_sub_le _ _
      linarith [hi m hmK,hStail m hmK]
  exact hnorm.trans_lt (half_lt_self hε)

/-- Under the same hypotheses, the extracted diagonal multipliers
converge in operator norm on every Banach coefficient space. -/
theorem tendsto_operatorDiagonalMultiplier_of_uniform_constantTail
    {α : Type*} (l : Filter α) [NeBot l]
    (T : α → Coeff p →L[ℂ] Coeff p)
    (S : Coeff p →L[ℂ] Coeff p) (z : ℂ)
    (hentry : ∀ m : ℤ,
      Tendsto (fun i => (T i (lp.single p m 1)) m) l
        (𝓝 ((S (lp.single p m 1)) m)))
    (htail : ∀ ε : ℝ, 0 < ε → ∃ K : ℕ,
      ∀ᶠ i in l, ∀ m : ℤ, K ≤ m.natAbs →
        ‖(T i (lp.single p m 1)) m-z‖ < ε) :
    Tendsto (fun i => multiplierCLM (p := p) (operatorDiagonalSymbol (T i))) l
      (𝓝 (multiplierCLM (p := p) (operatorDiagonalSymbol S))) := by
  have hsymbol := tendsto_operatorDiagonalSymbol_of_uniform_constantTail
    l T S z hentry htail
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  filter_upwards [Metric.tendsto_nhds.mp hsymbol ε hε] with i hi
  rw [dist_eq_norm] at hi ⊢
  exact (norm_multiplierCLM_sub_le (p := p)
    (operatorDiagonalSymbol (T i)) (operatorDiagonalSymbol S)).trans_lt hi

end NLS.Coeff
