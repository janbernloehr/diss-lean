import NLS.SequenceSpaces.BoundedMatrixLimit
import Mathlib.Topology.MetricSpace.UniformConvergence

/-!
# Extending coordinatewise operator convergence from finite inputs

An eventually uniformly bounded operator family is equicontinuous
after replacing its finitely many exceptional terms. Scalar
coordinate convergence on the dense finite-support subspace then
extends to every input.
-/

noncomputable section
open Filter Topology
open scoped NNReal ENNReal
namespace NLS.Coeff

/-- Basis-entry convergence implies convergence on each finite input,
without a norm bound on the operator family. -/
theorem tendsto_operator_coordinate_of_basis_on_finsupp
    {p : ℝ≥0∞} [Fact (1 ≤ p)]
    {α : Type*} (l : Filter α)
    (T : α → Coeff p →L[ℂ] Coeff p)
    (Q : Coeff p →L[ℂ] Coeff p)
    (hentry : ∀ m k : ℤ,
      Tendsto (fun i => (T i (lp.single p k 1)) m) l
        (𝓝 ((Q (lp.single p k 1)) m)))
    (u : ℤ →₀ ℂ) (m : ℤ) :
    Tendsto (fun i => (T i (ofFinsupp u)) m) l
      (𝓝 ((Q (ofFinsupp u)) m)) := by
  classical
  let e (k : ℤ) : Coeff p := lp.single p k 1
  have hinput : ofFinsupp (p := p) =
      Finsupp.linearCombination ℂ e := by
    apply Finsupp.lhom_ext
    intro k z
    ext j
    by_cases hjk : j = k
    · subst j
      simp [Finsupp.linearCombination_single, ofFinsupp_apply,
        e, lp.single_apply]
    · simp [Finsupp.linearCombination_single, ofFinsupp_apply,
        e, lp.single_apply, hjk]
  have hterm (k : ℤ) : Tendsto
      (fun i => u k * (T i (e k)) m) l
      (𝓝 (u k * (Q (e k)) m)) :=
    (hentry m k).const_mul (u k)
  have hsum := tendsto_finsetSum u.support (fun k _ => hterm k)
  convert hsum using 1
  · ext i
    rw [show ofFinsupp (p := p) u =
      (Finsupp.linearCombination ℂ e) u from congrArg (· u) hinput]
    simp only [Finsupp.linearCombination_apply, Finsupp.sum,
      map_sum, map_smul, lp.coeFn_sum, Finset.sum_apply,
      lp.coeFn_smul, Pi.smul_apply, smul_eq_mul]
  · rw [show ofFinsupp (p := p) u =
      (Finsupp.linearCombination ℂ e) u from congrArg (· u) hinput]
    simp only [Finsupp.linearCombination_apply, Finsupp.sum,
      map_sum, map_smul, lp.coeFn_sum, Finset.sum_apply,
      lp.coeFn_smul, Pi.smul_apply, smul_eq_mul]

/-- Coordinatewise convergence on finite inputs extends to all `ℓᵖ`
inputs when the operators have an eventual common norm bound. -/
theorem tendsto_operator_coordinate_of_finsupp
    {p : ℝ≥0∞} [Fact (1 ≤ p)] (hp : p ≠ ⊤)
    {α : Type*} (l : Filter α)
    (T : α → Coeff p →L[ℂ] Coeff p)
    (Q : Coeff p →L[ℂ] Coeff p)
    (M : ℝ) (hM : 0 ≤ M) (hQ : ‖Q‖ ≤ M)
    (hbound : ∀ᶠ i in l, ‖T i‖ ≤ M)
    (hfin : ∀ u : ℤ →₀ ℂ, ∀ m : ℤ,
      Tendsto (fun i => (T i (ofFinsupp u)) m) l
        (𝓝 ((Q (ofFinsupp u)) m)))
    (x : Coeff p) (m : ℤ) :
    Tendsto (fun i => (T i x) m) l (𝓝 ((Q x) m)) := by
  classical
  let T' (i : α) : Coeff p →L[ℂ] Coeff p :=
    if ‖T i‖ ≤ M then T i else Q
  have hT'norm (i : α) : ‖T' i‖ ≤ M := by
    dsimp [T']
    split_ifs with hi
    · exact hi
    · exact hQ
  have hTeq : T' =ᶠ[l] T := by
    filter_upwards [hbound] with i hi
    simp [T',hi]
  let F : α → Coeff p → ℂ := fun i y => (T' i y) m
  let f : Coeff p → ℂ := fun y => (Q y) m
  let K : ℝ≥0 := ⟨M,hM⟩
  have hF_lip (i : α) : LipschitzWith K (F i) := by
    have hTlip : LipschitzWith K (T' i) :=
      ContinuousLinearMap.lipschitzWith_of_opNorm_le (by
        change ‖T' i‖ ≤ M
        exact hT'norm i)
    convert (lp.lipschitzWith_one_eval p m).comp hTlip using 1
    · exact (one_mul K).symm
    · rfl
  have hF_equicont : Equicontinuous F :=
    (LipschitzWith.uniformEquicontinuous F K hF_lip).equicontinuous
  have hfcont : Continuous f :=
    (lp.evalCLM ℂ (fun _ : ℤ => ℂ) p m).continuous.comp Q.continuous
  have hclosed : IsClosed
      {y : Coeff p | Tendsto (fun i => F i y) l (𝓝 (f y))} :=
    hF_equicont.isClosed_setOfPred_tendsto hfcont
  have hrange : Set.range (ofFinsupp (p := p)) ⊆
      {y : Coeff p | Tendsto (fun i => F i y) l (𝓝 (f y))} := by
    rintro y ⟨u,rfl⟩
    apply (hfin u m).congr'
    filter_upwards [hTeq] with i hi
    simp [F,hi]
  have hlimit : Tendsto (fun i => F i x) l (𝓝 (f x)) :=
    hclosed.closure_subset (closure_mono hrange ((denseRange_ofFinsupp hp) x))
  apply hlimit.congr'
  filter_upwards [hTeq] with i hi
  simp [F,hi]

/-- Eventual uniform boundedness and basis-entry convergence imply
coordinatewise convergence on every input vector. -/
theorem tendsto_operator_coordinate_of_basis
    {p : ℝ≥0∞} [Fact (1 ≤ p)] (hp : p ≠ ⊤)
    {α : Type*} (l : Filter α)
    (T : α → Coeff p →L[ℂ] Coeff p)
    (Q : Coeff p →L[ℂ] Coeff p)
    (M : ℝ) (hM : 0 ≤ M) (hQ : ‖Q‖ ≤ M)
    (hbound : ∀ᶠ i in l, ‖T i‖ ≤ M)
    (hentry : ∀ m k : ℤ,
      Tendsto (fun i => (T i (lp.single p k 1)) m) l
        (𝓝 ((Q (lp.single p k 1)) m)))
    (x : Coeff p) (m : ℤ) :
    Tendsto (fun i => (T i x) m) l (𝓝 ((Q x) m)) :=
  tendsto_operator_coordinate_of_finsupp hp l T Q M hM hQ hbound
    (fun u j => tendsto_operator_coordinate_of_basis_on_finsupp
      l T Q hentry u j) x m

/-- The operator norm is lower semicontinuous under coordinatewise
convergence on every input vector. -/
theorem opNorm_le_of_coordinatewise_limit
    {p : ℝ≥0∞} [Fact (1 ≤ p)]
    {α : Type*} (l : Filter α) [NeBot l]
    (T : α → Coeff p →L[ℂ] Coeff p)
    (S : Coeff p →L[ℂ] Coeff p)
    (M : ℝ) (hM : 0 ≤ M)
    (hbound : ∀ᶠ i in l, ‖T i‖ ≤ M)
    (hpoint : ∀ x : Coeff p, ∀ m : ℤ,
      Tendsto (fun i => (T i x) m) l (𝓝 ((S x) m))) :
    ‖S‖ ≤ M := by
  apply ContinuousLinearMap.opNorm_le_bound _ hM
  intro x
  have hnorm : ∀ᶠ i in l, ‖T i x‖ ≤ M * ‖x‖ := by
    filter_upwards [hbound] with i hi
    exact (T i).le_of_opNorm_le hi x
  have hlim : Tendsto (fun i => ((T i x : Coeff p) : ℤ → ℂ))
      l (𝓝 (S x : ℤ → ℂ)) :=
    tendsto_pi_nhds.mpr (hpoint x)
  exact lp.norm_le_of_tendsto hnorm hlim

end NLS.Coeff
