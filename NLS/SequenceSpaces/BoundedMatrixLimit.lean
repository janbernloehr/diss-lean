import NLS.SequenceSpaces.FiniteCoefficients
import Mathlib.LinearAlgebra.Finsupp.LinearCombination

/-!
# Bounded operators from entrywise limits on a basis

Uniformly bounded operators on a finite-exponent `ℓᵖ` space whose
basis columns converge coordinatewise determine a bounded limit
operator. The proof first takes limits on finite coefficient vectors,
then extends the resulting bounded linear map by density.
-/

noncomputable section
open Filter Topology
open scoped ENNReal
namespace NLS.Coeff

set_option maxHeartbeats 1000000 in
theorem exists_bounded_operator_of_entrywise_basis_limit
    {p : ℝ≥0∞} [Fact (1 ≤ p)] (hp : p ≠ ⊤)
    {α : Type*} (l : Filter α) [NeBot l]
    (T : α → Coeff p →L[ℂ] Coeff p)
    (M : ℝ) (hM : 0 ≤ M) (hbound : ∀ᶠ i in l, ‖T i‖ ≤ M)
    (v : ℤ → Coeff p)
    (hentry : ∀ m k : ℤ,
      Tendsto (fun i => (T i (lp.single p k 1)) m) l (𝓝 (v k m))) :
    ∃ Q : Coeff p →L[ℂ] Coeff p,
      ‖Q‖ ≤ M ∧ ∀ k : ℤ, Q (lp.single p k 1) = v k := by
  classical
  let L₀ : (ℤ →₀ ℂ) →ₗ[ℂ] Coeff p := Finsupp.linearCombination ℂ v
  let e (k : ℤ) : Coeff p := lp.single p k 1
  have hinput : ofFinsupp (p := p) =
      Finsupp.linearCombination ℂ e := by
    apply Finsupp.lhom_ext
    intro k z
    ext m
    by_cases hmk : m = k
    · subst m
      simp [Finsupp.linearCombination_single, ofFinsupp_apply,
        e, lp.single_apply]
    · simp [Finsupp.linearCombination_single, ofFinsupp_apply,
        e, lp.single_apply, hmk]
  have hlim (u : ℤ →₀ ℂ) : Tendsto
      (fun i => ((T i (ofFinsupp u) : Coeff p) : ℤ → ℂ))
      l (𝓝 (L₀ u : ℤ → ℂ)) := by
    rw [tendsto_pi_nhds]
    intro m
    have hterm (k : ℤ) : Tendsto
        (fun i => u k * (T i (e k)) m) l
        (𝓝 (u k * (v k) m)) := by
      exact (hentry m k).const_mul (u k)
    have hsum := tendsto_finsetSum u.support (fun k _ => hterm k)
    convert hsum using 1
    · ext i
      rw [show ofFinsupp (p := p) u =
        (Finsupp.linearCombination ℂ e) u from congrArg (· u) hinput]
      simp only [Finsupp.linearCombination_apply, Finsupp.sum,
        map_sum, map_smul, lp.coeFn_sum, Finset.sum_apply,
        lp.coeFn_smul, Pi.smul_apply, smul_eq_mul]
    · simp only [L₀, Finsupp.linearCombination_apply, Finsupp.sum,
        lp.coeFn_sum, Finset.sum_apply, lp.coeFn_smul,
        Pi.smul_apply, smul_eq_mul]
  have hLbound (u : ℤ →₀ ℂ) :
      ‖L₀ u‖ ≤ M * ‖ofFinsupp (p := p) u‖ := by
    have hfamily : ∀ᶠ i in l,
        ‖T i (ofFinsupp u)‖ ≤ M * ‖ofFinsupp (p := p) u‖ := by
      filter_upwards [hbound] with i hi
      exact (T i).le_of_opNorm_le hi _
    exact lp.norm_le_of_tendsto hfamily (hlim u)
  let Q : Coeff p →L[ℂ] Coeff p :=
    L₀.extendOfNorm (ofFinsupp (p := p))
  have hQnorm : ‖Q‖ ≤ M := by
    exact LinearMap.opNorm_extendOfNorm_le
      (f := L₀) (e := ofFinsupp (p := p))
      (denseRange_ofFinsupp hp) hM hLbound
  refine ⟨Q,hQnorm,?_⟩
  intro k
  have heq : ofFinsupp (p := p) (Finsupp.single k 1) = e k := by
    rw [hinput]
    simp
  have hQe := LinearMap.extendOfNorm_eq
    (denseRange_ofFinsupp hp) ⟨M,hLbound⟩ (Finsupp.single k 1)
  rw [heq] at hQe
  simpa only [Q,L₀, Finsupp.linearCombination_single, one_smul] using hQe

end NLS.Coeff
