import NLS.DifferentialPolynomial.IntegrationByPartsReduction
import Mathlib.Tactic.Choose

/-! # Integration by parts without a common charge grading

The scalar Miura potential mixes different field counts. Reducing each
monomial with its own gradings supplies one reduction for their sum while
retaining the original total-derivative bound.
-/
noncomputable section
open MvPolynomial
namespace NLS.DifferentialPolynomial

theorem exists_jet_reduction_of_derivativeOrder (m : ℕ) (hm : 1 ≤ m)
    (p : Polynomial) (D : ℤ) (hD : D ≤ 2*(m : ℤ)-2) (hp : DerivativeOrderLE p D) :
    ∃ q r : Polynomial, p = q+spatialDerivative r ∧ JetOrderLE q (m-1) ∧ DerivativeOrderLE q D := by
  classical
  have hex (t : Monomial) : ∃ q r : Polynomial,
      MvPolynomial.monomial t (p.coeff t) = q+spatialDerivative r ∧
        JetOrderLE q (m-1) ∧ DerivativeOrderLE q D := by
    by_cases ht : t ∈ p.support
    · obtain ⟨k,hk⟩ := exists_jetOrderLE (MvPolynomial.monomial t (p.coeff t))
      obtain ⟨q,r,he,hq,_,_,hd⟩ := hasJetReduction_of_jetOrder m hm
        (Finsupp.weight totalWeight t) (Finsupp.weight fieldCharge t) D hD k
        (MvPolynomial.monomial t (p.coeff t)) hk
        (isWeightedHomogeneous_monomial _ _ _ rfl)
        (isWeightedHomogeneous_monomial _ _ _ rfl) (Supported.monomial _ _ (hp t ht))
      exact ⟨q,r,he,hq,hd⟩
    · refine ⟨0,0,?_,JetOrderLE.zero _,DerivativeOrderLE.zero _⟩
      simp [MvPolynomial.notMem_support_iff.mp ht]
  choose q r he hq hd using hex
  refine ⟨∑ t ∈ p.support, q t, ∑ t ∈ p.support, r t, ?_,
    JetOrderLE.sum _ _ (fun t _ => hq t), DerivativeOrderLE.sum _ _ (fun t _ => hd t)⟩
  calc
    p = ∑ t ∈ p.support, MvPolynomial.monomial t (p.coeff t) := p.as_sum
    _ = ∑ t ∈ p.support, (q t+spatialDerivative (r t)) :=
      Finset.sum_congr rfl (fun t _ => he t)
    _ = _ := by rw [Finset.sum_add_distrib, map_sum]

end NLS.DifferentialPolynomial
