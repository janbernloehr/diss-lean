import NLS.ComplexAnalysis.SimplePoleQuotient
import Mathlib.LinearAlgebra.Lagrange
import Mathlib.Analysis.Calculus.Deriv.Polynomial

/-! # Finite interpolation with the actual characteristic residues

An entire characteristic may have infinitely many zeros while a numerator
differs from it in only finitely many factors. A polynomial cross identity
then determines the finite interpolation using the characteristic's actual
derivatives, without prescribing residues or discarding a common tail.
-/
noncomputable section
open Set Complex Filter Topology
namespace NLS.ComplexAnalysis

theorem prod_range_cross_eq_of_tail_eq (A B : ℕ → ℂ) (K N : ℕ)
    (htail : ∀ k, K ≤ k → A k = B k) (hN : K ≤ N) :
    (∏ k ∈ Finset.range N,A k)*(∏ k ∈ Finset.range K,B k) =
      (∏ k ∈ Finset.range K,A k)*(∏ k ∈ Finset.range N,B k) := by
  obtain ⟨j,rfl⟩ := Nat.exists_eq_add_of_le hN
  rw [Finset.prod_range_add,Finset.prod_range_add]
  have he : (∏ k ∈ Finset.range j,A (K+k)) = ∏ k ∈ Finset.range j,B (K+k) :=
    Finset.prod_congr rfl (fun k _ => htail (K+k) (by omega))
  rw [he]
  ring

theorem product_limits_cross_eq_of_tail_eq (A B : ℕ → ℂ) (a b : ℂ) (K : ℕ)
    (hA : Tendsto (fun N => ∏ k ∈ Finset.range N,A k) atTop (𝓝 a))
    (hB : Tendsto (fun N => ∏ k ∈ Finset.range N,B k) atTop (𝓝 b))
    (htail : ∀ k, K ≤ k → A k = B k) :
    a*(∏ k ∈ Finset.range K,B k) = (∏ k ∈ Finset.range K,A k)*b := by
  apply tendsto_nhds_unique (hA.mul_const _) ((hB.const_mul _).congr' ?_)
  filter_upwards [eventually_ge_atTop K] with N hN
  exact (prod_range_cross_eq_of_tail_eq A B K N htail hN).symm

theorem normalize_characteristic_cross_identity (c C D F P A B : ℂ) (hD : D ≠ 0)
    (he : F*(D*P) = A*B) :
    (c*F/C)*P = (c/C/D*A)*B := by
  apply mul_left_cancel₀ hD
  calc
    _ = (c/C)*(F*(D*P)) := by ring
    _ = (c/C)*(A*B) := by rw [he]
    _ = _ := by
      symm
      calc
        _ = (D*D⁻¹)*((c/C)*(A*B)) := by simp only [div_eq_mul_inv];ring
        _ = _ := by rw [mul_inv_cancel₀ hD,one_mul]

theorem sheet_weighted_resolvent_cancel (ψ R s D E μ : ℂ)
    (hR : R ≠ 0) (hD : D ≠ 0) (hE : E ≠ μ) :
    ψ*(R*s/(2*(μ-E)*D))/R = -(1/2 : ℂ)*(ψ*s/(D*(E-μ))) := by
  field_simp [hR,hD,sub_ne_zero.mpr hE,sub_ne_zero.mpr hE.symm]
  ring

theorem characteristic_residue_eq_nodal_weight {ι : Type*} [DecidableEq ι]
    (S : Finset ι) (μ : ι → ℂ) (p : Polynomial ℂ) (f g : ℂ → ℂ)
    (hμ : Set.InjOn μ S) (hf : Differentiable ℂ f) (hg : Differentiable ℂ g)
    (he : ∀ z, f z*(Lagrange.nodal S μ).eval z = p.eval z*g z)
    (hzero : ∀ i ∈ S,g (μ i) = 0) (hsimple : ∀ i ∈ S,deriv g (μ i) ≠ 0)
    (i : ι) (hi : i ∈ S) :
    f (μ i)/deriv g (μ i) = p.eval (μ i)*Lagrange.nodalWeight S μ i := by
  have hleft := (hf (μ i)).hasDerivAt.mul ((Lagrange.nodal S μ).hasDerivAt (μ i))
  have hright := (p.hasDerivAt (μ i)).mul (hg (μ i)).hasDerivAt
  have heq := hleft.unique (hright.congr_of_eventuallyEq (Filter.Eventually.of_forall (fun z => he z)))
  simp only [Lagrange.eval_nodal_at_node hi,hzero i hi,mul_zero,zero_add] at heq
  rw [Lagrange.nodalWeight_eq_eval_derivative_nodal hi]
  have hD : (Lagrange.nodal S μ).derivative.eval (μ i) ≠ 0 := by
    have hn := Lagrange.nodalWeight_ne_zero hμ hi
    rw [Lagrange.nodalWeight_eq_eval_derivative_nodal hi] at hn
    exact fun h => hn (by rw [h,inv_zero])
  field_simp [hsimple i hi,hD]
  simpa only [mul_comm] using heq

theorem finite_characteristic_weighted_interpolation {ι : Type*} [DecidableEq ι]
    (S : Finset ι) (μ : ι → ℂ) (p : Polynomial ℂ) (f g : ℂ → ℂ)
    (hμ : Set.InjOn μ S) (hp : p.degree < S.card)
    (hf : Differentiable ℂ f) (hg : Differentiable ℂ g)
    (he : ∀ z, f z*(Lagrange.nodal S μ).eval z = p.eval z*g z)
    (hzero : ∀ i ∈ S,g (μ i) = 0) (hsimple : ∀ i ∈ S,deriv g (μ i) ≠ 0)
    (z : ℂ) (hz : ∀ i ∈ S,z ≠ μ i) :
    (∑ i ∈ S,f (μ i)*g z/(deriv g (μ i)*(z-μ i))) = f z := by
  have hP : (Lagrange.nodal S μ).eval z ≠ 0 := Lagrange.eval_nodal_not_at_node hz
  have hpval := congrArg (fun q : Polynomial ℂ => q.eval z) (Lagrange.eq_interpolate hμ hp)
  rw [Lagrange.eval_interpolate_not_at_node (r := fun i => p.eval (μ i)) hz] at hpval
  have hsum : (∑ i ∈ S,f (μ i)*g z/(deriv g (μ i)*(z-μ i))) =
      g z*(∑ i ∈ S,Lagrange.nodalWeight S μ i*(z-μ i)⁻¹*p.eval (μ i)) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    have hr := characteristic_residue_eq_nodal_weight S μ p f g hμ hf hg he hzero hsimple i hi
    calc
      _ = (f (μ i)/deriv g (μ i))*g z*(z-μ i)⁻¹ := by simp only [div_eq_mul_inv,mul_inv_rev];ring
      _ = _ := by rw [hr];ring
  rw [hsum]
  apply mul_left_cancel₀ hP
  calc
    _ = g z*((Lagrange.nodal S μ).eval z*
        ∑ i ∈ S,Lagrange.nodalWeight S μ i*(z-μ i)⁻¹*p.eval (μ i)) := by ring
    _ = g z*p.eval z := by rw [← hpval]
    _ = _ := by linear_combination -(he z)

/-- Filled divided differences include every interpolation node itself. -/
theorem finite_characteristic_dslope_interpolation {ι : Type*} [DecidableEq ι]
    (S : Finset ι) (μ : ι → ℂ) (p : Polynomial ℂ) (f g : ℂ → ℂ)
    (hμ : Set.InjOn μ S) (hp : p.degree < S.card)
    (hf : Differentiable ℂ f) (hg : Differentiable ℂ g)
    (he : ∀ z, f z*(Lagrange.nodal S μ).eval z = p.eval z*g z)
    (hzero : ∀ i ∈ S,g (μ i) = 0) (hsimple : ∀ i ∈ S,deriv g (μ i) ≠ 0)
    (z : ℂ) :
    (∑ i ∈ S,f (μ i)*dslope g (μ i) z/deriv g (μ i)) = f z := by
  by_cases hnode : ∃ j ∈ S,z = μ j
  · obtain ⟨j,hj,rfl⟩ := hnode
    rw [Finset.sum_eq_single j]
    · rw [dslope_same,mul_div_cancel_right₀ _ (hsimple j hj)]
    · intro i hi hij
      have hne : μ j ≠ μ i := fun h => hij (hμ hi hj h.symm)
      rw [dslope_of_ne g hne]
      simp only [slope,vsub_eq_sub,smul_eq_mul,hzero j hj,hzero i hi,
        sub_self,mul_zero,zero_div]
    · exact fun h => (h hj).elim
  · have hz : ∀ i ∈ S,z ≠ μ i := by
      intro i hi h;exact hnode ⟨i,hi,h⟩
    rw [← finite_characteristic_weighted_interpolation S μ p f g hμ hp hf hg he hzero hsimple z hz]
    apply Finset.sum_congr rfl
    intro i hi
    rw [dslope_of_ne g (hz i hi)]
    simp only [slope,vsub_eq_sub,smul_eq_mul,hzero i hi,sub_zero]
    simp only [div_eq_mul_inv,mul_inv_rev]
    ring

end NLS.ComplexAnalysis
