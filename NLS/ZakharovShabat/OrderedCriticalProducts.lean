import NLS.ZakharovShabat.CriticalPointOrder
import NLS.ZakharovShabat.DiscriminantDerivativeProduct

/-!
# Ordered critical sequences with locally uniform displacement bounds

Sorting changes only a bounded finite head. Thus the complete ordered roots
retain lp displacements, a common potential-neighborhood norm bound, and
the exact normalized derivative product.
-/

noncomputable section
open Set Complex
open NLS.ComplexAnalysis
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]
variable {hp : p ≠ ⊤} {hp1 : 1 < p} {φ : PairSpace p} {hφ : φ ∈ pairParitySubspace 0}
variable {N : ℕ} {ξ : ℤ → ℂ}

/-- Sorting the central roots preserves lp and gives a cutoff-only increase in the displacement bound. -/
theorem CriticalPointLabeling.exists_ordered_displacement (h : CriticalPointLabeling hp hp1 φ hφ N ξ)
    (a : Coeff p) (ha : ∀ n, ξ n = (Real.pi : ℂ)*n+a n) :
    ∃ η : ℤ → ℂ, ∃ b : Coeff p, CriticalPointLabeling hp hp1 φ hφ N η ∧
      Monotone (fun n => complexLexKey (η n)) ∧ (∀ n, η n = (Real.pi : ℂ)*n+b n) ∧
      ‖b‖ ≤ (Finset.Icc (-(N : ℤ)) N).card*(centralCircleRadius N+Real.pi*N)+‖a‖ ∧
      (∀ n : ℤ, N < n.natAbs → η n = ξ n) := by
  obtain ⟨α,hα,hs⟩ := h.exists_ordered_relabeling
  have hlp : Memℓp (fun n => ξ n-(Real.pi : ℂ)*n) p := by
    simpa only [ha, add_sub_cancel_left] using (show Memℓp (fun n => a n) p from lp.memℓp a)
  let b : Coeff p := ⟨_,memℓp_spliceCentralRoots N α ξ hlp⟩
  refine ⟨spliceCentralRoots N α ξ,b,hα,hs,?_,?_,?_⟩
  · intro n
    change spliceCentralRoots N α ξ n = (Real.pi : ℂ)*n+(spliceCentralRoots N α ξ n-(Real.pi : ℂ)*n)
    ring
  · apply Coeff.norm_le_of_eq_outside_finset b a (Finset.Icc (-(N : ℤ)) N)
      (centralCircleRadius N+Real.pi*N)
    · intro n hn
      exact norm_centralCriticalLabel_displacement_le hp hp1 φ hφ N _ hα.central n
        (by simp only [Finset.mem_Icc] at hn; omega)
    · intro n hn
      have hn' : N < n.natAbs := by simp only [Finset.mem_Icc] at hn; omega
      simp only [b, spliceCentralRoots, if_pos hn', ha, add_sub_cancel_left]
  · intro n hn
    simp only [spliceCentralRoots, if_pos hn]

/-- One common neighborhood supplies ordered critical roots, bounded displacements, and exact products. -/
theorem exists_uniform_ordered_critical_products (hp : p ≠ ⊤) (hp1 : 1 < p) (φ : PairSpace p) :
    ∃ N : ℕ, 0 < N ∧ ∃ U : Set (PairSpace p), IsOpen U ∧ Convex ℝ U ∧ φ ∈ U ∧ 0 ∈ U ∧
      ∃ R : ℝ, 0 ≤ R ∧ ∀ ψ ∈ U, ∀ hψ : ψ ∈ pairParitySubspace 0,
        ∃ ξ : ℤ → ℂ, ∃ a : Coeff p, CriticalPointLabeling hp hp1 ψ hψ N ξ ∧
          Monotone (fun n => complexLexKey (ξ n)) ∧
          (∀ n, ξ n = (Real.pi : ℂ)*n+a n) ∧ ‖a‖ ≤ R ∧
          (∀ z, deriv (canonicalDiscriminant hp ψ) z = entireSingleSpectralProduct ξ z) ∧
          TendstoLocallyUniformlyOn (fun M z => singleSpectralPartialProduct ξ z M)
            (deriv (canonicalDiscriminant hp ψ)) Filter.atTop Set.univ := by
  obtain ⟨N,hN,U,ho,hc,hφ,h0,R,hR,h⟩ := exists_uniform_critical_displacements hp hp1 φ
  let B := (Finset.Icc (-(N : ℤ)) N).card*(centralCircleRadius N+Real.pi*N)
  have hB : 0 ≤ B := mul_nonneg (by positivity)
    (add_nonneg (centralCircleRadius_pos N).le (by positivity))
  refine ⟨N,hN,U,ho,hc,hφ,h0,B+R,add_nonneg hB hR,?_⟩
  intro ψ hψ heven
  obtain ⟨ξ,a,hlabel,he,ha⟩ := h ψ hψ heven
  obtain ⟨η,b,hη,hs,hb,hbn,_⟩ := hlabel.exists_ordered_displacement a he
  have hlp : Memℓp (fun n => η n-(Real.pi : ℂ)*n) p := by
    simpa only [hb, add_sub_cancel_left] using (show Memℓp (fun n => b n) p from lp.memℓp b)
  exact ⟨η,b,hη,hs,hb,hbn.trans (add_le_add le_rfl ha),
    fun z => (hη.product_eq_derivative hlp z).symm,hη.tendstoLocallyUniformlyOn_derivative_product hlp⟩

/-- Every even finite-p potential has a complete ordered critical sequence with lp displacement. -/
theorem exists_ordered_criticalPointLabeling_memℓp (hp : p ≠ ⊤) (hp1 : 1 < p)
    (φ : PairSpace p) (hφ : φ ∈ pairParitySubspace 0) :
    ∃ N : ℕ, ∃ ξ : ℤ → ℂ, CriticalPointLabeling hp hp1 φ hφ N ξ ∧
      Monotone (fun n => complexLexKey (ξ n)) ∧ Memℓp (fun n => ξ n-(Real.pi : ℂ)*n) p := by
  obtain ⟨N,_,U,_,_,hmem,_,R,_,h⟩ := exists_uniform_ordered_critical_products hp hp1 φ
  obtain ⟨ξ,a,hξ,hs,ha,_,_,_⟩ := h φ hmem hφ
  refine ⟨N,ξ,hξ,hs,?_⟩
  simpa only [ha, add_sub_cancel_left] using (show Memℓp (fun n => a n) p from lp.memℓp a)

end NLS.ZakharovShabat
