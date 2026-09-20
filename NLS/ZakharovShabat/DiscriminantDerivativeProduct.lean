import NLS.ZakharovShabat.CriticalProductQuotient

/-!
# The discriminant derivative product, Lemma 8.5

Equal analytic orders give an entire quotient. Exterior normalization and
maximum modulus bound it globally; Liouville makes it constant and the
escaping free cosine-zero sequence fixes that constant to one.
-/

noncomputable section
open Filter Topology
open scoped ENNReal
open NLS.ComplexAnalysis
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]
variable {hp : p ≠ ⊤} {hp1 : 1 < p} {φ : PairSpace p} {hφ : φ ∈ pairParitySubspace 0}
variable {N : ℕ} {ξ : ℤ → ℂ}

/-- Exterior normalization fixes the entire critical-product quotient to one. -/
theorem CriticalPointLabeling.quotient_eq_one (h : CriticalPointLabeling hp hp1 φ hφ N ξ)
    (hξ : Memℓp (fun n => ξ n-(Real.pi : ℂ)*n) p) (z : ℂ) :
    criticalProductQuotient hp φ ξ z = 1 := by
  have hd := differentiableOn_univ.mp (h.analyticOnNhd_quotient hξ).differentiableOn
  obtain ⟨c,hc⟩ := hd.exists_const_forall_eq_of_bounded (h.isBounded_quotient hξ)
  have ht := h.tendsto_quotient_of_separated hξ freeCosineZero tendsto_norm_freeCosineZero
    (by positivity : 0 < Real.pi/4) le_rfl freeCosineZero_separated
  have he : c = 1 := tendsto_nhds_unique
    (tendsto_const_nhds : Tendsto (fun _ : ℕ => c) atTop (𝓝 c))
    (ht.congr (fun n => hc (freeCosineZero n)))
  exact (hc z).trans he

/-- The normalized entire product over the complete critical sequence equals the derivative everywhere. -/
theorem CriticalPointLabeling.product_eq_derivative (h : CriticalPointLabeling hp hp1 φ hφ N ξ)
    (hξ : Memℓp (fun n => ξ n-(Real.pi : ℂ)*n) p) (z : ℂ) :
    entireSingleSpectralProduct ξ z = deriv (canonicalDiscriminant hp φ) z := by
  have he := analyticQuotient_mul (analyticOnNhd_entireSingleSpectralProduct hp ξ hξ)
    (analyticOnNhd_discriminant_derivative hp hp1 φ hφ) (h.product_analyticOrderAt hξ) z
  change criticalProductQuotient hp φ ξ z * deriv (canonicalDiscriminant hp φ) z =
    entireSingleSpectralProduct ξ z at he
  rw [h.quotient_eq_one hξ z, one_mul] at he
  exact he.symm

/-- The literal normalized critical-root cutoffs converge locally uniformly to the derivative. -/
theorem CriticalPointLabeling.tendstoLocallyUniformlyOn_derivative_product
    (h : CriticalPointLabeling hp hp1 φ hφ N ξ)
    (hξ : Memℓp (fun n => ξ n-(Real.pi : ℂ)*n) p) :
    TendstoLocallyUniformlyOn (fun M z => singleSpectralPartialProduct ξ z M)
      (deriv (canonicalDiscriminant hp φ)) atTop Set.univ :=
  (tendstoLocallyUniformlyOn_entireSingleSpectralProduct hp ξ hξ).congr_right
    (fun z _ => h.product_eq_derivative hξ z)

/-- Every even finite-p potential has the normalized derivative product of Lemma 8.5. -/
theorem exists_discriminant_derivative_product (hp : p ≠ ⊤) (hp1 : 1 < p)
    (φ : PairSpace p) (hφ : φ ∈ pairParitySubspace 0) :
    ∃ N : ℕ, ∃ ξ : ℤ → ℂ, CriticalPointLabeling hp hp1 φ hφ N ξ ∧
      Memℓp (fun n => ξ n-(Real.pi : ℂ)*n) p ∧
      TendstoLocallyUniformlyOn (fun M z => singleSpectralPartialProduct ξ z M)
        (deriv (canonicalDiscriminant hp φ)) atTop Set.univ ∧
      ∀ z, deriv (canonicalDiscriminant hp φ) z = entireSingleSpectralProduct ξ z := by
  obtain ⟨N,ξ,h,hξ⟩ := exists_criticalPointLabeling_memℓp hp hp1 φ hφ
  exact ⟨N,ξ,h,hξ,h.tendstoLocallyUniformlyOn_derivative_product hξ,
    fun z => (h.product_eq_derivative hξ z).symm⟩

/-- One potential neighborhood supplies bounded lp critical displacements and the exact derivative product. -/
theorem exists_uniform_discriminant_derivative_products (hp : p ≠ ⊤) (hp1 : 1 < p) (φ : PairSpace p) :
    ∃ N : ℕ, 0 < N ∧ ∃ U : Set (PairSpace p), IsOpen U ∧ Convex ℝ U ∧ φ ∈ U ∧ 0 ∈ U ∧
      ∃ R : ℝ, 0 ≤ R ∧ ∀ ψ ∈ U, ∀ hψ : ψ ∈ pairParitySubspace 0,
        ∃ ξ : ℤ → ℂ, ∃ a : Coeff p, CriticalPointLabeling hp hp1 ψ hψ N ξ ∧
          (∀ n, ξ n = (Real.pi : ℂ)*n+a n) ∧ ‖a‖ ≤ R ∧
          (∀ z, deriv (canonicalDiscriminant hp ψ) z = entireSingleSpectralProduct ξ z) ∧
          TendstoLocallyUniformlyOn (fun M z => singleSpectralPartialProduct ξ z M)
            (deriv (canonicalDiscriminant hp ψ)) atTop Set.univ := by
  obtain ⟨N,hN,U,ho,hc,hφ,h0,R,hR,h⟩ := exists_uniform_critical_displacements hp hp1 φ
  refine ⟨N,hN,U,ho,hc,hφ,h0,R,hR,?_⟩
  intro ψ hψ heven
  obtain ⟨ξ,a,hlabel,he,ha⟩ := h ψ hψ heven
  have hlp : Memℓp (fun n => ξ n-(Real.pi : ℂ)*n) p := by
    have he' : (fun n => ξ n-(Real.pi : ℂ)*n) = fun n => a n := by
      funext n
      rw [he n, add_sub_cancel_left]
    rw [he']
    exact a.property
  exact ⟨ξ,a,hlabel,he,ha,fun z => (hlabel.product_eq_derivative hlp z).symm,
    hlabel.tendstoLocallyUniformlyOn_derivative_product hlp⟩

end NLS.ZakharovShabat
