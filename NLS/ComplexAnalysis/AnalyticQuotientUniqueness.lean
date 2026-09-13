import NLS.ComplexAnalysis.EqualOrderQuotient

/-!
# Uniqueness and products of filled analytic quotients

An analytic factorization determines the filled values at every common zero.
This also makes the quotient compatible with multiplication of numerators
and denominators.
-/

noncomputable section
open Filter Topology
namespace NLS.ComplexAnalysis

/-- A finite-order analytic germ is nonzero in a punctured neighborhood. -/
theorem eventually_ne_zero_of_finite_analyticOrder {g : ℂ → ℂ} {z : ℂ}
    (hg : AnalyticAt ℂ g z) (hfin : analyticOrderAt g z ≠ ⊤) :
    ∀ᶠ w in 𝓝[≠] z, g w ≠ 0 := by
  obtain ⟨u,hu,hune,he⟩ := hg.analyticOrderAt_ne_top.mp hfin
  filter_upwards [he.filter_mono nhdsWithin_le_nhds,
    (hu.continuousAt.eventually_ne hune).filter_mono nhdsWithin_le_nhds,
    self_mem_nhdsWithin] with w hw hwu hwz
  rw [hw,smul_eq_mul]
  exact mul_ne_zero (pow_ne_zero _ (sub_ne_zero.mpr hwz)) hwu

/-- Every entire factorization agrees with the filled quotient, even at common zeros. -/
theorem analyticQuotient_eq_of_factorization {f g u : ℂ → ℂ}
    (hf : AnalyticOnNhd ℂ f Set.univ) (hg : AnalyticOnNhd ℂ g Set.univ)
    (ho : ∀ z, analyticOrderAt f z = analyticOrderAt g z)
    (hfin : ∀ z, analyticOrderAt g z ≠ ⊤)
    (hu : AnalyticOnNhd ℂ u Set.univ) (he : ∀ z, u z*g z = f z) : analyticQuotient f g = u := by
  funext z
  have haq := analyticOnNhd_analyticQuotient hf hg ho hfin z (Set.mem_univ _)
  have hnear : analyticQuotient f g =ᶠ[𝓝[≠] z] u := by
    filter_upwards [eventually_ne_zero_of_finite_analyticOrder (hg z (Set.mem_univ _)) (hfin z)] with w hw
    apply mul_right_cancel₀ hw
    exact (analyticQuotient_mul hf hg ho w).trans (he w).symm
  exact tendsto_nhds_unique_of_eventuallyEq (l := 𝓝[≠] z)
    haq.continuousAt.continuousWithinAt (hu z (Set.mem_univ _)).continuousAt.continuousWithinAt hnear

/-- Multiplying both analytic factorizations multiplies their filled quotient factors. -/
theorem analyticQuotient_mul_distrib {f₁ f₂ g₁ g₂ : ℂ → ℂ}
    (hf₁ : AnalyticOnNhd ℂ f₁ Set.univ) (hf₂ : AnalyticOnNhd ℂ f₂ Set.univ)
    (hg₁ : AnalyticOnNhd ℂ g₁ Set.univ) (hg₂ : AnalyticOnNhd ℂ g₂ Set.univ)
    (ho₁ : ∀ z, analyticOrderAt f₁ z = analyticOrderAt g₁ z)
    (ho₂ : ∀ z, analyticOrderAt f₂ z = analyticOrderAt g₂ z)
    (hfin₁ : ∀ z, analyticOrderAt g₁ z ≠ ⊤) (hfin₂ : ∀ z, analyticOrderAt g₂ z ≠ ⊤) :
    analyticQuotient (f₁*f₂) (g₁*g₂) = analyticQuotient f₁ g₁*analyticQuotient f₂ g₂ := by
  have ho : ∀ z, analyticOrderAt (f₁*f₂) z = analyticOrderAt (g₁*g₂) z := by
    intro z
    rw [analyticOrderAt_mul (hf₁ z (Set.mem_univ _)) (hf₂ z (Set.mem_univ _)),
      analyticOrderAt_mul (hg₁ z (Set.mem_univ _)) (hg₂ z (Set.mem_univ _)),ho₁ z,ho₂ z]
  have hfin : ∀ z, analyticOrderAt (g₁*g₂) z ≠ ⊤ := by
    intro z
    rw [analyticOrderAt_mul (hg₁ z (Set.mem_univ _)) (hg₂ z (Set.mem_univ _))]
    exact WithTop.add_ne_top.mpr ⟨hfin₁ z,hfin₂ z⟩
  apply analyticQuotient_eq_of_factorization (hf₁.mul hf₂) (hg₁.mul hg₂) ho hfin
    ((analyticOnNhd_analyticQuotient hf₁ hg₁ ho₁ hfin₁).mul (analyticOnNhd_analyticQuotient hf₂ hg₂ ho₂ hfin₂))
  intro z
  calc
    _ = (analyticQuotient f₁ g₁ z*g₁ z)*(analyticQuotient f₂ g₂ z*g₂ z) := by ring
    _ = _ := by rw [analyticQuotient_mul hf₁ hg₁ ho₁,analyticQuotient_mul hf₂ hg₂ ho₂]

end NLS.ComplexAnalysis
