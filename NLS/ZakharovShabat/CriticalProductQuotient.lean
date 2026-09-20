import NLS.ZakharovShabat.CriticalPointProductOrders
import NLS.ZakharovShabat.EntireFreeDiscBounds

/-!
# The entire critical-product quotient

Equal finite orders fill every common zero. The quotient tends to one on
the free-disc exterior, and maximum modulus propagates an exterior bound
to the whole complex plane.
-/

noncomputable section
open Filter Topology
open scoped ENNReal
open NLS.ComplexAnalysis
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The entire critical product divided by the discriminant derivative, with common zeros filled. -/
def criticalProductQuotient (hp : p ≠ ⊤) (φ : PairSpace p) (ξ : ℤ → ℂ) : ℂ → ℂ :=
  analyticQuotient (entireSingleSpectralProduct ξ) (deriv (canonicalDiscriminant hp φ))

variable {hp : p ≠ ⊤} {hp1 : 1 < p} {φ : PairSpace p} {hφ : φ ∈ pairParitySubspace 0}
variable {N : ℕ} {ξ : ℤ → ℂ}

/-- Matching multiplicities remove all quotient singularities. -/
theorem CriticalPointLabeling.analyticOnNhd_quotient (h : CriticalPointLabeling hp hp1 φ hφ N ξ)
    (hξ : Memℓp (fun n => ξ n-(Real.pi : ℂ)*n) p) :
    AnalyticOnNhd ℂ (criticalProductQuotient hp φ ξ) Set.univ :=
  analyticOnNhd_analyticQuotient (analyticOnNhd_entireSingleSpectralProduct hp ξ hξ)
    (analyticOnNhd_discriminant_derivative hp hp1 φ hφ) (h.product_analyticOrderAt hξ)
    (analyticOrderAt_discriminant_derivative_ne_top hp hp1 φ hφ)

/-- The filled quotient is nonzero even at multiple critical points. -/
theorem CriticalPointLabeling.quotient_ne_zero (h : CriticalPointLabeling hp hp1 φ hφ N ξ)
    (hξ : Memℓp (fun n => ξ n-(Real.pi : ℂ)*n) p) (z : ℂ) :
    criticalProductQuotient hp φ ξ z ≠ 0 :=
  analyticQuotient_ne_zero (analyticOnNhd_entireSingleSpectralProduct hp ξ hξ)
    (analyticOnNhd_discriminant_derivative hp hp1 φ hφ) (h.product_analyticOrderAt hξ)
    (analyticOrderAt_discriminant_derivative_ne_top hp hp1 φ hφ) z

/-- Both free-normalized functions tend to one, so their filled quotient does as well. -/
theorem CriticalPointLabeling.tendsto_quotient_of_separated {α : Type*} {l : Filter α}
    (_h : CriticalPointLabeling hp hp1 φ hφ N ξ)
    (hξ : Memℓp (fun n => ξ n-(Real.pi : ℂ)*n) p)
    (z : α → ℂ) (hescape : Tendsto (fun i => ‖z i‖) l atTop)
    {r : ℝ} (hr : 0 < r) (hrπ : r ≤ Real.pi/4)
    (hsep : ∀ i (n : ℤ), r ≤ ‖z i-(Real.pi : ℂ)*n‖) :
    Tendsto (fun i => criticalProductQuotient hp φ ξ (z i)) l (𝓝 1) := by
  have ht := tendsto_discriminant_derivative_div_free_of_separated hp hp1 φ hφ z hescape hr hrπ hsep
  have hs := tendsto_entireSingleSpectralProduct_div_free_of_separated hp ξ hξ z hescape hr hrπ hsep
  have hratio := hs.div ht (by norm_num : (1 : ℂ) ≠ 0)
  simp only [div_one] at hratio
  apply hratio.congr'
  filter_upwards [ht.eventually_ne (by norm_num : (1 : ℂ) ≠ 0)] with i hi
  have hd : deriv (canonicalDiscriminant hp φ) (z i) ≠ 0 := by
    intro he
    exact hi (by rw [he, zero_div])
  have hf : -2*Complex.sin (z i) ≠ 0 := mul_ne_zero (by norm_num)
    (sin_ne_zero_of_notMem_freeLattice (notMem_freeLattice_of_separated hr (hsep i)))
  rw [criticalProductQuotient, analyticQuotient_eq_div
    (analyticOnNhd_entireSingleSpectralProduct hp ξ hξ)
    (analyticOnNhd_discriminant_derivative hp hp1 φ hφ) _ hd]
  exact div_div_div_cancel_right₀ hf _ _

/-- The exterior limit supplies a global bound for the entire quotient. -/
theorem CriticalPointLabeling.isBounded_quotient (h : CriticalPointLabeling hp hp1 φ hφ N ξ)
    (hξ : Memℓp (fun n => ξ n-(Real.pi : ℂ)*n) p) :
    Bornology.IsBounded (Set.range (criticalProductQuotient hp φ ξ)) := by
  let S := {z : ℂ // ∀ n : ℤ, Real.pi/4 ≤ ‖z-(Real.pi : ℂ)*n‖}
  have ht := h.tendsto_quotient_of_separated hξ (fun z : S => z.val) tendsto_comap
    (by positivity : 0 < Real.pi/4) le_rfl (fun z => z.property)
  obtain ⟨R,hR⟩ := exists_threshold_norm_le_two (fun z : S => ‖z.val‖)
    (fun z : S => criticalProductQuotient hp φ ξ z.val) ht
  apply isBounded_entire_of_bound_off_freeDiscs
    (differentiableOn_univ.mp (h.analyticOnNhd_quotient hξ).differentiableOn)
    (by positivity : 0 < Real.pi/4) le_rfl R 2
  exact fun z hz hsep => hR ⟨z,hsep⟩ hz

end NLS.ZakharovShabat
