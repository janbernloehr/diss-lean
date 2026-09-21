import NLS.ZakharovShabat.UniformSmallCanonicalRelativeProducts
import NLS.ZakharovShabat.CanonicalDeletedProductLp

/-! # Uniformly small remaining-product errors
Maximum modulus fills the removable free center, and Cauchy's estimate
controls derivatives on the smaller disc. Both estimates have a common
potential neighborhood and signed-index cutoff for each tolerance.
-/

noncomputable section
open Set Metric
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- Small relative-product errors bound the entire remaining-product error on one closed disc. -/
theorem norm_deletedPairError_le_of_small_relativeProducts (hp : p ≠ ⊤) (a b : Coeff p)
    (n : ℤ) {C δ : ℝ} (hC : 0 ≤ C) (hδ : 0 ≤ δ)
    (hq : ∀ z : ℂ, ‖z-(Real.pi : ℂ)*n‖ ≤ Real.pi/2 → ‖freeSineQuotient n z‖ ≤ C)
    (hprod : ∀ z : ℂ, ‖z-(Real.pi : ℂ)*n‖ ≤ Real.pi/2 →
      ‖freeDiscRelativeProduct a n z-1‖ ≤ δ ∧ ‖freeDiscRelativeProduct b n z-1‖ ≤ δ)
    (z : ℂ) (hz : ‖z-(Real.pi : ℂ)*n‖ ≤ Real.pi/2) :
    ‖deletedPairError a b n z‖ ≤ C^2*((1+δ)*δ+δ) := by
  let A : Coeff p := lp.single p n (δ : ℂ)
  have hAn : ‖A n‖ = δ := by simp [A,lp.single_apply,Complex.norm_real,Real.norm_of_nonneg hδ]
  have hA : ‖A‖ = δ := by
    rw [lp.norm_single (zero_lt_one.trans_le (Fact.out : 1 ≤ p)),Complex.norm_real,Real.norm_of_nonneg hδ]
  apply NLS.ComplexAnalysis.norm_le_of_sphere_bound (differentiable_deletedPairError hp a b n)
    ((Real.pi : ℂ)*n) (half_pos Real.pi_pos) _ _ hz
  intro w hw
  have hw' : ‖w-(Real.pi : ℂ)*n‖ ≤ Real.pi/2 :=
    (show ‖w-(Real.pi : ℂ)*n‖ = Real.pi/2 by simpa only [mem_sphere,dist_eq_norm] using hw).le
  have he := norm_deletedPairError_le_offLattice hp a b A A hC n w
    (freeHalfSphere_notMem_freeLattice n hw) (hq w hw')
    (by rw [hAn]; exact (hprod w hw').1) (by rw [hAn]; exact (hprod w hw').2)
  simpa only [norm_deletedPairErrorMajorant_apply,hAn,hA] using he

/-- Values and derivatives of the canonical remaining-product error are locally uniformly small. -/
theorem exists_uniform_small_canonicalDeletedPairErrors (hp : p ≠ ⊤) (hp1 : 1 < p)
    (φ : PairSpace p) {ε : ℝ} (hε : 0 < ε) :
    ∃ N : ℕ, 0 < N ∧ ∃ U : Set (PairSpace p), IsOpen U ∧ Convex ℝ U ∧ φ ∈ U ∧ 0 ∈ U ∧
      ∀ ψ ∈ U, ∀ heven : ψ ∈ pairParitySubspace 0, ∀ n : ℤ, N < n.natAbs →
        (∀ z : ℂ, ‖z-(Real.pi : ℂ)*n‖ ≤ Real.pi/2 → ‖canonicalDeletedPairError hp hp1 ψ heven n z‖ ≤ ε) ∧
        ∀ z : ℂ, ‖z-(Real.pi : ℂ)*n‖ ≤ Real.pi/4 →
          ‖deriv (canonicalDeletedPairError hp hp1 ψ heven n) z‖ ≤ (4/Real.pi)*ε := by
  obtain ⟨C,hC,hq⟩ := exists_bound_freeSineQuotient (Real.pi/2)
  let δ := min 1 (ε/(3*(C^2+1)))
  have hδ : 0 < δ := lt_min zero_lt_one (by positivity)
  have hδ1 : δ ≤ 1 := min_le_left _ _
  have hδε : δ*(3*(C^2+1)) ≤ ε := (le_div_iff₀ (by positivity)).mp (min_le_right _ _)
  have hb : C^2*((1+δ)*δ+δ) ≤ ε := by
    have hsq : δ^2 ≤ δ := by nlinarith
    have hmul := mul_le_mul_of_nonneg_left hsq (sq_nonneg C)
    nlinarith [sq_nonneg C]
  obtain ⟨N,hN,U,ho,hc,hφ,h0,h⟩ := exists_uniform_small_canonicalRelativeProducts hp hp1 φ hδ
  refine ⟨N,hN,U,ho,hc,hφ,h0,fun ψ hψ heven n hn => ?_⟩
  have hv (z : ℂ) (hz : ‖z-(Real.pi : ℂ)*n‖ ≤ Real.pi/2) :
      ‖canonicalDeletedPairError hp hp1 ψ heven n z‖ ≤ ε := by
    rw [canonicalDeletedPairError_eq]
    exact (norm_deletedPairError_le_of_small_relativeProducts hp _ _ n hC hδ.le (hq n)
      (fun w hw => ⟨(h ψ hψ heven n hn w hw).1.le,(h ψ hψ heven n hn w hw).2.le⟩) z hz).trans hb
  refine ⟨hv,fun z hz => ?_⟩
  have hd : Differentiable ℂ (canonicalDeletedPairError hp hp1 ψ heven n) := by
    rw [canonicalDeletedPairError_eq]
    exact differentiable_deletedPairError hp _ _ n
  have he := NLS.ComplexAnalysis.norm_deriv_le_of_closedDisc_bound hd ((Real.pi : ℂ)*n)
    (by linarith [Real.pi_pos] : Real.pi/4 < Real.pi/2) ε hv hz
  convert he using 1
  ring

end NLS.ZakharovShabat
