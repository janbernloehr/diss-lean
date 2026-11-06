import NLS.KdV.HillUniformOffDiagonalPhases

noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology
open NLS.ComplexAnalysis NLS.ZakharovShabat
open scoped ENNReal ComplexConjugate Classical

namespace NLS.KdV



private theorem analytic_tsum_hill_kernel_bound
    {X : Type} [NormedAddCommGroup X] [NormedSpace ℂ X]
    (f : ℕ → X → ℂ) (D : Set X) (hD : IsOpen D) (n : ℕ) (M : ℝ) (hM : 0≤M)
    (ha : ∀ k : ℕ, AnalyticOnNhd ℂ (f k) D)
    (hb : ∀ k : ℕ, ∀ x∈D, ‖f k x‖≤M*hillOffDiagonalPeriodKernel n (k : ℤ)) :
    AnalyticOnNhd ℂ (fun x => ∑' k : ℕ, f k x) D ∧
      ∀ x∈D, ‖∑' k : ℕ, f k x‖≤4*M/Real.pi^2 := by
  let b : ℕ → ℝ := fun k => M*hillOffDiagonalPeriodKernel n (k : ℤ)
  have hknat : Summable (fun k : ℕ => hillOffDiagonalPeriodKernel n (k : ℤ)) :=
    (summable_hillOffDiagonalPeriodKernel n).comp_injective Int.ofNat_injective
  have hsum : Summable b := hknat.mul_left M
  refine ⟨analyticOnNhd_tsum_of_summable_uniform_bound f D hD ha b hsum hb,?_⟩
  intro x hx
  have hs : Summable (fun k : ℕ => ‖f k x‖) := hsum.of_nonneg_of_le (fun _ => norm_nonneg _) (fun k => hb k x hx)
  have hnat : (∑' k : ℕ, hillOffDiagonalPeriodKernel n (k : ℤ))≤∑' m : ℤ, hillOffDiagonalPeriodKernel n m :=
    tsum_comp_le_tsum_of_inj (summable_hillOffDiagonalPeriodKernel n) (hillOffDiagonalPeriodKernel_nonneg n) Int.ofNat_injective
  apply (norm_tsum_le_tsum_norm hs).trans
  have hh := hs.tsum_le_tsum (fun k => hb k x hx) hsum
  rw [show (∑' k : ℕ, b k)=M*(∑' k : ℕ, hillOffDiagonalPeriodKernel n (k : ℤ)) from tsum_mul_left] at hh
  exact (hh.trans (mul_le_mul_of_nonneg_left hnat hM)).trans
    ((mul_le_mul_of_nonneg_left (tsum_hillOffDiagonalPeriodKernel_le n) hM).trans_eq (by ring))

private def hillKernelSeriesPullback
    {X Y : Type} [NormedAddCommGroup X] [NormedSpace ℂ X]
    [NormedAddCommGroup Y] [NormedSpace ℂ Y]
    (β : ℕ → Y → ℂ) (T : X →L[ℂ] Y) : X → ℂ := fun x => ∑' k : ℕ, β k (T x)

private theorem analytic_tsum_hill_kernel_pullback
    {X Y : Type} [NormedAddCommGroup X] [NormedSpace ℂ X]
    [NormedAddCommGroup Y] [NormedSpace ℂ Y]
    (β : ℕ → Y → ℂ) (T : X →L[ℂ] Y) (U : Set Y) (hU : IsOpen U)
    (L M : ℝ) (n : ℕ) (hM : 0≤M)
    (ha : ∀ k : ℕ, AnalyticOnNhd ℂ (β k) U)
    (hb : ∀ x : X, ‖x‖≤L → T x∈U → ∀ k : ℕ, ‖β k (T x)‖≤M*hillOffDiagonalPeriodKernel n (k : ℤ)) :
    AnalyticOnNhd ℂ (hillKernelSeriesPullback β T) {x : X | T x∈U ∧ ‖x‖<L} ∧
      ∀ x∈{x : X | T x∈U ∧ ‖x‖<L}, ‖hillKernelSeriesPullback β T x‖≤4*M/Real.pi^2 := by
  apply analytic_tsum_hill_kernel_bound _ _ ((hU.preimage T.continuous).inter (isOpen_lt continuous_norm continuous_const)) n M hM
  · intro k x hx
    exact (ha k _ hx.1).comp (T.analyticAt x)
  · intro k x hx
    exact hb x hx.2.le hx.1 k


/-- The common coefficient neighborhood intersected with a bounded
native source domain, written without an implicit map coercion. -/
def hillNativeSourceDomain (w : SpectralWeight) (p0 : Coeff 2) (δ L : ℝ) :
    Set (WeightedCoeff w.doubleIndex.toWeight 2) :=
  {r | hillPeriodOneCoefficientMap w r∈ball p0 δ ∧ ‖r‖<L}

theorem mem_hillNativeSourceDomain (w : SpectralWeight) (p0 : Coeff 2) (δ L : ℝ)
    (r : WeightedCoeff w.doubleIndex.toWeight 2) :
    r∈hillNativeSourceDomain w p0 δ L ↔ hillPeriodOneCoefficientMap w r∈ball p0 δ ∧ ‖r‖<L := Iff.rfl

private theorem isOpen_linear_norm_domain
    {X Y : Type} [NormedAddCommGroup X] [NormedSpace ℂ X]
    [NormedAddCommGroup Y] [NormedSpace ℂ Y]
    (T : X →L[ℂ] Y) (U : Set Y) (hU : IsOpen U) (L : ℝ) :
    IsOpen {x : X | T x∈U ∧ ‖x‖<L} :=
  (hU.preimage T.continuous).inter (isOpen_lt continuous_norm continuous_const)

theorem isOpen_hillNativeSourceDomain (w : SpectralWeight) (p0 : Coeff 2) (δ L : ℝ) :
    IsOpen (hillNativeSourceDomain w p0 δ L) :=
  isOpen_linear_norm_domain (hillPeriodOneCoefficientMap w) (ball p0 δ) isOpen_ball L

private theorem analytic_linear_norm_pullback
    {X Y : Type} [NormedAddCommGroup X] [NormedSpace ℂ X]
    [NormedAddCommGroup Y] [NormedSpace ℂ Y]
    (T : X →L[ℂ] Y) (f : Y → ℂ) (U : Set Y) (hf : AnalyticOnNhd ℂ f U) (L : ℝ) :
    AnalyticOnNhd ℂ (fun x : X => f (T x)) {x : X | T x∈U ∧ ‖x‖<L} := by
  intro x hx
  exact (hf _ hx.1).comp (T.analyticAt x)

theorem analyticOnNhd_hillNativeSource_pullback
    (w : SpectralWeight) (p0 : Coeff 2) (δ L : ℝ) (f : Coeff 2 → ℂ)
    (hf : AnalyticOnNhd ℂ f (ball p0 δ)) :
    AnalyticOnNhd ℂ (fun r : WeightedCoeff w.doubleIndex.toWeight 2 => f (hillPeriodOneCoefficientMap w r))
      (hillNativeSourceDomain w p0 δ L) :=
  analytic_linear_norm_pullback (hillPeriodOneCoefficientMap w) f (ball p0 δ) hf L

/-- Typed native pullback of the actual off-diagonal kernel series. -/
def hillNativeKernelSeries (w : SpectralWeight) (β : ℕ → Coeff 2 → ℂ) :
    WeightedCoeff w.doubleIndex.toWeight 2 → ℂ :=
  hillKernelSeriesPullback β (hillPeriodOneCoefficientMap w)

theorem hillNativeKernelSeries_apply
    (w : SpectralWeight) (β : ℕ → Coeff 2 → ℂ) (r : WeightedCoeff w.doubleIndex.toWeight 2) :
    hillNativeKernelSeries w β r=∑' k : ℕ, β k (hillPeriodOneCoefficientMap w r) := rfl

theorem hillNativeKernelSeries_analytic_bound
    (p0 : Coeff 2) (w : SpectralWeight) (β : ℕ → Coeff 2 → ℂ)
    (δ L M : ℝ) (n : ℕ) (hM : 0≤M)
    (ha : ∀ k : ℕ, AnalyticOnNhd ℂ (β k) (ball p0 δ))
    (hb : ∀ r : WeightedCoeff w.doubleIndex.toWeight 2, ‖r‖≤L →
      hillPeriodOneCoefficientMap w r∈ball p0 δ → ∀ k : ℕ,
        ‖β k (hillPeriodOneCoefficientMap w r)‖≤M*hillOffDiagonalPeriodKernel n (k : ℤ)) :
    AnalyticOnNhd ℂ (hillNativeKernelSeries w β)
      (hillNativeSourceDomain w p0 δ L) ∧
      ∀ r : WeightedCoeff w.doubleIndex.toWeight 2, hillPeriodOneCoefficientMap w r∈ball p0 δ → ‖r‖<L →
        ‖hillNativeKernelSeries w β r‖≤4*M/Real.pi^2 := by
  have h := analytic_tsum_hill_kernel_pullback (X := WeightedCoeff w.doubleIndex.toWeight 2) (Y := Coeff 2)
    β (hillPeriodOneCoefficientMap w) (ball p0 δ) isOpen_ball L M n hM ha hb
  refine ⟨h.1,?_⟩
  intro r hr hn
  exact h.2 r ⟨hr,hn⟩

end NLS.KdV
