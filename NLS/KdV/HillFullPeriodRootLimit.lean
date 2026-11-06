import NLS.KdV.HillProductPeriodUniformLimit
import NLS.KdV.HillGapRootHilbertCompactness
import NLS.KdV.HillGlobalPeriodDerivativeInjectivity

noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology
open NLS.ComplexAnalysis NLS.ZakharovShabat
open scoped ENNReal ComplexConjugate Classical

namespace NLS.KdV



variable (q : WeightedCoeff SpectralWeight.one.toWeight 2)
    (hq : SpectralWeight.one.toCoeff q∈Coeff.paritySubspace 0)
    (hr : IsRealHillPotential (SpectralWeight.one.toCoeff q))

/-- The full Hilbert coordinates of the original selected real roots. -/
def hillAbelianSelectedGlobalRootCoordinates (n : ℕ) (hn : 1≤n) : Coeff 2 :=
  hillGapRootHilbertCoordinates q hq hr (hillAbelianSelectedGlobalRoots q hq hr n hn).val
    (hillAbelianSelectedGlobalRoots q hq hr n hn).property

/-- At every real potential, some subsequence of the original selected
root vectors converges to an actual gap-box vector whose full product
has zero original period on every positive gap. -/
theorem exists_hillAbelianSelectedGlobalRoots_full_product_subsequence :
    ∃ roots : hillGapRootBox q hq hr, ∃ φ : ℕ → ℕ, StrictMono φ ∧
      Tendsto (fun m => hillAbelianSelectedGlobalRootCoordinates q hq hr (φ m+1) (by omega)) atTop
        (𝓝 (hillGapRootHilbertCoordinates q hq hr roots.val roots.property)) ∧
      ∀ k : ℕ, 1≤k → hillIntrinsicGapPeriod q hq hr k
        (fun E => hillAbelianHilbertProduct 0 (E,hillGapRootHilbertCoordinates q hq hr roots.val roots.property))=0 := by
  let S := range (fun roots : hillGapRootBox q hq hr => hillGapRootHilbertCoordinates q hq hr roots.val roots.property)
  let A : ℕ → Coeff 2 := fun n => hillAbelianSelectedGlobalRootCoordinates q hq hr (n+1) (by omega)
  have hS : IsCompact S := isCompact_range_hillGapRootHilbertCoordinates q hq hr
  have hmem (n : ℕ) : A n∈S := ⟨hillAbelianSelectedGlobalRoots q hq hr (n+1) (by omega),rfl⟩
  obtain ⟨a,ha,φ,hφ,hconv⟩ := hS.tendsto_subseq hmem
  obtain ⟨roots,har⟩ := ha
  subst a
  obtain ⟨B,hB,hBb⟩ := hS.isBounded.exists_pos_norm_le
  refine ⟨roots,φ,hφ,hconv,?_⟩
  intro k hk
  obtain ⟨U,C,hU,hqU,hC,hPa,hbound⟩ := exists_hillAbelianProductComplexPeriod_full_uniform_bound q hq hr k hk B hB.le
  let P : Coeff 2 → ℂ := fun b => hillAbelianProductComplexPeriod q hq hr 0 k (b,SpectralWeight.one.toCoeff q)
  have hP : AnalyticAt ℂ P (hillGapRootHilbertCoordinates q hq hr roots.val roots.property) :=
    (hPa 0 _ ⟨mem_univ _,hqU⟩).comp (f := fun b : Coeff 2 => (b,SpectralWeight.one.toCoeff q))
      (analyticAt_id.prod analyticAt_const)
  have hlim : Tendsto (fun m => P (A (φ m))) atTop
      (𝓝 (P (hillGapRootHilbertCoordinates q hq hr roots.val roots.property))) := hP.continuousAt.tendsto.comp hconv
  have hzero : Tendsto (fun m => P (A (φ m))) atTop (𝓝 0) := by
    rw [Metric.tendsto_atTop]
    intro ε hε
    obtain ⟨J,hJ⟩ := exists_nat_gt (C/ε)
    obtain ⟨L,hL⟩ := eventually_atTop.mp (hφ.tendsto_atTop (eventually_ge_atTop (J+k)))
    refine ⟨L,?_⟩
    intro m hm
    have hlarge : J+k≤φ m := hL m hm
    have hkn : k≠φ m+1 := by omega
    have hperiod := (hillAbelianSelectedGlobalRoots_periods q hq hr (φ m+1) (by omega)).2 k hk
    rw [if_neg hkn,div_eq_zero_iff] at hperiod
    have hz := hperiod.resolve_right (hillAbelianSelectedGlobalRoots_periods q hq hr (φ m+1) (by omega)).1
    have hprodZero : hillAbelianProductComplexPeriod q hq hr (φ m+1) k (A (φ m),SpectralWeight.one.toCoeff q)=0 := by
      rw [hillAbelianProductComplexPeriod_eq_rescaled q hq hr _ _ (by omega),hillAbelianComplexPeriod_at_base q hq hr _ k hk]
      dsimp only [A,hillAbelianSelectedGlobalRootCoordinates]
      rw [hillAbelianHilbertPeriod_eq_genuine_period q hq hr
        (hillAbelianSelectedGlobalRoots q hq hr (φ m+1) (by omega)).val
        (hillAbelianSelectedGlobalRoots q hq hr (φ m+1) (by omega)).property,hz,mul_zero]
    have hb := hbound (φ m+1) (by omega) (A (φ m)) (hBb _ (hmem _)) (SpectralWeight.one.toCoeff q) hqU
    rw [hprodZero,zero_sub,norm_neg] at hb
    rw [dist_zero_right]
    apply hb.trans_lt
    have hnpos : (0:ℝ)<(φ m+1 : ℕ) := by positivity
    apply (div_lt_iff₀ hnpos).mpr
    have hCJ : C<ε*(J : ℝ) := by nlinarith [(div_lt_iff₀ hε).mp hJ]
    have hJN : (J : ℝ)≤(φ m+1 : ℕ) := by exact_mod_cast (by omega : J≤φ m+1)
    nlinarith
  have he : P (hillGapRootHilbertCoordinates q hq hr roots.val roots.property)=0 := tendsto_nhds_unique hlim hzero
  exact (hillAbelianProductComplexPeriod_at_base q hq hr 0 k hk _).symm.trans he

end NLS.KdV
