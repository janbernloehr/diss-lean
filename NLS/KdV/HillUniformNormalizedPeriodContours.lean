import NLS.KdV.HillUniformPeriodNormalization
import NLS.KdV.HillSeparatedPeriodKernel

noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology
open NLS.ComplexAnalysis NLS.ZakharovShabat
open scoped ENNReal Classical

namespace NLS.KdV



/-- Remove the original free-period scaling while retaining the full
index separation; this includes indices near the deleted gap. -/
theorem norm_le_hillOffDiagonalPeriodKernel_of_scaled_bound
    (n k : ℕ) (hn : 1≤n) (hk : 1≤k) (hkn : k≠n) (S : ℝ) (z : ℂ)
    (hb : ‖(((freeHillValue k : ℂ)-(freeHillValue n : ℂ))/(n : ℂ))*z‖≤S/(k : ℝ)) :
    ‖z‖≤S*hillOffDiagonalPeriodKernel n (k : ℤ) := by
  have hn0 : (0:ℝ)<n := by exact_mod_cast (show 0<n by omega)
  have hk0 : (0:ℝ)<k := by exact_mod_cast (show 0<k by omega)
  have hd : 0 < |freeHillValue k-freeHillValue n| :=
    abs_pos.mpr (sub_ne_zero.mpr (strictMono_freeHillValue.injective.ne hkn))
  rw [norm_mul,norm_div,← ofReal_sub,norm_real,Real.norm_eq_abs,Complex.norm_natCast] at hb
  rw [hillOffDiagonalPeriodKernel,if_pos (by omega : 0<(k : ℤ) ∧ (k : ℤ)≠(n : ℤ)),Int.cast_natCast]
  rw [← mul_div_assoc]
  apply (le_div_iff₀ (mul_pos hk0 hd)).mpr
  have hm := mul_le_mul_of_nonneg_right hb (by positivity : 0≤(n : ℝ)*(k : ℝ))
  convert hm using 1 <;> field_simp

variable
    (h0q : SpectralWeight.one.toCoeff (0 : WeightedCoeff SpectralWeight.one.toWeight 2)∈Coeff.paritySubspace 0)
    (h0r : IsRealHillPotential (SpectralWeight.one.toCoeff (0 : WeightedCoeff SpectralWeight.one.toWeight 2)))

/-- The original normalized differential has a scaled contour estimate
uniform in both indices once the original own period is bounded below. -/
theorem norm_scaled_hillAbelianNormalizedComplexIntegrand_le
    (n k : ℕ) (hn : 1≤n) (hk : 1≤k) (hnk : n≠k) (a p : Coeff 2)
    (C : ℝ) (hC : 0≤C) (E : ℂ)
    (hE : E∈sphere (hillRealGapCenter 0 h0q h0r k : ℂ)
      (hillRealGapHalfLength 0 h0q h0r k+hillRealGapCollar 0 h0q h0r k))
    (hdom : (E,p)∈hillAbelianComplexRootDomain 0 h0q h0r)
    (hbound : ‖hillEnergyCanonicalRootProduct 0 h0q h0r E/hillAbelianComplexRoot 0 h0q h0r (E,p)-1‖≤C*‖p‖/(k : ℝ))
    (hP : 1/2≤‖hillAbelianComplexPeriod 0 h0q h0r n n (a,p)‖) :
    ‖(((freeHillValue k : ℂ)-(freeHillValue n : ℂ))/(n : ℂ))*
      (hillAbelianNormalizedComplexPsi h0q h0r n (a,p) E/hillAbelianComplexRoot 0 h0q h0r (E,p))‖≤
        (8*Real.exp ((8/Real.pi^2)*‖a‖)*(1+C*‖p‖))/(k : ℝ) := by
  have hkR : (1:ℝ)≤k := by exact_mod_cast hk
  have hratio : ‖hillEnergyCanonicalRootProduct 0 h0q h0r E/hillAbelianComplexRoot 0 h0q h0r (E,p)‖≤1+C*‖p‖ := by
    have hh := norm_le_norm_sub_add (hillEnergyCanonicalRootProduct 0 h0q h0r E/hillAbelianComplexRoot 0 h0q h0r (E,p)) 1
    rw [norm_one] at hh
    have hd : C*‖p‖/(k : ℝ)≤C*‖p‖ := div_le_self (by positivity) hkR
    linarith
  have hroot := hillEnergyCanonicalRootProduct_ne_zero_on_realCutDomain 0 h0q h0r E hdom.1.1
  have he : (((freeHillValue k : ℂ)-(freeHillValue n : ℂ))/(n : ℂ))*
      (hillAbelianNormalizedComplexPsi h0q h0r n (a,p) E/hillAbelianComplexRoot 0 h0q h0r (E,p)) =
      ((((freeHillValue k : ℂ)-(freeHillValue n : ℂ))/(n : ℂ))*
        (hillAbelianHilbertPsi n (E,a)/hillEnergyCanonicalRootProduct 0 h0q h0r E))*
          (hillEnergyCanonicalRootProduct 0 h0q h0r E/hillAbelianComplexRoot 0 h0q h0r (E,p))/
            hillAbelianComplexPeriod 0 h0q h0r n n (a,p) := by
    unfold hillAbelianNormalizedComplexPsi
    field_simp
  rw [he,norm_div,norm_mul]
  apply (div_le_div₀ (by positivity : 0≤((4/(k : ℝ))*Real.exp ((8/Real.pi^2)*‖a‖))*(1+C*‖p‖))
    (mul_le_mul (norm_scaled_hillAbelianHilbertPsi_free_root_le h0q h0r n k hn hk hnk E hE a)
      hratio (norm_nonneg _) (by positivity)) (by norm_num : (0:ℝ)<1/2) hP).trans_eq
  ring

/-- On one common complex source ball the original normalized physical
differentials have contour bounds uniform in both indices. The complete
separation kernel covers every off-diagonal gap, including k close to n. -/
theorem exists_hillSelectedPsi_common_uniform_separated_contour_charts :
    ∃ δ S : ℝ, 0<δ ∧ 0<S ∧ ∀ n : ℕ, ∀ hn : 1≤n,
      ∃ G : ℂ × Coeff 2 → ℂ,
        AnalyticOnNhd ℂ G (univ ×ˢ ball 0 δ) ∧
        (∀ p∈ball 0 δ, ∀ k : ℕ, 1≤k →
          (∀ E∈sphere (hillRealGapCenter 0 h0q h0r k : ℂ)
            (hillRealGapHalfLength 0 h0q h0r k+hillRealGapCollar 0 h0q h0r k),
            (E,p)∈hillAbelianComplexRootDomain 0 h0q h0r ∧
            (k≠n →
              ‖(((freeHillValue k : ℂ)-(freeHillValue n : ℂ))/(n : ℂ))*
                (G (E,p)/hillAbelianComplexRoot 0 h0q h0r (E,p))‖≤S/(k : ℝ) ∧
              ‖G (E,p)/hillAbelianComplexRoot 0 h0q h0r (E,p)‖≤S*hillOffDiagonalPeriodKernel n (k : ℤ))) ∧
          (2*(Real.pi : ℂ))⁻¹ * ∮ E in C((hillRealGapCenter 0 h0q h0r k : ℂ),
            hillRealGapHalfLength 0 h0q h0r k+hillRealGapCollar 0 h0q h0r k),
            G (E,p)/hillAbelianComplexRoot 0 h0q h0r (E,p) = if k=n then 1 else 0) ∧
        ∀ q : RealPeriodOneHillPotential, ‖q.val‖<δ → ∀ E : ℂ,
          G (E,SpectralWeight.one.toCoeff q.val)=hillAbelianSelectedGlobalPsi q.val q.property.1 q.property.2 n hn E := by
  obtain ⟨δc,C,hδc,hC,hcharts⟩ := exists_hillAbelianNormalizedComplexPsi_common_root_charts h0q h0r
  obtain ⟨ε,A,hε,hA,hinv⟩ := exists_hillFreeGapContour_inverse_root_bound h0q h0r
  obtain ⟨εp,D,hεp,_,hc⟩ := exists_hillComplexPeriodControl h0q h0r
  let δ := min δc (min ε εp)
  let S := 8*Real.exp ((8/Real.pi^2)*(C*δ))*(1+A*δ)
  have hδ : 0<δ := by dsimp only [δ];positivity
  have hS : 0<S := by dsimp only [S];positivity
  have hδc' : δ≤δc := min_le_left _ _
  have hδε : δ≤ε := (min_le_right _ _).trans (min_le_left _ _)
  have hδεp : δ≤εp := (min_le_right _ _).trans (min_le_right _ _)
  refine ⟨δ,S,hδ,hS,?_⟩
  intro n hn
  obtain ⟨s,_,_,hGa,hdata,hmatch⟩ := hcharts n hn
  let G : ℂ × Coeff 2 → ℂ := fun t =>
    hillAbelianNormalizedComplexPsi h0q h0r n ((s t.2 : Coeff 2),t.2) t.1
  refine ⟨G,hGa.mono (prod_mono Subset.rfl (ball_subset_ball hδc')),?_,?_⟩
  · intro p hp k hk
    have hp' : ‖p‖≤δ := (show ‖p‖<δ by simpa only [mem_ball,dist_zero_right] using hp).le
    have hpc := ball_subset_ball hδc' hp
    have hpa := (hdata p hpc).1
    have ha : ‖(s p : Coeff 2)‖≤C*δ := by
      rw [Submodule.norm_coe]
      exact hpa.trans (mul_le_mul_of_nonneg_left hp' hC.le)
    refine ⟨?_,(hdata p hpc).2.2.2 k hk⟩
    intro E hE
    obtain ⟨hdom,hb⟩ := hinv p (hp'.trans hδε) k hk E hE
    refine ⟨hdom,?_⟩
    intro hkn
    have hscaled : ‖(((freeHillValue k : ℂ)-(freeHillValue n : ℂ))/(n : ℂ))*
        (G (E,p)/hillAbelianComplexRoot 0 h0q h0r (E,p))‖≤S/(k : ℝ) := by
      apply (norm_scaled_hillAbelianNormalizedComplexIntegrand_le h0q h0r n k hn hk hkn.symm
        (s p : Coeff 2) p A hA.le E hE hdom hb (hdata p hpc).2.2.1).trans
      apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg k)
      dsimp only [S]
      gcongr
    exact ⟨hscaled,norm_le_hillOffDiagonalPeriodKernel_of_scaled_bound n k hn hk hkn S _ hscaled⟩
  · intro q hq E
    let roots := hillAbelianSelectedGlobalRoots q.val q.property.1 q.property.2 n hn
    let p := SpectralWeight.one.toCoeff q.val
    have hp : ‖p‖≤εp := (SpectralWeight.one.norm_toCoeff_le q.val).trans (hq.le.trans hδεp)
    have hperiods (k : ℕ) (hk : 1≤k) (hkn : k≠n) :
        hillAbelianCandidatePeriod q.val q.property.1 q.property.2 roots.val n k=0 := by
      have hh := (hillAbelianSelectedGlobalRoots_periods q.val q.property.1 q.property.2 n hn).2 k hk
      rw [if_neg hkn] at hh
      exact (div_eq_zero_iff.mp hh).resolve_right
        (hillAbelianSelectedGlobalRoots_periods q.val q.property.1 q.property.2 n hn).1
    have hs := hmatch q (hq.trans_le hδc') roots.val roots.property hperiods
    have he : (s p : Coeff 2)=Coeff.positiveDeletedProjection 2 (n : ℤ)
        (hillGapRootHilbertCoordinates q.val q.property.1 q.property.2 roots.val roots.property) :=
      congrArg (fun b : PositiveDeletedCoeff 2 (n : ℤ) => (b : Coeff 2)) hs.symm
    change hillAbelianNormalizedComplexPsi h0q h0r n ((s p : Coeff 2),p) E=_
    rw [he]
    exact hillAbelianNormalizedComplexPsi_projected_real_roots h0q h0r εp D hc q hp roots.val roots.property n hn E

end NLS.KdV
