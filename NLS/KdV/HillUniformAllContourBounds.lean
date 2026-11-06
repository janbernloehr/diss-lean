import NLS.KdV.HillUniformNormalizedPeriodContours

noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology
open NLS.ComplexAnalysis NLS.ZakharovShabat
open scoped ENNReal ComplexConjugate Classical

namespace NLS.KdV



variable
    (h0q : SpectralWeight.one.toCoeff (0 : WeightedCoeff SpectralWeight.one.toWeight 2)∈Coeff.paritySubspace 0)
    (h0r : IsRealHillPotential (SpectralWeight.one.toCoeff (0 : WeightedCoeff SpectralWeight.one.toWeight 2)))

/-- The contour radius times the full off-diagonal kernel is uniformly
bounded, even next to the own gap. -/
theorem hillFreeGapRadius_mul_periodKernel_le (n k : ℕ) (hk : 1≤k) (hkn : k≠n) :
    (hillRealGapHalfLength 0 h0q h0r k+hillRealGapCollar 0 h0q h0r k)*
      hillOffDiagonalPeriodKernel n (k : ℤ)≤1/2 := by
  have hk0 : (0:ℝ)<k := by exact_mod_cast (show 0<k by omega)
  have hsum : 0<(k : ℝ)+(n : ℝ) := by positivity
  have hdiff : 1≤|(k : ℝ)-(n : ℝ)| := by
    have hh := Int.one_le_abs (show (k : ℤ)-(n : ℤ)≠0 by omega)
    exact_mod_cast hh
  have hE : freeHillValue k-freeHillValue n=Real.pi^2*((k : ℝ)-(n : ℝ))*((k : ℝ)+(n : ℝ)) := by
    simp only [freeHillValue,Int.cast_natCast]
    ring
  have hElow : Real.pi^2*(n : ℝ)≤|freeHillValue k-freeHillValue n| := by
    rw [hE,abs_mul,abs_mul,abs_of_pos (sq_pos_of_pos Real.pi_pos),abs_of_pos hsum]
    have hh := mul_le_mul hdiff (show (n : ℝ)≤(k : ℝ)+(n : ℝ) by linarith)
      (Nat.cast_nonneg n) (by linarith : 0≤|(k : ℝ)-(n : ℝ)|)
    nlinarith [sq_nonneg Real.pi]
  have hD : 0 < |freeHillValue k-freeHillValue n| :=
    abs_pos.mpr (sub_ne_zero.mpr (strictMono_freeHillValue.injective.ne hkn))
  have hR : hillRealGapHalfLength 0 h0q h0r k+hillRealGapCollar 0 h0q h0r k≤Real.pi^2*(k : ℝ)/2 := by
    rw [hillFreeGapHalfLength h0q h0r k hk,zero_add,hillFreeGapCollar h0q h0r k hk]
    nlinarith [sq_nonneg Real.pi]
  rw [hillOffDiagonalPeriodKernel,if_pos (by omega : 0<(k : ℤ) ∧ (k : ℤ)≠(n : ℤ)),Int.cast_natCast]
  apply (mul_le_mul_of_nonneg_right hR (by positivity)).trans
  have hratio : (n : ℝ)/|freeHillValue k-freeHillValue n|≤(Real.pi^2)⁻¹ := by
    apply (div_le_iff₀ hD).mpr
    rw [inv_mul_eq_div]
    apply (le_div_iff₀ (sq_pos_of_pos Real.pi_pos)).mpr
    nlinarith
  calc
    (Real.pi^2*(k : ℝ)/2)*((n : ℝ)/((k : ℝ)*|freeHillValue k-freeHillValue n|)) =
        (Real.pi^2/2)*((n : ℝ)/|freeHillValue k-freeHillValue n|) := by field_simp
    _ ≤ (Real.pi^2/2)*(Real.pi^2)⁻¹ := mul_le_mul_of_nonneg_left hratio (by positivity)
    _ = 1/2 := by field_simp

/-- Include the own gap in the original normalized complex contour bound. -/
theorem norm_hillAbelianNormalizedComplexOwnIntegrand_le
    (n : ℕ) (hn : 1≤n) (a p : Coeff 2) (C : ℝ) (hC : 0≤C) (E : ℂ)
    (hE : E∈sphere (hillRealGapCenter 0 h0q h0r n : ℂ)
      (hillRealGapHalfLength 0 h0q h0r n+hillRealGapCollar 0 h0q h0r n))
    (hdom : (E,p)∈hillAbelianComplexRootDomain 0 h0q h0r)
    (hbound : ‖hillEnergyCanonicalRootProduct 0 h0q h0r E/hillAbelianComplexRoot 0 h0q h0r (E,p)-1‖≤C*‖p‖/(n : ℝ))
    (hP : 1/2≤‖hillAbelianComplexPeriod 0 h0q h0r n n (a,p)‖) :
    ‖hillAbelianNormalizedComplexPsi h0q h0r n (a,p) E/hillAbelianComplexRoot 0 h0q h0r (E,p)‖≤
      (4*Real.exp ((8/Real.pi^2)*‖a‖)*(1+C*‖p‖))/
        (hillRealGapHalfLength 0 h0q h0r n+hillRealGapCollar 0 h0q h0r n) := by
  have hnR : (1:ℝ)≤n := by exact_mod_cast hn
  have hR : 0<hillRealGapHalfLength 0 h0q h0r n+hillRealGapCollar 0 h0q h0r n :=
    add_pos_of_nonneg_of_pos (hillRealGapContour_geometry 0 h0q h0r n hn).1 (hillRealGapContour_geometry 0 h0q h0r n hn).2.1
  have hr : ‖hillEnergyCanonicalRootProduct 0 h0q h0r E/hillAbelianComplexRoot 0 h0q h0r (E,p)‖≤1+C*‖p‖ := by
    have hh := norm_le_norm_sub_add (hillEnergyCanonicalRootProduct 0 h0q h0r E/hillAbelianComplexRoot 0 h0q h0r (E,p)) 1
    rw [norm_one] at hh
    have hd : C*‖p‖/(n : ℝ)≤C*‖p‖ := div_le_self (by positivity) hnR
    linarith
  have hroot := hillEnergyCanonicalRootProduct_ne_zero_on_realCutDomain 0 h0q h0r E hdom.1.1
  have he : hillAbelianNormalizedComplexPsi h0q h0r n (a,p) E/hillAbelianComplexRoot 0 h0q h0r (E,p)=
      ((hillAbelianHilbertPsi n (E,a)/hillEnergyCanonicalRootProduct 0 h0q h0r E)*
        (hillEnergyCanonicalRootProduct 0 h0q h0r E/hillAbelianComplexRoot 0 h0q h0r (E,p)))/
          hillAbelianComplexPeriod 0 h0q h0r n n (a,p) := by
    unfold hillAbelianNormalizedComplexPsi
    field_simp
  rw [he,norm_div,norm_mul]
  have hfree : ‖hillAbelianHilbertPsi n (E,a)/hillEnergyCanonicalRootProduct 0 h0q h0r E‖≤
      (2/(hillRealGapHalfLength 0 h0q h0r n+hillRealGapCollar 0 h0q h0r n))*Real.exp ((8/Real.pi^2)*‖a‖) := by
    rw [hillAbelianHilbertPsi_contour_separation h0q h0r n n hn E hE a,mul_div_right_comm,norm_mul]
    exact mul_le_mul (norm_hillFreeOwnAbelianQuotient_on_contour h0q h0r n hn E hE)
      (norm_hilbertWeightedProduct_hillFreeContour_le h0q h0r n n hn E hE a) (norm_nonneg _) (by positivity)
  apply (div_le_div₀ (by positivity : 0≤(2/(hillRealGapHalfLength 0 h0q h0r n+
      hillRealGapCollar 0 h0q h0r n))*Real.exp ((8/Real.pi^2)*‖a‖)*(1+C*‖p‖))
    (mul_le_mul hfree hr (norm_nonneg _) (by positivity)) (by norm_num : (0:ℝ)<1/2) hP).trans_eq
  ring

/-- The original normalized physical differentials admit one common
analytic source ball and one radius-normalized bound on every contour,
including the own contour and all neighboring gaps. -/
theorem exists_hillSelectedPsi_common_uniform_all_contour_charts :
    ∃ δ S : ℝ, 0<δ ∧ 0<S ∧ ∀ n : ℕ, ∀ hn : 1≤n,
      ∃ G : ℂ × Coeff 2 → ℂ,
        AnalyticOnNhd ℂ G (univ ×ˢ ball 0 δ) ∧
        (∀ p∈ball 0 δ, ∀ k : ℕ, 1≤k →
          (∀ E∈sphere (hillRealGapCenter 0 h0q h0r k : ℂ)
            (hillRealGapHalfLength 0 h0q h0r k+hillRealGapCollar 0 h0q h0r k),
            (E,p)∈hillAbelianComplexRootDomain 0 h0q h0r ∧
            ‖G (E,p)/hillAbelianComplexRoot 0 h0q h0r (E,p)‖≤S/
              (hillRealGapHalfLength 0 h0q h0r k+hillRealGapCollar 0 h0q h0r k)) ∧
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
    have hR : 0<hillRealGapHalfLength 0 h0q h0r k+hillRealGapCollar 0 h0q h0r k :=
      add_pos_of_nonneg_of_pos (hillRealGapContour_geometry 0 h0q h0r k hk).1
        (hillRealGapContour_geometry 0 h0q h0r k hk).2.1
    by_cases hkn : k=n
    · subst k
      apply (norm_hillAbelianNormalizedComplexOwnIntegrand_le h0q h0r n hn (s p : Coeff 2) p
        A hA.le E hE hdom hb (hdata p hpc).2.2.1).trans
      apply div_le_div_of_nonneg_right _ hR.le
      dsimp only [S]
      gcongr
      norm_num
    · have hscaled : ‖(((freeHillValue k : ℂ)-(freeHillValue n : ℂ))/(n : ℂ))*
          (G (E,p)/hillAbelianComplexRoot 0 h0q h0r (E,p))‖≤S/(k : ℝ) := by
        apply (norm_scaled_hillAbelianNormalizedComplexIntegrand_le h0q h0r n k hn hk (Ne.symm hkn)
          (s p : Coeff 2) p A hA.le E hE hdom hb (hdata p hpc).2.2.1).trans
        apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg k)
        dsimp only [S]
        gcongr
      apply (norm_le_hillOffDiagonalPeriodKernel_of_scaled_bound n k hn hk hkn S _ hscaled).trans
      apply (le_div_iff₀ hR).mpr
      have hh := mul_le_mul_of_nonneg_left (hillFreeGapRadius_mul_periodKernel_le h0q h0r n k hk hkn) hS.le
      nlinarith

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
