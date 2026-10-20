import NLS.SequenceSpaces.WeightedMultiplier
import NLS.Fourier.PartialIntervalOscillatorySampling
import NLS.ZakharovShabat.WKBBoundedFrequencyCutoff
import NLS.SequenceSpaces.SobolevDecayingLeadingTail
import NLS.ZakharovShabat.SobolevWKBInitialDecay
import NLS.ZakharovShabat.WKBLeadingFrequencyCutoff
import NLS.ZakharovShabat.SobolevWKBBothLeadingFourierTails

/-! # The leading terms in the trace identity

Both leading oscillatory terms multiplied by their small initial coordinates have uniformly bounded H^(s+1) tails.
-/

noncomputable section
open Set Complex MeasureTheory NLS.Fourier
open scoped ContDiff ENNReal
namespace NLS.ZakharovShabat

/-- Direct L2 sampling controls the leading trace term under bounded
displacements alone; the initial coordinate supplies the extra inverse power. -/
theorem exists_uniform_nlsWKB_first_trace_leading_tail_bound_of_bounded_displacement
    (s : ℕ) (R D : ℝ) (hR : 0 ≤ R) (hD : 0 ≤ D) :
    ∃ K : ℕ, 0 < K ∧ ∃ C : ℝ, 0 ≤ C ∧
      ∀ K' : ℕ, K ≤ K' → ∀ ab : SobolevSource s, ‖ab‖ ≤ R → ∀ a b : ℝ → ℂ,
      ContDiff ℝ ∞ a → ContDiff ℝ ∞ b →
      Function.Periodic a 1 → Function.Periodic b 1 →
      (∀ j, ab.1.val j = periodOneCoefficient a j) →
      (∀ j, ab.2.val j = periodOneCoefficient b j) →
      ∀ δ : NLS.Coeff ⊤, ‖δ‖ ≤ D →
      ∃ f : ScalarSobolev (s+1),
        (∀ n, f.val n = if K' ≤ n.natAbs then
          let z := (Real.pi:ℂ)*n+δ n
          nlsWKBInitialUpper a b s z*nlsWKBLeadingTerm a b s z 1 else 0) ∧ ‖f‖ ≤ C := by
  classical
  obtain ⟨K,hK,hcut⟩ := exists_wkb_bounded_frequency_cutoff D hD
  obtain ⟨B,hB,hinit⟩ := exists_uniform_nlsWKB_initial_coordinate_decay s s le_rfl R hR
  obtain ⟨L,hL,hL2⟩ := exists_uniform_nlsRiccatiDensity_L2_bound s s le_rfl R hR
  refine ⟨K,hK,B*(Real.exp (3*D)*L),by positivity,?_⟩
  intro K' hK' ab hab a b ha hb hpa hpb hca hcb δ hδD
  let ρ := nlsRiccatiDensity a b s
  have hρ : Continuous ρ := (contDiff_nlsRiccatiDensity a b ha hb s).continuous
  have hρL2 := memLp_two_interval hρ 0 1 (by norm_num : (0:ℝ) ≤ 1)
  have hρn : ‖unitIntervalMemLpCoefficients ρ hρL2‖ ≤ L := by
    have he := norm_sq_unitIntervalMemLpCoefficients ρ hρL2
    have he' : ‖unitIntervalMemLpCoefficients ρ hρL2‖ =
        Real.sqrt (∫ x in (0:ℝ)..1, ‖ρ x‖^2) := by
      rw [← he,Real.sqrt_sq (norm_nonneg _)]
    rw [he']
    exact hL2 ab hab a b ha hb hpa hpb hca hcb
  obtain ⟨q,hq,hqn⟩ := exists_partial_interval_oscillatory_lattice_coefficients ρ hρL2 δ 1 ⟨by norm_num,le_rfl⟩
  have hqbound : ‖q‖ ≤ Real.exp (3*D)*L :=
    hqn.trans (mul_le_mul (Real.exp_le_exp.mpr (by linarith)) hρn (norm_nonneg _) (Real.exp_pos _).le)
  let ν (n : ℤ) := (Real.pi:ℂ)*n+δ n
  let m (n : ℤ) := if K' ≤ n.natAbs then (-I)*nlsWKBInitialUpper a b s (ν n)*((2*I*ν n)⁻¹)^s else 0
  let v := Weight.sobolev ((s+1:ℕ):ℝ)
  have hδ (n : ℤ) : ‖δ n‖ ≤ D := (lp.norm_apply_le_norm (by simp) δ n).trans hδD
  have hm (n : ℤ) : v n*‖m n‖ ≤ B*Weight.one n := by
    by_cases hn : K' ≤ n.natAbs
    · have hh := hcut δ hδ n (hK'.trans hn)
      have hw : (1+|(n:ℝ)|)*‖(2*I*ν n)⁻¹‖ ≤ 1 := by
        simp only [norm_inv,norm_mul,norm_ofNat,norm_I,mul_one]
        rw [← div_eq_mul_inv]
        apply (div_le_one (by change 0 < 2*‖(Real.pi:ℂ)*n+δ n‖; linarith [hh.1])).mpr
        change 1+|(n:ℝ)| ≤ 2*‖(Real.pi:ℂ)*n+δ n‖
        linarith [hh.2]
      have hi := (hinit ab hab a b ha hb hpa hpb hca hcb (ν n) hh.1).2
      have hp := pow_le_pow_left₀ (by positivity) hw (s+1)
      simp only [v,Weight.sobolev_apply,Real.rpow_natCast,m,if_pos hn,
        norm_mul,norm_neg,norm_I,one_mul,norm_pow,Weight.one_apply,mul_one]
      calc
        _ ≤ (1+|(n:ℝ)|)^(s+1)*((B*‖(2*I*ν n)⁻¹‖)*‖(2*I*ν n)⁻¹‖^s) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hi (by positivity)) (by positivity)
        _ = B*((1+|(n:ℝ)|)*‖(2*I*ν n)⁻¹‖)^(s+1) := by simp only [mul_pow,pow_succ]; ring
        _ ≤ B := by simpa only [one_pow,mul_one] using mul_le_mul_of_nonneg_left hp hB
    · simpa only [m,if_neg hn,norm_zero,mul_zero,Weight.one_apply,mul_one] using hB
  let q₀ := (WeightedCoeff.weightIsometry Weight.one 2).symm q
  have hq₀ (n : ℤ) : q₀.val n = q n := by
    change q n/(Weight.one n:ℂ) = q n
    simp
  let f := WeightedCoeff.weightedMultiplier Weight.one v m B hm q₀
  refine ⟨f,?_,?_⟩
  · intro n
    change m n*q₀.val n = _
    rw [hq₀,hq n]
    by_cases hn : K' ≤ n.natAbs
    · simp only [m,if_pos hn,nlsWKBLeadingTerm,ν,ρ,Complex.ofReal_one,mul_one]
      ring
    · simp [m,hn]
  · have hn := WeightedCoeff.norm_weightedMultiplier_le Weight.one v m B hB hm q₀
    exact hn.trans (mul_le_mul_of_nonneg_left (by simpa only [q₀,LinearIsometryEquiv.norm_map] using hqbound) hB)

/-- Both small-coordinate leading terms have a common H^(s+1) bound
under merely bounded lattice displacements, at every larger cutoff. -/
theorem exists_uniform_nlsWKB_trace_leading_fourier_tail_bound_of_bounded_displacement
    (s : ℕ) (R D : ℝ) (hR : 0 ≤ R) (hD : 0 ≤ D) :
    ∃ K : ℕ, 0 < K ∧ ∃ C : ℝ, 0 ≤ C ∧
      ∀ K' : ℕ, K ≤ K' → ∀ ab : SobolevSource s, ‖ab‖ ≤ R → ∀ a b : ℝ → ℂ,
      ContDiff ℝ ∞ a → ContDiff ℝ ∞ b →
      Function.Periodic a 1 → Function.Periodic b 1 →
      (∀ j, ab.1.val j = periodOneCoefficient a j) →
      (∀ j, ab.2.val j = periodOneCoefficient b j) →
      ∀ δ : NLS.Coeff ⊤, ‖δ‖ ≤ D →
      ∃ f g : ScalarSobolev (s+1),
        (∀ n, f.val n = if K' ≤ n.natAbs then
          let z := (Real.pi:ℂ)*n+δ n
          nlsWKBInitialUpper a b s z*nlsWKBLeadingTerm a b s z 1 else 0) ∧
        (∀ n, g.val n = if K' ≤ n.natAbs then
          let z := (Real.pi:ℂ)*n+δ n
          nlsWKBInitialLower a b s z*nlsWKBLeadingTerm (-b) (-a) s (-z) 1 else 0) ∧
        ‖f‖ ≤ C ∧ ‖g‖ ≤ C := by
  obtain ⟨K,hK,C,hC,h⟩ := exists_uniform_nlsWKB_first_trace_leading_tail_bound_of_bounded_displacement s R D hR hD
  refine ⟨K,hK,C,hC,?_⟩
  intro K' hK' ab hab a b ha hb hpa hpb hca hcb δ hδD
  obtain ⟨f,hf,hfn⟩ := h K' hK' ab hab a b ha hb hpa hpb hca hcb δ hδD
  let cd : SobolevSource s := (-ab.2,-ab.1)
  have hcd : ‖cd‖ ≤ R := by simpa only [cd,Prod.norm_def,norm_neg,max_comm] using hab
  have hc1 (j : ℤ) : cd.1.val j = periodOneCoefficient (-b) j := by
    simpa only [cd,WeightedCoeff.neg_val,periodOneCoefficient_neg] using congrArg Neg.neg (hcb j)
  have hc2 (j : ℤ) : cd.2.val j = periodOneCoefficient (-a) j := by
    simpa only [cd,WeightedCoeff.neg_val,periodOneCoefficient_neg] using congrArg Neg.neg (hca j)
  let δ' : NLS.Coeff ⊤ := -Coeff.reflection δ
  have hδ'D : ‖δ'‖ ≤ D := by simpa only [δ',norm_neg,LinearIsometryEquiv.norm_map] using hδD
  obtain ⟨g,hg,hgn⟩ := h K' hK' cd hcd (-b) (-a) hb.neg ha.neg
    (fun x => congrArg Neg.neg (hpb x)) (fun x => congrArg Neg.neg (hpa x)) hc1 hc2 δ' hδ'D
  refine ⟨f,WeightedCoeff.reflection ((s+1:ℕ):ℝ) g,hf,?_,hfn,?_⟩
  · intro n
    rw [WeightedCoeff.reflection_apply,hg (-n),Int.natAbs_neg]
    split_ifs with hn
    · have hz : (Real.pi:ℂ)*(-n)+δ' (-n) = -((Real.pi:ℂ)*n+δ n) := by
        change (Real.pi:ℂ)*(-n)-δ (-(-n)) = -((Real.pi:ℂ)*n+δ n)
        simp only [neg_neg]
        ring
      simp only [Int.cast_neg]
      rw [hz]
      simp only [nlsWKBInitialUpper,nlsWKBSecondVector,Prod.fst_swap,neg_neg,nlsWKBInitialLower]
    · rfl
  · simpa only [LinearIsometryEquiv.norm_map] using hgn

/-- Both leading oscillatory terms, multiplied by their small initial
coordinates in the trace identity, have H^(s+1) tails on original Hs
balls with a common bound at every larger cutoff. -/
theorem exists_uniform_nlsWKB_trace_leading_fourier_tail_bound
    (s : ℕ) (R D M : ℝ) (hR : 0 ≤ R) (hD : 0 ≤ D) (hM : 0 ≤ M) :
    ∃ K : ℕ, 0 < K ∧ ∃ C : ℝ, 0 ≤ C ∧
      ∀ K' : ℕ, K ≤ K' → ∀ ab : SobolevSource s, ‖ab‖ ≤ R → ∀ a b : ℝ → ℂ,
      ContDiff ℝ ∞ a → ContDiff ℝ ∞ b →
      Function.Periodic a 1 → Function.Periodic b 1 →
      (∀ j, ab.1.val j = periodOneCoefficient a j) →
      (∀ j, ab.2.val j = periodOneCoefficient b j) →
      ∀ δ : NLS.Coeff ⊤, ‖δ‖ ≤ D →
      (∀ n : ℤ, (1+|(n:ℝ)|)*‖δ n‖ ≤ M) →
      ∃ f g : ScalarSobolev (s+1),
        (∀ n, f.val n = if K' ≤ n.natAbs then
          let z := (Real.pi:ℂ)*n+δ n
          nlsWKBInitialUpper a b s z*
            nlsWKBLeadingTerm a b s z 1 else 0) ∧
        (∀ n, g.val n = if K' ≤ n.natAbs then
          let z := (Real.pi:ℂ)*n+δ n
          nlsWKBInitialLower a b s z*
            nlsWKBLeadingTerm (-b) (-a) s (-z) 1 else 0) ∧
        ‖f‖ ≤ C ∧ ‖g‖ ≤ C := by
  obtain ⟨K,hK,C,hC,h⟩ := exists_uniform_nlsWKB_trace_leading_fourier_tail_bound_of_bounded_displacement s R D hR hD
  have _hM := hM
  refine ⟨K,hK,C,hC,?_⟩
  intro K' hK' ab hab a b ha hb hpa hpb hca hcb δ hδD _hδM
  exact h K' hK' ab hab a b ha hb hpa hpb hca hcb δ hδD

end NLS.ZakharovShabat
