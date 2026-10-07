import NLS.ZakharovShabat.SourceSobolevGapBound
import NLS.ZakharovShabat.SourceNormalizedActionUniformBound
import NLS.ZakharovShabat.SourceNormalizedActionRootAnalytic

/-! # Locally bounded kinetic-weighted actions on H¹

The actual action factors as the squared gap times the normalized action.
The weighted gap estimate therefore controls the absolute sum of `(2πn)² I_n`
on a complex H¹ neighborhood of every real source.
-/
noncomputable section
open Set
open scoped ENNReal
namespace NLS.ZakharovShabat

/-- The spectral term subtracted from the period-one physical NLS energy. -/
def sourceSobolevWeightedAction (a : ScalarDomain 2 × ScalarDomain 2) (n : ℤ) : ℂ :=
  (2 * (Real.pi : ℂ) * n)^2 *
    sourceComplexAction (by simp) (by norm_num) n (sobolevSourceInclusion a)

private theorem kinetic_weight_bound (n : ℤ) :
    ‖(2 * (Real.pi : ℂ) * n)^2‖ ≤ Real.pi^2 *
      ((SpectralWeight.sobolev 1 (by norm_num)) (2*n))^2 := by
  simp only [norm_pow, norm_mul, Complex.norm_ofNat, Complex.norm_real,
    Real.norm_eq_abs, abs_of_pos Real.pi_pos, Complex.norm_intCast,
    SpectralWeight.sobolev_apply, Weight.sobolev_apply,
    Real.rpow_one, Int.cast_mul, Int.cast_ofNat, abs_mul,
    abs_of_pos (by norm_num : (0 : ℝ) < 2)]
  nlinarith [sq_nonneg Real.pi, abs_nonneg (n : ℝ),
    mul_nonneg (sq_nonneg Real.pi) (abs_nonneg (n : ℝ))]

/-- Actual weighted actions have uniformly bounded ℓ¹ realizations near every
real H¹ source; this is a bound on the entire spectral series. -/
theorem exists_local_sourceSobolevWeightedAction_bound
    (a : ScalarDomain 2 × ScalarDomain 2)
    (ha : IsRealType (CoeffPair.toMax 2 (sobolevSourceInclusion a))) :
    ∃ U : Set (ScalarDomain 2 × ScalarDomain 2), IsOpen U ∧ a ∈ U ∧
      ∃ C : ℝ, ∀ b ∈ U, ∃ Iseq : Coeff 1,
        (∀ n : ℤ, Iseq n = sourceSobolevWeightedAction b n) ∧ ‖Iseq‖ ≤ C := by
  let L := sobolevSourceInclusion
  obtain ⟨V,hV,haV,G,hg⟩ := exists_local_sourceSobolevWeightedSquaredGap_bound a
  obtain ⟨W,hW,haW,C,hC,hfactorbound⟩ :=
    exists_local_hilbert_normalizedAction_uniform_bound (L a) ha
  obtain ⟨T,hT,haT,_,hfactor⟩ := exists_local_sourceNormalizedAction_allIndices_analytic_factor
    (by simp) (by norm_num) (L a) ha
  let U := V ∩ L ⁻¹' (W ∩ T)
  let K := Real.pi^2 * C
  have hK : 0 ≤ K := mul_nonneg (sq_nonneg _) hC
  refine ⟨U,hV.inter ((hW.inter hT).preimage L.continuous),⟨haV,haW,haT⟩,K*G,?_⟩
  intro b hb
  obtain ⟨g,hgcoord,hgnorm⟩ := hg b hb.1
  have hbound (n : ℤ) : ‖sourceSobolevWeightedAction b n‖ ≤ K * ‖g n‖ := by
    let w := SpectralWeight.sobolev 1 (by norm_num)
    let d := sourcePeriodicGapDisplacement (by simp) (by norm_num) (L b) n
    let A := sourceNormalizedActionComplexExtension (by simp) (by norm_num) n (L b)
    have hA : ‖A‖ ≤ C := hfactorbound (L b) hb.2.1 n
    have hgabs : ‖g n‖ = (w (2*n))^2 * ‖d‖^2 := by
      rw [hgcoord n]
      change ‖((w (2*n) : ℂ)^2 * d^2)‖ = _
      rw [norm_mul, norm_pow, norm_pow, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos (w.toWeight.positive _)]
    rw [sourceSobolevWeightedAction, hfactor (L b) hb.2.2 n]
    change ‖(2*(Real.pi : ℂ)*n)^2 * (d^2*A)‖ ≤ _
    simp only [norm_mul, norm_pow]
    rw [hgabs]
    calc
      _ ≤ (Real.pi^2 * (w (2*n))^2) * (‖d‖^2 * C) := by
        exact mul_le_mul (by simpa only [norm_pow, norm_mul] using kinetic_weight_bound n)
          (mul_le_mul_of_nonneg_left hA (sq_nonneg _)) (by positivity) (by positivity)
      _ = _ := by dsimp [K]; ring
  have hs := (g.property.norm.summable_of_one).mul_left K
  have hm : Memℓp (sourceSobolevWeightedAction b) 1 :=
    Coeff.memℓp_of_power_dominated _ _ hs (by simpa using hbound)
  let Iseq := Coeff.ofFunctionOrZero 1 (sourceSobolevWeightedAction b)
  refine ⟨Iseq,fun n => Coeff.ofFunctionOrZero_apply_of_mem _ _ hm n,?_⟩
  have hn := Coeff.norm_ofFunctionOrZero_rpow_le (p := 1) (by simp)
    (sourceSobolevWeightedAction b) (fun n => K*‖g n‖) hs (by simpa using hbound)
  have he : (∑' n : ℤ, ‖g n‖) = ‖g‖ := by
    simpa using (lp.norm_rpow_eq_tsum (p := 1) (by simp) g).symm
  have hI : ‖Iseq‖ ≤ K*‖g‖ := by
    simpa only [Iseq, ENNReal.toReal_one, Real.rpow_one, tsum_mul_left, he] using hn
  exact hI.trans (mul_le_mul_of_nonneg_left hgnorm hK)

end NLS.ZakharovShabat
