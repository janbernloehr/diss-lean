import NLS.ZakharovShabat.SourceSection26Sum
import NLS.ZakharovShabat.SourcePiSobolevNormBounds
import NLS.ZakharovShabat.OddHamiltonianRemainderEstimate

/-! # The literal leading action coefficient at the end of Section 26 -/
noncomputable section
open scoped ComplexConjugate
namespace NLS.ZakharovShabat

/-- The physical norm of a real pair is twice its first component's squared norm. -/
theorem sourcePiSobolevCoordinates_real_norm_sq (m k : ℕ) (hk : k ≤ m)
    (a : realTypeHigherSobolevSourceLocus m) :
    ‖sourcePiSobolevCoordinates m k hk a.val‖^2 =
      2*‖sourcePiSobolevScalar m k hk a.val.1‖^2 := by
  have he : sourcePiSobolevScalar m k hk a.val.2 =
      star (Coeff.reflection (sourcePiSobolevScalar m k hk a.val.1)) := by
    ext n
    simp only [lp.star_apply,Coeff.reflection_apply,sourcePiSobolevScalar_apply,
      realTypeHigherSobolevSource_coefficients m a,mul_neg,SpectralWeight.apply_neg]
    simp only [star_mul,Complex.star_def,Complex.conj_ofReal,mul_comm]
  rw [sourcePiSobolevCoordinates,WithLp.prod_norm_sq_eq_of_L2]
  change ‖sourcePiSobolevScalar m k hk a.val.1‖^2+
    ‖sourcePiSobolevScalar m k hk a.val.2‖^2 = _
  rw [he,norm_star,Coeff.reflection.norm_map]
  ring

/-- The top derivative uses only half of the squared real-pair physical norm. -/
theorem two_mul_highestJet_sq_le_sourcePiSobolev (m : ℕ)
    (a : realTypeHigherSobolevSourceLocus m) :
    2*‖hierarchySobolevJetL2 m m le_rfl a.val.1‖^2 ≤
      ‖sourcePiSobolevCoordinates m m le_rfl a.val‖^2 := by
  rw [sourcePiSobolevCoordinates_real_norm_sq]
  have h : ‖hierarchySobolevJetL2 m m le_rfl a.val.1‖ ≤
      ‖sourcePiSobolevScalar m m le_rfl a.val.1‖ := by
    apply lp.norm_mono (by norm_num : (2:ENNReal) ≠ 0)
    intro n
    rw [hierarchySobolevJetL2_apply,norm_periodOneJetMultiplier,
      sourcePiSobolevScalar_apply,norm_mul,Complex.norm_real,
      Real.norm_of_nonneg ((SpectralWeight.piSobolev m (Nat.cast_nonneg m)).positive (2*n)).le]
    simp only [SpectralWeight.piSobolev_apply,Real.rpow_natCast,Int.cast_mul,Int.cast_ofNat,
      abs_mul,abs_of_pos (by norm_num : (0:ℝ)<2),abs_of_pos Real.pi_pos]
    rw [← mul_pow]
    gcongr
    nlinarith [abs_nonneg (n:ℝ),Real.pi_pos]
  exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) h 2) (by norm_num)

/-- The final Section 26 display retains the literal leading coefficient 2^m,
with one remainder constant chosen before all original real H^m sources. -/
theorem exists_sourceSection26_action_leading_bound (m : ℕ) (hm : 1 ≤ m) :
    ∃ c : ℝ, 0 ≤ c ∧ ∀ a : realTypeHigherSobolevSourceLocus m,
      (∑' n : ℤ, sourceIndexedWeightedActionTerm
        ⟨higherSobolevSourceInclusion m a.val,a.property⟩ m n) ≤
        2^m*‖sourcePiSobolevCoordinates m m le_rfl a.val‖^2+
          c^2*(1+‖sourcePiSobolevCoordinates m 1 hm a.val‖)^(4*m)*
            ‖higherSobolevSourceInclusion m a.val‖^2 := by
  obtain ⟨C,hC,hH⟩ := exists_sobolevOddHamiltonian_energy_estimates m hm 1 zero_lt_one
  let B : ℝ := (1+16*Real.pi)^(2*m)
  let K : ℝ := B+2^m*C*2
  have hK : 0 ≤ K := by dsimp [K,B]; positivity
  refine ⟨Real.sqrt K,Real.sqrt_nonneg _,?_⟩
  intro a
  let X := ‖sourcePiSobolevCoordinates m m le_rfl a.val‖^2
  let R := (1+‖sourcePiSobolevCoordinates m 1 hm a.val‖)^(4*m)*
    ‖higherSobolevSourceInclusion m a.val‖^2
  have hjet := two_mul_highestJet_sq_le_sourcePiSobolev m a
  have hrem := mul_le_mul_of_nonneg_left (source_scalarMass_remainder_le m hm a.val) hC
  have hham : (sobolevOddHamiltonian m hm a.val).re ≤ X+2*C*R := by
    have h := (Complex.re_le_norm _).trans (hH a).2
    dsimp [X,R]
    nlinarith
  have hsum := sourceSection26_action_estimate m hm a
  have hmul := mul_le_mul_of_nonneg_left hham (by positivity : 0 ≤ (2:ℝ)^m)
  rw [Real.sq_sqrt hK]
  dsimp [B,K,X,R] at *
  nlinarith

end NLS.ZakharovShabat
