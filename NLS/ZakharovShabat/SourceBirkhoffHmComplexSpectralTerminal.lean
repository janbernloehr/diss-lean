import NLS.ZakharovShabat.SourceHigherSobolevFirstNormalizedCoordinates
import NLS.ZakharovShabat.SourceBirkhoffComplexSpectralTerminal

/-! # Complex angular smoothing at every positive integer source order

Both signed Birkhoff-minus-terminal errors belong locally to h^(m+1) on the original complex Hm source. The common neighborhood and bound include collapsed gaps. This proves the angular part of the Fourier comparison.
-/

noncomputable section
open Set Metric Complex Filter Topology
open scoped ENNReal

namespace NLS.ZakharovShabat.SourceBirkhoffMapComplexData
variable {W₀ B W : Set (CoeffPair 2)} {s : (n : ℤ) → CoeffPair 2 → DeletedCoeff 2 n}
variable (D : SourceBirkhoffMapComplexData (by simp) (by norm_num) W₀ B W s)
include D

/-- Every positive integer Sobolev order has a complex local bound for the actual angular error gaining one derivative. -/
theorem exists_local_higherSobolevBirkhoffSpectralTerminal_bound (m : ℕ) (hm : 1 ≤ m)
    (a : realTypeHigherSobolevSourceLocus m) :
    ∃ U : Set (SobolevSource m), IsOpen U ∧ a.val ∈ U ∧
      ∃ M : ℝ, 0 ≤ M ∧ ∀ b ∈ U, ∀ sign : ℝ, sign=1 ∨ sign= -1 →
        ∃ z : WeightedCoeff (Weight.sobolev ((m:ℝ)+1)) 2,
          (∀ n, z.val n = sourceBirkhoffWeightedCoordinate (by simp) (by norm_num) n s (sign:ℂ)
              (higherSobolevSourceInclusion m b)-sourceGapWeightedEtaTerminalCoordinate (by simp) (by norm_num)
                n (sign:ℂ) (higherSobolevSourceInclusion m b)) ∧ ‖z‖ ≤ M := by
  let J := higherSobolevFirstNormalizedCoordinates m hm
  let H := higherSobolevNormalizedCoordinates m
  let φ1 : realTypeSourceLocus 2 := ⟨J a.val,higherSobolevFirstNormalizedCoordinates_realType m hm a⟩
  let φm : realTypeSourceLocus 2 := ⟨H a.val,(higherSobolevNormalizedCoordinates_realType_iff m a.val).2 a.property⟩
  let w := SpectralWeight.sobolev m (Nat.cast_nonneg m)
  obtain ⟨Vn,hVn,hφn,K,hK,hn⟩ := D.exists_local_normalizedSobolevNormalizationPhase_smoothing φ1
  obtain ⟨Ve,hVe,hφe,L,hL,he⟩ := D.exists_local_normalizedSobolevEtaRemainder_phase_smoothing φ1
  obtain ⟨Va,hVa,hφa,A,hA,ha⟩ := D.exists_local_normalizedWeightedEta_analytic w φm
  let U := (J ⁻¹' (Vn ∩ Ve)) ∩ H ⁻¹' Va
  have hU : IsOpen U := ((hVn.inter hVe).preimage J.continuous).inter (hVa.preimage H.continuous)
  let M := (2*K*Real.exp K+L*Real.exp L)*A
  refine ⟨U,hU,⟨⟨hφn,hφe⟩,hφa⟩,M,by dsimp only [M]; positivity,?_⟩
  intro b hb sign hsign
  have hs : (sign:ℂ)=1 ∨ (sign:ℂ)= -1 := by rcases hsign with rfl | rfl <;> simp
  have habs : |sign|=1 := by rcases hsign with rfl | rfl <;> norm_num
  let χ := higherSobolevSourceInclusion m b
  have hJ : normalizedWeightedSource (SpectralWeight.sobolev 1 (by norm_num)) (J b) = χ :=
    normalizedWeightedSource_higherSobolevFirstNormalizedCoordinates m hm b
  have hH : normalizedWeightedSource w (H b) = χ := rfl
  let G := normalizedWeightedEtaSequence (by simp) (by norm_num) s w (sign:ℂ) (H b)
  have hG : ‖G‖ ≤ A := ((ha (sign:ℂ) hs).2 (H b) hb.2).1
  have hGc (n : ℤ) : G n = (w (2*n):ℂ)*sourceGapWeightedEtaCoordinate (by simp) (by norm_num) n s (sign:ℂ) χ := by
    simpa only [hH] using ((ha (sign:ℂ) hs).2 (H b) hb.2).2 n
  have hmajor (n : ℤ) : ‖((Weight.sobolev m n):ℂ)*sourceGapWeightedEtaCoordinate (by simp) (by norm_num)
      n s (sign:ℂ) χ‖ ≤ ‖G n‖ := by
    rw [hGc,norm_mul,norm_mul,Complex.norm_real,Complex.norm_real,
      Real.norm_of_nonneg ((Weight.sobolev m).positive n).le,Real.norm_of_nonneg (w.positive _).le]
    apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
    simp only [w,SpectralWeight.sobolev_apply,Weight.sobolev_apply,Real.rpow_natCast,
      Int.cast_mul,Int.cast_ofNat,abs_mul,abs_of_nonneg (by norm_num : (0:ℝ) ≤ 2)]
    apply pow_le_pow_left₀ (by positivity)
    linarith [abs_nonneg (n:ℝ)]
  let c : WeightedCoeff (Weight.sobolev m) 2 :=
    ⟨fun n => sourceGapWeightedEtaCoordinate (by simp) (by norm_num) n s (sign:ℂ) χ,
      (lp.memℓp G).mono' hmajor⟩
  have hc : ‖c‖ ≤ A := by
    change ‖WeightedCoeff.weightEquiv (Weight.sobolev m) 2 c‖ ≤ A
    exact (lp.norm_mono (by norm_num : (2:ℝ≥0∞) ≠ 0) hmajor).trans hG
  obtain ⟨T,hT,hnT⟩ := hn (J b) hb.1.1 2 inferInstance m sign
  obtain ⟨S,hS,hnS⟩ := he (J b) hb.1.2 2 inferInstance m (-sign)
  have ht : ‖T‖ ≤ 2*K*Real.exp K := by
    simpa only [habs,one_mul,show (1:ℝ)+1=2 by norm_num,mul_comm K 2] using hnT
  have hu : ‖S‖ ≤ L*Real.exp L := by simpa only [abs_neg,habs,one_mul] using hnS
  refine ⟨T c-S c,?_,?_⟩
  · intro n
    rw [WeightedCoeff.sub_val,hT,hS,hJ]
    simp only [Complex.ofReal_neg]
    rw [sourceGapWeightedEtaTerminalCoordinate_eq_inverse_phase (by simp) (by norm_num) n s]
    change (_-1)*sourceGapWeightedEtaCoordinate (by simp) (by norm_num) n s (sign:ℂ) χ-
      (_-1)*sourceGapWeightedEtaCoordinate (by simp) (by norm_num) n s (sign:ℂ) χ = _
    simp only [sourceBirkhoffWeightedCoordinate]
    ring
  · have htbound := (T.le_opNorm c).trans (mul_le_mul ht hc (norm_nonneg _) (by positivity))
    have hubound := (S.le_opNorm c).trans (mul_le_mul hu hc (norm_nonneg _) (by positivity))
    exact (norm_sub_le (T c) (S c)).trans ((add_le_add htbound hubound).trans_eq (by dsimp only [M]; ring))

end NLS.ZakharovShabat.SourceBirkhoffMapComplexData
