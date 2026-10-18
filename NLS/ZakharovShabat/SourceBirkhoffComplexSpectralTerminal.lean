import NLS.ZakharovShabat.SourceNormalizationComplexPhaseSmoothing
import NLS.ZakharovShabat.SourceEtaRemainderComplexSmoothing

/-! # Locally bounded complex angular error in h2

Both actual signed Birkhoff-minus-terminal errors belong to h2 on one complex neighborhood of every normalized first-order Sobolev real source. This is the angular part of the Fourier comparison.
-/

noncomputable section
open Set Metric Complex Filter Topology
open scoped ENNReal
namespace NLS.ZakharovShabat.SourceBirkhoffMapComplexData
variable {W₀ B W : Set (CoeffPair 2)} {s : (n : ℤ) → CoeffPair 2 → DeletedCoeff 2 n}
variable (D : SourceBirkhoffMapComplexData (by simp) (by norm_num) W₀ B W s)
include D

set_option maxHeartbeats 400000 in
/-- Both actual signed Birkhoff-minus-terminal errors are locally bounded in h2 over complex first-order Sobolev sources. -/
theorem exists_local_normalizedSobolevBirkhoffSpectralTerminal_bound (φ : realTypeSourceLocus 2) :
    ∃ U : Set (CoeffPair 2), IsOpen U ∧ φ.val ∈ U ∧
      ∃ M : ℝ, 0 ≤ M ∧ ∀ ψ ∈ U, ∀ sign : ℝ, sign=1 ∨ sign= -1 →
        ∃ z : WeightedCoeff (Weight.sobolev 2) 2,
          (∀ n, z.val n = sourceBirkhoffWeightedCoordinate (by simp) (by norm_num) n s (sign:ℂ)
              (normalizedWeightedSource (SpectralWeight.sobolev 1 (by norm_num)) ψ)-
            sourceGapWeightedEtaTerminalCoordinate (by simp) (by norm_num) n (sign:ℂ)
              (normalizedWeightedSource (SpectralWeight.sobolev 1 (by norm_num)) ψ)) ∧ ‖z‖ ≤ M := by
  let w := SpectralWeight.sobolev 1 (by norm_num)
  obtain ⟨Vn,hVn,hφn,K,hK,hn⟩ := D.exists_local_normalizedSobolevNormalizationPhase_smoothing φ
  obtain ⟨Ve,hVe,hφe,L,hL,he⟩ := D.exists_local_normalizedSobolevEtaRemainder_phase_smoothing φ
  obtain ⟨Va,hVa,hφa,A,hA,ha⟩ := D.exists_local_normalizedWeightedEta_analytic w φ
  let U := (Vn ∩ Ve) ∩ Va
  let M := (2*K*Real.exp K+L*Real.exp L)*A
  refine ⟨U,(hVn.inter hVe).inter hVa,⟨⟨hφn,hφe⟩,hφa⟩,M,by dsimp only [M]; positivity,?_⟩
  intro ψ hψ sign hsign
  have hs : (sign:ℂ)=1 ∨ (sign:ℂ)= -1 := by rcases hsign with rfl | rfl <;> simp
  have habs : |sign|=1 := by rcases hsign with rfl | rfl <;> norm_num
  let χ := normalizedWeightedSource w ψ
  let G := normalizedWeightedEtaSequence (by simp) (by norm_num) s w (sign:ℂ) ψ
  obtain ⟨_,hb⟩ := ha (sign:ℂ) hs
  have hG : ‖G‖ ≤ A := (hb ψ hψ.2).1
  have hGc : ∀ n, G n = (w (2*n):ℂ)*sourceGapWeightedEtaCoordinate (by simp) (by norm_num) n s (sign:ℂ) χ :=
    (hb ψ hψ.2).2
  have hmajor (n : ℤ) : ‖((Weight.sobolev 1 n):ℂ)*sourceGapWeightedEtaCoordinate (by simp) (by norm_num)
      n s (sign:ℂ) χ‖ ≤ ‖G n‖ := by
    rw [hGc,norm_mul,norm_mul,Complex.norm_real,Complex.norm_real,
      Real.norm_of_nonneg ((Weight.sobolev 1).positive n).le,Real.norm_of_nonneg (w.positive _).le]
    apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
    simp only [w,SpectralWeight.sobolev_apply,Weight.sobolev_apply,Real.rpow_one,
      Int.cast_mul,Int.cast_ofNat,abs_mul,abs_of_nonneg (by norm_num : (0:ℝ) ≤ 2)]
    linarith [abs_nonneg (n:ℝ)]
  let c : WeightedCoeff (Weight.sobolev 1) 2 :=
    ⟨fun n => sourceGapWeightedEtaCoordinate (by simp) (by norm_num) n s (sign:ℂ) χ,
      (lp.memℓp G).mono' hmajor⟩
  have hc : ‖c‖ ≤ A := by
    change ‖WeightedCoeff.weightEquiv (Weight.sobolev 1) 2 c‖ ≤ A
    exact (lp.norm_mono (by norm_num : (2:ℝ≥0∞) ≠ 0) hmajor).trans hG
  have hn' := hn ψ hψ.1.1 2 inferInstance 1 sign
  have he' := he ψ hψ.1.2 2 inferInstance 1 (-sign)
  rw [show (1:ℝ)+1=2 by norm_num] at hn' he'
  obtain ⟨T,hT,hnT⟩ := hn'
  obtain ⟨S,hS,hnS⟩ := he'
  have ht : ‖T‖ ≤ 2*K*Real.exp K := by simpa only [habs,one_mul,show (1:ℝ)+1=2 by norm_num,mul_comm K 2] using hnT
  have hu : ‖S‖ ≤ L*Real.exp L := by simpa only [abs_neg,habs,one_mul] using hnS
  refine ⟨T c-S c,?_,?_⟩
  · intro n
    rw [WeightedCoeff.sub_val,hT,hS]
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
