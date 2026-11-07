import NLS.Articles.KdVPseudomeasures.SourceWienerCouplingEnvelope
import NLS.Articles.KdVPseudomeasures.SourceWienerSpectralValues
import NLS.KdV.HillGapFromCouplingEnvelope
import NLS.SequenceSpaces.DoubledPairL1Majorant

/-! One summable tail envelope for BOTH actual original complex Wiener
spectral sequences. The cutoff precedes every weight and entire norm ball. -/
noncomputable section
open scoped ENNReal
open NLS.KdV NLS.Fourier NLS.Fourier.PeriodicFourierLebesgue
namespace NLS.Articles.KdVPseudomeasures

theorem exists_uniform_sourceWienerHighSpectral_envelope (R : ℝ) :
    ∃ N : ℕ, 2 ≤ N ∧ ∀ w : SpectralWeight,
      ∀ q : PeriodicFourierLebesgue (2:ℝ) (w.negativeSobolev 0) 1, ‖q‖ ≤ R →
        ∃ H : Coeff 1, ‖H‖ ≤ 2*‖q‖ ∧
          ∀ hp : IsPeriodicDistribution 1 q.val.toTempered,
            ∀ n : ℕ+, N ≤ (n:ℕ) →
              w (n:ℤ)*‖sourceWienerGapValues w q (n:ℤ)‖ ≤
                Real.sqrt 6*‖Coeff.doubledPairMajorant H (n:ℤ)‖ ∧
              w (n:ℤ)*‖sourceWienerMidpointValues w q hp (n:ℤ)‖ ≤
                (128*(Real.sqrt 6+1))*‖Coeff.doubledPairMajorant H (n:ℤ)‖ := by
  obtain ⟨NC,hNC,hC⟩ := exists_uniform_sourceWienerCoupling_envelope R
  obtain ⟨NL,_,_,hL⟩ := source_uniform_canonical_complex_labels_with_contraction 0 sourceWienerAdmissible R
  obtain ⟨NM,_,_,hM⟩ := exists_uniform_sourceComplexMidpoint_coupling_bound 0 sourceWienerAdmissible R 2
  let N := max NC (max NL NM)
  have hN : 2 ≤ N := hNC.trans (le_max_left _ _)
  refine ⟨N,hN,?_⟩
  intro w q hq
  obtain ⟨H,hH,hcoupling⟩ := hC w q hq
  refine ⟨H,hH,?_⟩
  intro hp n hn
  let u := sourceWienerPlain w q
  have hu : ‖u‖ ≤ R := (norm_sourceWienerPlain_le w q).trans hq
  have hup : IsPeriodicDistribution 1 u.val.toTempered := by rw [sourceWienerPlain_val]; exact hp
  have hnC : NC ≤ (n:ℕ) := (le_max_left _ _).trans hn
  have hnL : NL ≤ (n:ℕ) := by dsimp [N] at hn; omega
  have hnM : NM ≤ (n:ℕ) := by dsimp [N] at hn; omega
  have hlabels := hL u hu
  obtain ⟨p,hl,hrr⟩ := hlabels.high_pair (n:ℕ) hnL
  have hs := endpointHill_small_of_wide_small 0 (by norm_num) (n:ℕ) (sourceEndpointCoefficients 0 u)
    (by simpa only [norm_sourceEndpointCoefficients] using hlabels.cutoff_small (n:ℕ) hnL)
  let U := ‖H (2*(n:ℤ))‖
  let L := ‖H (-(2*(n:ℤ)))‖
  have hbc := hcoupling (n:ℕ) n.property hnC
  have hgap2 := p.gap_le_of_coupling_envelope (n:ℕ) n.property (sourceEndpointCoefficients 0 u) hs
    (w (2*(n:ℤ))) U L (w.positive _) (norm_nonneg _) (norm_nonneg _) hbc
  have hweight : w (n:ℤ) ≤ w (2*(n:ℤ)) := w.mono_abs (by
    rw [abs_of_nonneg (by positivity : (0:ℤ) ≤ (n:ℤ)), abs_of_nonneg (by positivity : (0:ℤ) ≤ 2*(n:ℤ))]
    omega)
  have hgap : w (n:ℤ)*‖p.right-p.left‖ ≤ Real.sqrt 6*(U+L) :=
    (mul_le_mul_of_nonneg_right hweight (norm_nonneg _)).trans hgap2
  have hraw : sourceWienerGapValues w q (n:ℤ) = p.right-p.left := by
    have h := sourceWienerGapValues_nat w q (n:ℕ) n.property
    exact h.trans (by rw [hl,hrr])
  have hg : w (n:ℤ)*‖sourceWienerGapValues w q (n:ℤ)‖ ≤ Real.sqrt 6*(U+L) :=
    (congrArg (fun c : ℂ => w (n:ℤ)*‖c‖) hraw).le.trans hgap
  have hm := hM u hu hup n hnM
  have hmr : ‖sourceComplexDirichletMidpoint 0 sourceWienerAdmissible u hup n‖ ≤
      128*(‖p.right-p.left‖+
        ‖endpointUpperCoupling 0 (by norm_num) (by norm_num) (n:ℕ) (sourceEndpointCoefficients 0 u,p.right)‖+
        ‖endpointLowerCoupling 0 (by norm_num) (by norm_num) (n:ℕ) (sourceEndpointCoefficients 0 u,p.right)‖) := by
    dsimp only at hm
    rwa [hl,hrr] at hm
  obtain ⟨hb,hc⟩ := hbc p.right p.right_mem
  have hb' : w (n:ℤ)*‖endpointUpperCoupling 0 (by norm_num) (by norm_num) (n:ℕ)
      (sourceEndpointCoefficients 0 u,p.right)‖ ≤ U :=
    (mul_le_mul_of_nonneg_right hweight (norm_nonneg _)).trans hb
  have hc' : w (n:ℤ)*‖endpointLowerCoupling 0 (by norm_num) (by norm_num) (n:ℕ)
      (sourceEndpointCoefficients 0 u,p.right)‖ ≤ L :=
    (mul_le_mul_of_nonneg_right hweight (norm_nonneg _)).trans hc
  have hmid : w (n:ℤ)*‖sourceComplexDirichletMidpoint 0 sourceWienerAdmissible u hup n‖ ≤
      (128*(Real.sqrt 6+1))*(U+L) := by
    have hw := mul_le_mul_of_nonneg_left hmr (w.positive (n:ℤ)).le
    nlinarith
  have hmidraw := sourceWienerMidpointValues_nat w q hp n
  have hmid' : w (n:ℤ)*‖sourceWienerMidpointValues w q hp (n:ℤ)‖ ≤
      (128*(Real.sqrt 6+1))*(U+L) :=
    (congrArg (fun c : ℂ => w (n:ℤ)*‖c‖) hmidraw).le.trans hmid
  have hpair : ‖Coeff.doubledPairMajorant H (n:ℤ)‖ = U+L := Coeff.norm_doubledPairMajorant_apply H _
  exact ⟨hg.trans_eq (congrArg (fun x : ℝ => Real.sqrt 6*x) hpair.symm),
    hmid'.trans_eq (congrArg (fun x : ℝ => (128*(Real.sqrt 6+1))*x) hpair.symm)⟩

end NLS.Articles.KdVPseudomeasures
