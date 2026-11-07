import NLS.Articles.KdVPseudomeasures.SourceWienerHighSpectralEnvelope
import NLS.SequenceSpaces.FiniteTailL1Bound
import NLS.SequenceSpaces.EvenWeightedTailEnvelope

/-! BOTH full actual complex spectral sequences have weighted ell-one
realizations uniformly on every original Wiener norm ball. No real-potential
neighborhood, tail truncation or supplied spectral regularity is assumed. -/
noncomputable section
open scoped ENNReal
open NLS.KdV NLS.Fourier NLS.Fourier.PeriodicFourierLebesgue NLS.WeightedCoeff
namespace NLS.Articles.KdVPseudomeasures

theorem sourceWienerSpectralSequences_uniform_l1 (w : SpectralWeight) (R : ℝ) :
    ∃ B : ℝ, 0 ≤ B ∧
      ∀ q : PeriodicFourierLebesgue (2:ℝ) (w.negativeSobolev 0) 1, ‖q‖ ≤ R →
        ∀ hp : IsPeriodicDistribution 1 q.val.toTempered,
          ∃ G M : WeightedCoeff w.toWeight 1,
            (∀ k, G.val k=sourceWienerGapValues w q k) ∧
            (∀ k, M.val k=sourceWienerMidpointValues w q hp k) ∧ ‖G‖ ≤ B ∧ ‖M‖ ≤ B := by
  obtain ⟨N,hN,hhigh⟩ := exists_uniform_sourceWienerHighSpectral_envelope R
  obtain ⟨B₁,B₂,hB₁,hB₂,hfull⟩ := sourceWienerSpectralValues_uniform_infinity w R
  let C₁ := ((Coeff.lowFrequencies N).card:ℝ)*B₁+Real.sqrt 6*(4*|R|)
  let C₂ := ((Coeff.lowFrequencies N).card:ℝ)*B₂+(128*(Real.sqrt 6+1))*(4*|R|)
  have hC₁ : 0 ≤ C₁ := by dsimp [C₁]; positivity
  have hC₂ : 0 ≤ C₂ := by dsimp [C₂]; positivity
  refine ⟨C₁+C₂,add_nonneg hC₁ hC₂,?_⟩
  intro q hq hp
  obtain ⟨H,hH,hpoint⟩ := hhigh w q hq
  let g := Coeff.doubledPairMajorant H
  have hgnorm : ‖g‖ ≤ 4*|R| := by
    calc
      _ ≤ 2*‖H‖ := Coeff.norm_doubledPairMajorant_le H
      _ ≤ 2*(2*‖q‖) := mul_le_mul_of_nonneg_left hH (by norm_num)
      _ ≤ 4*|R| := by nlinarith [le_abs_self R]
  have hgapTail (k : ℤ) (hk : N ≤ k.natAbs) :
      ‖(w k:ℂ)*sourceWienerGapValues w q k‖ ≤ Real.sqrt 6*‖g k‖ :=
    even_weighted_tail_envelope w (sourceWienerGapValues w q) (sourceWienerGapValues_neg w q)
      H N (by omega) (Real.sqrt 6) (fun n hn => (hpoint hp n hn).1) k hk
  have hmidTail (k : ℤ) (hk : N ≤ k.natAbs) :
      ‖(w k:ℂ)*sourceWienerMidpointValues w q hp k‖ ≤ (128*(Real.sqrt 6+1))*‖g k‖ :=
    even_weighted_tail_envelope w (sourceWienerMidpointValues w q hp) (sourceWienerMidpointValues_neg w q hp)
      H N (by omega) (128*(Real.sqrt 6+1)) (fun n hn => (hpoint hp n hn).2) k hk
  obtain ⟨G,hG,hGn⟩ := exists_weighted_l1_of_uniform_prefix_and_tail w.toWeight
    (sourceWienerGapValues w q) g N B₁ (Real.sqrt 6) (Real.sqrt_nonneg 6)
    (fun k _ => (hfull q hq hp k).1) hgapTail
  obtain ⟨M,hM,hMn⟩ := exists_weighted_l1_of_uniform_prefix_and_tail w.toWeight
    (sourceWienerMidpointValues w q hp) g N B₂ (128*(Real.sqrt 6+1)) (by positivity)
    (fun k _ => (hfull q hq hp k).2) hmidTail
  have hGbound : ‖G‖ ≤ C₁ := hGn.trans (by dsimp [C₁]; gcongr)
  have hMbound : ‖M‖ ≤ C₂ := hMn.trans (by dsimp [C₂]; gcongr)
  exact ⟨G,M,hG,hM,hGbound.trans (le_add_of_nonneg_right hC₂),
    hMbound.trans (le_add_of_nonneg_left hC₁)⟩

end NLS.Articles.KdVPseudomeasures
