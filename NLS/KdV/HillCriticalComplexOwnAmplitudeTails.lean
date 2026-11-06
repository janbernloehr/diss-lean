import NLS.KdV.HillCriticalComplexOwnAmplitude
import NLS.SequenceSpaces.PositiveFourierTail
import NLS.SequenceSpaces.ReciprocalSquareTail

noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology
open scoped ENNReal Classical

namespace NLS.KdV



variable
    (h0q : SpectralWeight.one.toCoeff (0 : WeightedCoeff SpectralWeight.one.toWeight 2) ∈ Coeff.paritySubspace 0)
    (h0r : IsRealHillPotential (SpectralWeight.one.toCoeff (0 : WeightedCoeff SpectralWeight.one.toWeight 2)))

/-- Both original complex own amplitudes have the critical weighted square
tail bound, retaining the actual source Fourier remainder and quartic error. -/
theorem exists_hillComplexOwnCartesianAmplitudes_native_critical_tail_bound
    (B : ℝ) (hB : 0≤B) :
    ∃ C : ℝ, 0<C ∧ ∃ N0 : ℕ, 1≤N0 ∧ ∀ w : SpectralWeight,
      ∀ q : WeightedCoeff w.doubleIndex.toWeight 2, ‖q‖≤B → ∀ N : ℕ, N0≤N →
      (Summable (fun k : ℕ => (k+N : ℕ)*(w (2*((k+N : ℕ) : ℤ)))^2*
          ‖hillComplexOwnCartesianAmplitude h0q h0r (k+N) (hillPeriodOneCoefficientMap w q)‖^2) ∧
      (∑' k : ℕ, (k+N : ℕ)*(w (2*((k+N : ℕ) : ℤ)))^2*
          ‖hillComplexOwnCartesianAmplitude h0q h0r (k+N) (hillPeriodOneCoefficientMap w q)‖^2) ≤
        C*‖Coeff.fourierTail N (WeightedCoeff.weightEquiv w.doubleIndex.toWeight 2 q)‖^2+
          512*C*‖q‖^4/(N : ℝ)) ∧
      (Summable (fun k : ℕ => (k+N : ℕ)*(w (2*((k+N : ℕ) : ℤ)))^2*
          ‖hillComplexOwnCartesianDualAmplitude h0q h0r (k+N) (hillPeriodOneCoefficientMap w q)‖^2) ∧
      (∑' k : ℕ, (k+N : ℕ)*(w (2*((k+N : ℕ) : ℤ)))^2*
          ‖hillComplexOwnCartesianDualAmplitude h0q h0r (k+N) (hillPeriodOneCoefficientMap w q)‖^2) ≤
        C*‖Coeff.fourierTail N (WeightedCoeff.weightEquiv w.doubleIndex.toWeight 2 q)‖^2+
          512*C*‖q‖^4/(N : ℝ)) := by
  obtain ⟨C,hC,N0,hN0,hpoint⟩ :=
    exists_hillComplexOwnCartesianAmplitudes_native_critical_pointwise_bound h0q h0r B hB
  refine ⟨C,hC,N0,hN0,?_⟩
  intro w q hq N hN
  have hN1 : 1≤N := hN0.trans hN
  let a := WeightedCoeff.weightEquiv w.doubleIndex.toWeight 2 q
  let A := fun k : ℕ => ‖a ((k : ℤ)+N)‖^2+‖a (-((k : ℤ)+N))‖^2
  let R := fun k : ℕ => 1/((k : ℝ)+N)^2
  let D := 256*‖q‖^4
  have hA : Summable A := (Coeff.positive_pair_tail_sq a N hN1).1
  have hAn : (∑' k, A k)≤‖Coeff.fourierTail N a‖^2 := (Coeff.positive_pair_tail_sq a N hN1).2
  have hR : Summable R := ReciprocalSeries.summable_nat_reciprocal_sq_tail N hN1
  have hRn : (∑' k, R k)≤2/(N : ℝ) := ReciprocalSeries.tsum_nat_reciprocal_sq_tail_le N hN1
  have hcoef (j : ℤ) : ‖a j‖^2=(w (2*j))^2*‖q.val j‖^2 :=
    hillPeriodOne_weighted_coefficient_sq w q j
  have hmajor : Summable (fun k : ℕ => C*A k+(C*D)*R k) :=
    (hA.mul_left C).add (hR.mul_left (C*D))
  have htail (f : ℕ → ℂ)
      (hf : ∀ n : ℕ, N≤n → (n : ℝ)*(w (2*(n : ℤ)))^2*‖f n‖^2 ≤
        C*((w (2*(n : ℤ)))^2*‖q.val n‖^2+(w (2*(n : ℤ)))^2*‖q.val (-(n : ℤ))‖^2+
          256*‖q‖^4/(n : ℝ)^2)) :
      Summable (fun k : ℕ => (k+N : ℕ)*(w (2*((k+N : ℕ) : ℤ)))^2*‖f (k+N)‖^2) ∧
      (∑' k : ℕ, (k+N : ℕ)*(w (2*((k+N : ℕ) : ℤ)))^2*‖f (k+N)‖^2) ≤
        C*‖Coeff.fourierTail N a‖^2+512*C*‖q‖^4/(N : ℝ) := by
    have hb (k : ℕ) : (k+N : ℕ)*(w (2*((k+N : ℕ) : ℤ)))^2*‖f (k+N)‖^2 ≤ C*A k+(C*D)*R k := by
      apply (hf (k+N) (by omega)).trans_eq
      dsimp only [A,R,D]
      rw [hcoef,hcoef,mul_neg,w.apply_neg]
      push_cast
      ring
    have hs := Summable.of_nonneg_of_le (fun k => by positivity) hb hmajor
    refine ⟨hs,?_⟩
    calc
      _ ≤ ∑' k : ℕ, (C*A k+(C*D)*R k) := hs.tsum_le_tsum hb hmajor
      _ = C*(∑' k, A k)+(C*D)*(∑' k, R k) := by
        rw [(hA.mul_left C).tsum_add (hR.mul_left (C*D)),tsum_mul_left,tsum_mul_left]
      _ ≤ C*‖Coeff.fourierTail N a‖^2+(C*D)*(2/(N : ℝ)) := by
        gcongr
      _ = _ := by dsimp only [D];ring
  constructor
  · exact htail (fun n => hillComplexOwnCartesianAmplitude h0q h0r n (hillPeriodOneCoefficientMap w q))
      (fun n hn => (hpoint w q hq n (hN.trans hn)).1)
  · exact htail (fun n => hillComplexOwnCartesianDualAmplitude h0q h0r n (hillPeriodOneCoefficientMap w q))
      (fun n hn => (hpoint w q hq n (hN.trans hn)).2)

end NLS.KdV
