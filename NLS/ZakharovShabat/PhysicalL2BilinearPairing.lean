import NLS.Fourier.ArbitraryPeriodBilinearParseval
import NLS.ZakharovShabat.SourcePhysicalL2Equiv
import NLS.SequenceSpaces.SourceCotangent
import NLS.SequenceSpaces.FullDuality

/-! # Bilinear physical L2 pairing

Products of arbitrary physical L2 representatives are integrable. The
literal bilinear integral agrees with Fourier duality after reflection.
Testing all L2 directions separates physical pairs, without additional
regularity or endpoint conditions.
-/

noncomputable section
open Set MeasureTheory Complex Filter Topology NLS.ComplexAnalysis
open scoped ENNReal Classical
namespace NLS.ZakharovShabat
open NLS.Poisson NLS.Fourier

/-- Products of arbitrary physical L2 representatives are integrable. -/
theorem physicalL2_intervalIntegrable_mul (u v : IntervalL2) :
    IntervalIntegrable (fun x => u x*v x) volume 0 1 := by
  apply (intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num : (0:ℝ) ≤ 1)).mpr
  exact (Lp.memLp u).integrable_mul (Lp.memLp v)

/-- Reflection converts the literal physical bilinear integral to same-index Fourier duality. -/
theorem physicalL2_reflected_pairing (a b : Coeff 2) :
    (∫ x in (0:ℝ)..1, unitL2SynthesisEquiv (Coeff.reflection a) x*unitL2SynthesisEquiv b x) =
      Coeff.dualPairing a b := by
  have h := hasSum_bilinear_intervalFourierCoefficient (by norm_num : (0:ℝ) < 1)
    (Lp.memLp (unitL2SynthesisEquiv (Coeff.reflection a))) (Lp.memLp (unitL2SynthesisEquiv b))
  have hc (c : Coeff 2) (n : ℤ) : intervalFourierCoefficient 1 (unitL2SynthesisEquiv c) n = c n :=
    unitL2SynthesisLinear_coefficient c n
  simp only [hc,Coeff.reflection_apply,neg_neg,Complex.ofReal_one,inv_one,one_mul] at h
  exact h.tsum_eq.symm

/-- The physical pair integral retains the Fourier reversal in each component. -/
theorem physicalL2_pairing_source (a b : CoeffPair 2) :
    (∫ x in (0:ℝ)..1, (sourcePhysicalL2Equiv a).fst x*(sourcePhysicalL2Equiv b).fst x+
      (sourcePhysicalL2Equiv a).snd x*(sourcePhysicalL2Equiv b).snd x) =
      Coeff.dualPairing (Coeff.reflection a.fst) b.fst+
      Coeff.dualPairing (Coeff.reflection a.snd) b.snd := by
  rw [intervalIntegral.integral_add (physicalL2_intervalIntegrable_mul _ _) (physicalL2_intervalIntegrable_mul _ _)]
  have h1 := physicalL2_reflected_pairing (Coeff.reflection a.fst) b.fst
  have h2 := physicalL2_reflected_pairing (Coeff.reflection a.snd) b.snd
  change (∫ x in (0:ℝ)..1, unitL2SynthesisEquiv a.fst x*unitL2SynthesisEquiv b.fst x)+
    (∫ x in (0:ℝ)..1, unitL2SynthesisEquiv a.snd x*unitL2SynthesisEquiv b.snd x) = _
  simpa only [Coeff.reflection_reflection] using congrArg₂ (fun x y : ℂ => x+y) h1 h2

/-- Literal physical bilinear pairings distinguish all L2 pairs. -/
theorem physicalL2_pairing_ext (g k : IntervalPairL2)
    (he : ∀ h : IntervalPairL2,
      (∫ x in (0:ℝ)..1, g.fst x*h.fst x+g.snd x*h.snd x) =
      (∫ x in (0:ℝ)..1, k.fst x*h.fst x+k.snd x*h.snd x)) : g = k := by
  let a := sourcePhysicalL2Equiv.symm g
  let b := sourcePhysicalL2Equiv.symm k
  have hp (c : CoeffPair 2) :
      Coeff.dualPairing (Coeff.reflection a.fst) c.fst+Coeff.dualPairing (Coeff.reflection a.snd) c.snd =
      Coeff.dualPairing (Coeff.reflection b.fst) c.fst+Coeff.dualPairing (Coeff.reflection b.snd) c.snd := by
    rw [← physicalL2_pairing_source,← physicalL2_pairing_source]
    simpa only [a,b,LinearIsometryEquiv.apply_symm_apply] using he (sourcePhysicalL2Equiv c)
  have hab : a = b := by
    apply WithLp.ofLp_injective
    apply Prod.ext
    · ext n
      change a.fst n = b.fst n
      simpa only [CoeffPair.inlCLM_fst,CoeffPair.inlCLM_snd,map_zero,add_zero,
        Coeff.dualPairing_single,Coeff.reflection_apply,neg_neg] using hp (CoeffPair.inlCLM (lp.single 2 (-n) 1))
    · ext n
      change a.snd n = b.snd n
      simpa only [CoeffPair.inrCLM_fst,CoeffPair.inrCLM_snd,map_zero,zero_add,
        Coeff.dualPairing_single,Coeff.reflection_apply,neg_neg] using hp (CoeffPair.inrCLM (lp.single 2 (-n) 1))
  exact sourcePhysicalL2Equiv.symm.injective hab

end NLS.ZakharovShabat
