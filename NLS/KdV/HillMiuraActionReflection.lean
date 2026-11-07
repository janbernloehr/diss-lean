import NLS.KdV.HillMiuraInverseMoment
import NLS.ZakharovShabat.SourceRealHigherAction

/-! Reflection of ACTUAL diagonal Dirac gap moments. Endpoint order,
discriminant parity and the cosine substitution pi-theta retain the
original signed indices and every natural spectral-power normalization. -/
noncomputable section
open Set Complex NLS.ZakharovShabat
namespace NLS.KdV

theorem hillMiura_realGapAffinePoint_neg (u : Coeff 2) (n : ℤ) (t : ℝ) :
    realGapAffinePoint (by simp) (by norm_num) (hillMiuraDiagonal u) (-n) (-t)=
      -realGapAffinePoint (by simp) (by norm_num) (hillMiuraDiagonal u) n t := by
  change ((hillMiuraDiracLeft u (-n)).re+(hillMiuraDiracRight u (-n)).re)/2+
    ((hillMiuraDiracRight u (-n)).re-(hillMiuraDiracLeft u (-n)).re)/2*(-t)=
      -(((hillMiuraDiracLeft u n).re+(hillMiuraDiracRight u n).re)/2+
        ((hillMiuraDiracRight u n).re-(hillMiuraDiracLeft u n).re)/2*t)
  rw [(hillMiuraDiracPair_neg u).1 n,(hillMiuraDiracPair_neg u).2 n]
  simp only [neg_re]
  ring

theorem hillMiura_realGapArcoshProfile_neg (u : Coeff 2) (n : ℤ) (x : ℝ) :
    sourceRealGapArcoshProfile (by simp) (hillMiuraDiagonal u) (-n) (-x)=
      sourceRealGapArcoshProfile (by simp) (hillMiuraDiagonal u) n x := by
  have hn : (-n)%2=n%2 := by omega
  have hD : canonicalDiscriminant (by simp) (periodOnePotential (hillMiuraDiagonal u)) ((-x:ℝ):ℂ)=
      canonicalDiscriminant (by simp) (periodOnePotential (hillMiuraDiagonal u)) (x:ℂ) := by
    simpa only [hillMiuraFrequencyTrace,Complex.ofReal_neg] using hillMiuraFrequencyTrace_even u (x:ℂ)
  unfold sourceRealGapArcoshProfile realGapHalfDiscriminant
  rw [hn,hD]

theorem hillMiura_realGapCosineProfile_neg (u : Coeff 2) (n : ℤ) (θ : ℝ) :
    sourceRealGapCosineProfile (by simp) (by norm_num) (hillMiuraDiagonal u) (-n) (Real.pi-θ)=
      sourceRealGapCosineProfile (by simp) (by norm_num) (hillMiuraDiagonal u) n θ := by
  unfold sourceRealGapCosineProfile
  rw [Real.cos_pi_sub,hillMiura_realGapAffinePoint_neg,hillMiura_realGapArcoshProfile_neg]

/-- Every ACTUAL spectrally weighted real gap action has its exact parity. -/
theorem hillMiura_realHigherAction_neg (u : PeriodOneRealL2) (n : ℤ) (k : ℕ) :
    sourceRealHigherAction (by simp) (by norm_num) (hillMiuraRealSource u) (-n) k=
      (-1:ℝ)^k*sourceRealHigherAction (by simp) (by norm_num) (hillMiuraRealSource u) n k := by
  let ψ := hillMiuraDiagonal u.val
  have hg : canonicalPeriodicGap (by simp) (by norm_num) (periodOnePotential ψ) (periodOnePotential_mem _) (-n)=
      canonicalPeriodicGap (by simp) (by norm_num) (periodOnePotential ψ) (periodOnePotential_mem _) n := by
    change hillMiuraDiracRight u.val (-n)-hillMiuraDiracLeft u.val (-n)=
      hillMiuraDiracRight u.val n-hillMiuraDiracLeft u.val n
    rw [(hillMiuraDiracPair_neg u.val).1 n,(hillMiuraDiracPair_neg u.val).2 n]
    ring
  let f : ℤ → ℝ → ℝ := fun j θ => (realGapAffinePoint (by simp) (by norm_num) ψ j (Real.cos θ))^k *
    (Real.sin θ*sourceRealGapCosineProfile (by simp) (by norm_num) ψ j θ)
  have hi : (∫ θ in (0:ℝ)..Real.pi, f (-n) θ)=(-1:ℝ)^k*(∫ θ in (0:ℝ)..Real.pi, f n θ) := by
    have hsub := intervalIntegral.integral_comp_sub_left (f (-n)) Real.pi (a := 0) (b := Real.pi)
    simp only [sub_self,sub_zero] at hsub
    rw [← hsub,← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro θ _
    dsimp only [f,ψ]
    rw [Real.cos_pi_sub,hillMiura_realGapAffinePoint_neg,Real.sin_pi_sub,
      hillMiura_realGapCosineProfile_neg,neg_pow]
    ring
  change (canonicalPeriodicGap (by simp) (by norm_num) (periodOnePotential ψ) (periodOnePotential_mem _) (-n)).re/Real.pi*
    (∫ θ in (0:ℝ)..Real.pi, f (-n) θ)=
    (-1:ℝ)^k*((canonicalPeriodicGap (by simp) (by norm_num) (periodOnePotential ψ) (periodOnePotential_mem _) n).re/Real.pi*
      (∫ θ in (0:ℝ)..Real.pi, f n θ))
  rw [hg,hi]
  ring

end NLS.KdV
