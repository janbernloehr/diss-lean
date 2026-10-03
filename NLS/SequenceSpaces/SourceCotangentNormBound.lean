import NLS.SequenceSpaces.SourceCotangent
import NLS.SequenceSpaces.ConjugateDuality

/-! # Source cotangent bounds from conjugate Fourier coefficients

Values on the unit Fourier directions determine continuous functionals
at finite exponents. Hölder duality then bounds the source cotangent norm
by the sum of the two conjugate coefficient norms.
-/

noncomputable section
open scoped ENNReal
namespace NLS
variable {p q : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ q)] [q.HolderConjugate p]

/-- Unit Fourier values identify an actual functional with coefficient duality. -/
theorem Coeff.eq_dualPairing_of_single (hp : p ≠ ⊤) (L : Coeff p →L[ℂ] ℂ) (a : Coeff q)
    (ha : ∀ n : ℤ, L (lp.single p n 1) = a n) : L = Coeff.dualPairing a := by
  apply lp.ext_continuousLinearMap hp
  intro n
  apply ContinuousLinearMap.ext
  intro z
  change L (lp.single p n z) = Coeff.dualPairing a (lp.single p n z)
  have hz : (lp.single p n z : Coeff p) = z • lp.single p n (1 : ℂ) := by
    simpa only [smul_eq_mul,mul_one] using (lp.single_smul (E := fun _ : ℤ => ℂ) p n z (1 : ℂ))
  rw [hz,map_smul,ha]
  simp [Coeff.dualPairing_apply,lp.single_apply,Pi.single_apply,mul_comm]

/-- The two coefficient norms bound the actual source operator norm.
This uses the source pair norm, not the maximum product norm. -/
theorem CoeffPair.norm_cotangent_le_of_single (hp : p ≠ ⊤)
    (L : CoeffPair p →L[ℂ] ℂ) (a b : Coeff q)
    (ha : ∀ n : ℤ, L (CoeffPair.inlCLM (lp.single p n 1)) = a n)
    (hb : ∀ n : ℤ, L (CoeffPair.inrCLM (lp.single p n 1)) = b n) :
    ‖L‖ ≤ ‖a‖+‖b‖ := by
  have hleft := Coeff.eq_dualPairing_of_single hp (L.comp CoeffPair.inlCLM) a ha
  have hright := Coeff.eq_dualPairing_of_single hp (L.comp CoeffPair.inrCLM) b hb
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro h
  have he : h = CoeffPair.inlCLM h.fst+CoeffPair.inrCLM h.snd := by
    apply (CoeffPair.toMax p).injective
    apply Prod.ext <;> simp
  have hval : L h = Coeff.dualPairing a h.fst+Coeff.dualPairing b h.snd := by
    calc
      L h = L (CoeffPair.inlCLM h.fst)+L (CoeffPair.inrCLM h.snd) := by rw [← map_add,← he]
      _ = _ := by rw [← ContinuousLinearMap.comp_apply L CoeffPair.inlCLM,
        ← ContinuousLinearMap.comp_apply L CoeffPair.inrCLM,hleft,hright]
  rw [hval,add_mul]
  exact (norm_add_le _ _).trans ((add_le_add (Coeff.norm_dualPairing_le a h.fst)
    (Coeff.norm_dualPairing_le b h.snd)).trans (add_le_add
      (mul_le_mul_of_nonneg_left (WithLp.norm_fst_le _ h) (norm_nonneg _))
      (mul_le_mul_of_nonneg_left (WithLp.norm_snd_le _ h) (norm_nonneg _))))

end NLS
