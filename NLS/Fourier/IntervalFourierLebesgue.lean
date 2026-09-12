import NLS.Fourier.FractionalPeriodization
import NLS.Fourier.FractionalIntervalEmbedding
import NLS.SequenceSpaces.HilbertSobolevEmbedding

/-!
# Appendix A.9: interval Fourier–Lebesgue membership

For the period-two model, intrinsic interval `Hˢ` regularity gives actual
Fourier coefficients in `ℓ^q` for `0<s<1/2` and `q>1/(s+1/2)`.
The zero-regularity case uses `L²` alone and permits `q=2`. Intrinsic half
regularity implies every finite target `q>1` by lowering regularity first.
The infinity target already follows from `L²`.
-/

noncomputable section
open MeasureTheory Set
open scoped ENNReal
namespace NLS.Fourier

/-- The source's strict target threshold implies both the Banach condition and the reciprocal Hölder inequality. -/
theorem intervalFourierLebesgue_threshold {s q : ℝ} (hs : 0 ≤ s) (hs₁ : s < 1 / 2)
    (hq : 1 / (s + 1 / 2) < q) : 1 < q ∧ 1 / q < s + 1 / 2 := by
  have hd : 0 < s + 1 / 2 := by linarith
  have hb : 1 < 1 / (s + 1 / 2) := (one_lt_div hd).mpr (by linarith)
  have hq₁ : 1 < q := hb.trans hq
  refine ⟨hq₁, (div_lt_iff₀ (by linarith : 0 < q)).mpr ?_⟩
  have h := (div_lt_iff₀ hd).mp hq
  nlinarith

/-- Actual interval Fourier coefficients in a finite target satisfying the reciprocal Hölder condition. -/
theorem memlp_periodTwoCoefficient_of_interval_reciprocal {s q : ℝ}
    (hs : 0 < s) (hs₁ : s < 1 / 2) (hq : 1 ≤ q) (h : 1 / q < s + 1 / 2)
    (f : ℝ → ℂ) (hf₂ : MemLp f 2 (volume.restrict (Ioc 0 2)))
    (hE : fractionalIntervalEnergy s 2 f < ⊤) :
    Memℓp (periodTwoCoefficient f) (ENNReal.ofReal q) := by
  let a : WeightedCoeff (Weight.sobolev s) 2 :=
    ⟨periodTwoCoefficient f, memlp_sobolev_periodTwoCoefficient_of_interval hs hs₁ f hf₂ hE⟩
  exact WeightedCoeff.memlp_of_hilbertSobolev hs.le hq h a

/-- Appendix A.9 for positive subcritical interval regularity, in the period-two model. -/
theorem memlp_periodTwoCoefficient_of_interval {s q : ℝ}
    (hs : 0 < s) (hs₁ : s < 1 / 2) (hq : 1 / (s + 1 / 2) < q)
    (f : ℝ → ℂ) (hf₂ : MemLp f 2 (volume.restrict (Ioc 0 2)))
    (hE : fractionalIntervalEnergy s 2 f < ⊤) :
    Memℓp (periodTwoCoefficient f) (ENNReal.ofReal q) :=
  memlp_periodTwoCoefficient_of_interval_reciprocal hs hs₁
    (intervalFourierLebesgue_threshold hs.le hs₁ hq).1.le
    (intervalFourierLebesgue_threshold hs.le hs₁ hq).2 f hf₂ hE

/-- The zero-regularity embedding requires only interval `L²`, including the target two and infinity. -/
theorem memlp_periodTwoCoefficient_of_memLp {q : ℝ≥0∞} (hq : 2 ≤ q)
    (f : ℝ → ℂ) (hf₂ : MemLp f 2 (volume.restrict (Ioc 0 2))) :
    Memℓp (periodTwoCoefficient f) q := by
  have h : Memℓp (periodTwoCoefficient f) 2 := (periodTwoL2Coefficients f hf₂).prop
  exact h.of_exponent_ge hq

/-- Bounded actual Fourier coefficients follow from interval square integrability alone. -/
theorem memlp_top_periodTwoCoefficient_of_memLp (f : ℝ → ℂ)
    (hf₂ : MemLp f 2 (volume.restrict (Ioc 0 2))) : Memℓp (periodTwoCoefficient f) ⊤ :=
  memlp_periodTwoCoefficient_of_memLp le_top f hf₂

/-- Appendix A.9 including `s=0`; the intrinsic energy hypothesis is vacuous at zero. -/
theorem memlp_periodTwoCoefficient_of_nonneg_interval {s q : ℝ}
    (hs : 0 ≤ s) (hs₁ : s < 1 / 2) (hq : 1 / (s + 1 / 2) < q)
    (f : ℝ → ℂ) (hf₂ : MemLp f 2 (volume.restrict (Ioc 0 2)))
    (hE : 0 < s → fractionalIntervalEnergy s 2 f < ⊤) :
    Memℓp (periodTwoCoefficient f) (ENNReal.ofReal q) := by
  rcases eq_or_lt_of_le hs with he | hp
  · subst s
    have hq₂ : 2 ≤ q := by norm_num at hq; linarith
    apply memlp_periodTwoCoefficient_of_memLp _ f hf₂
    exact_mod_cast ENNReal.ofReal_le_ofReal hq₂
  · exact memlp_periodTwoCoefficient_of_interval hp hs₁ hq f hf₂ (hE hp)

/-- A smaller positive regularity exists for every finite target strictly above one. -/
theorem exists_subcritical_regularity {q : ℝ} (hq : 1 < q) :
    ∃ t : ℝ, 0 < t ∧ t < 1 / 2 ∧ 1 / q < t + 1 / 2 := by
  have hqpos : 0 < q := by linarith
  have hi : 1 / q < 1 := (div_lt_one hqpos).mpr hq
  have hm : max 0 (1 / q - 1 / 2) < (1 / 2 : ℝ) := max_lt (by norm_num) (by linarith)
  obtain ⟨t, ht, ht₁⟩ := exists_between hm
  refine ⟨t, (le_max_left _ _).trans_lt ht, ht₁, ?_⟩
  have h := (le_max_right _ _).trans_lt ht
  linarith

/-- The separate half-regularity conclusion of Appendix A.9, without periodizing at the critical index. -/
theorem memlp_periodTwoCoefficient_of_half_interval {q : ℝ} (hq : 1 < q)
    (f : ℝ → ℂ) (hf₂ : MemLp f 2 (volume.restrict (Ioc 0 2)))
    (hE : fractionalIntervalEnergy (1 / 2) 2 f < ⊤) :
    Memℓp (periodTwoCoefficient f) (ENNReal.ofReal q) := by
  obtain ⟨t, ht, ht₁, htq⟩ := exists_subcritical_regularity hq
  exact memlp_periodTwoCoefficient_of_interval_reciprocal ht ht₁ hq.le htq f hf₂
    (fractionalIntervalEnergy_lt_top_of_regularity ht.le ht₁.le (by norm_num) f hE)

end NLS.Fourier
