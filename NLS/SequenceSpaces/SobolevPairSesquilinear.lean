import NLS.SequenceSpaces.SobolevSesquilinearPairing
import NLS.SequenceSpaces.WeightedPairNormInfty

/-! # The sesquilinear dual product for the original signed pair spaces

The finite-exponent pair product and both conjugate endpoints retain the
source norms. The infinity space has its separate frequencywise sum norm.
-/
noncomputable section
open scoped ENNReal
namespace NLS
namespace WeightedCoeffPair
variable {p q : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ q)] [p.HolderConjugate q]

/-- The sum of the component sesquilinear products in the signed source basis. -/
def sobolevSesquilinearPairing (s : ℝ)
    (a : WeightedCoeffPair (Weight.sobolev s) p) (b : WeightedCoeffPair (Weight.sobolev (-s)) q) : ℂ :=
  WeightedCoeff.sobolevSesquilinearPairing s a.fst b.fst +
    WeightedCoeff.sobolevSesquilinearPairing s a.snd b.snd

theorem sobolevSesquilinearPairing_eq_tsum (s : ℝ)
    (a : WeightedCoeffPair (Weight.sobolev s) p) (b : WeightedCoeffPair (Weight.sobolev (-s)) q) :
    sobolevSesquilinearPairing s a b = ∑' n : ℤ,
      (a.fst.val n*star (b.fst.val n)+a.snd.val n*star (b.snd.val n)) := by
  rw [sobolevSesquilinearPairing,WeightedCoeff.sobolevSesquilinearPairing_apply,
    WeightedCoeff.sobolevSesquilinearPairing_apply,
    ← (WeightedCoeff.summable_norm_sobolevSesquilinearPairing s a.fst b.fst).of_norm.tsum_add
      (WeightedCoeff.summable_norm_sobolevSesquilinearPairing s a.snd b.snd).of_norm]

theorem sobolevSesquilinearPairing_summable (s : ℝ)
    (a : WeightedCoeffPair (Weight.sobolev s) p) (b : WeightedCoeffPair (Weight.sobolev (-s)) q) :
    Summable (fun n : ℤ => ‖a.fst.val n*star (b.fst.val n)+a.snd.val n*star (b.snd.val n)‖) :=
  Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun _ => norm_add_le _ _)
    ((WeightedCoeff.summable_norm_sobolevSesquilinearPairing s a.fst b.fst).add
      (WeightedCoeff.summable_norm_sobolevSesquilinearPairing s a.snd b.snd))

/-- A uniform bound in the source norms (not asserted sharp). -/
theorem norm_sobolevSesquilinearPairing_le (s : ℝ)
    (a : WeightedCoeffPair (Weight.sobolev s) p) (b : WeightedCoeffPair (Weight.sobolev (-s)) q) :
    ‖sobolevSesquilinearPairing s a b‖ ≤ 2*‖a‖*‖b‖ := by
  apply (norm_add_le _ _).trans
  calc
    _ ≤ ‖a.fst‖*‖b.fst‖+‖a.snd‖*‖b.snd‖ := add_le_add
      (WeightedCoeff.norm_sobolevSesquilinearPairing_le s _ _)
      (WeightedCoeff.norm_sobolevSesquilinearPairing_le s _ _)
    _ ≤ ‖a‖*‖b‖+‖a‖*‖b‖ := by
      gcongr
      · exact WithLp.norm_fst_le _ a
      · exact WithLp.norm_fst_le _ b
      · exact WithLp.norm_snd_le _ a
      · exact WithLp.norm_snd_le _ b
    _ = _ := by ring

/-- The signed first component converts to physical scalar frequencies in both factors. -/
theorem sobolevSesquilinearPairing_physical (s : ℝ)
    (a : WeightedCoeffPair (Weight.sobolev s) p) (b : WeightedCoeffPair (Weight.sobolev (-s)) q) :
    sobolevSesquilinearPairing s a b =
      WeightedCoeff.sobolevSesquilinearPairing s (WeightedCoeff.reflection s a.fst)
        (WeightedCoeff.reflection (-s) b.fst) +
      WeightedCoeff.sobolevSesquilinearPairing s a.snd b.snd := by
  rw [WeightedCoeff.sobolevSesquilinearPairing_reflection]
  rfl

theorem continuous_sobolevSesquilinearPairing (s : ℝ) :
    Continuous (fun ab : WeightedCoeffPair (Weight.sobolev s) p × WeightedCoeffPair (Weight.sobolev (-s)) q =>
      sobolevSesquilinearPairing s ab.1 ab.2) := by
  have haf : Continuous (fun a : WeightedCoeffPair (Weight.sobolev s) p => a.fst) := WithLp.continuous_fst _ _ _
  have has : Continuous (fun a : WeightedCoeffPair (Weight.sobolev s) p => a.snd) := WithLp.continuous_snd _ _ _
  have hbf : Continuous (fun b : WeightedCoeffPair (Weight.sobolev (-s)) q => b.fst) := WithLp.continuous_fst _ _ _
  have hbs : Continuous (fun b : WeightedCoeffPair (Weight.sobolev (-s)) q => b.snd) := WithLp.continuous_snd _ _ _
  have hf : Continuous (fun ab : WeightedCoeffPair (Weight.sobolev s) p × WeightedCoeffPair (Weight.sobolev (-s)) q =>
      (ab.1.fst,ab.2.fst)) := (haf.comp continuous_fst).prodMk (hbf.comp continuous_snd)
  have hs : Continuous (fun ab : WeightedCoeffPair (Weight.sobolev s) p × WeightedCoeffPair (Weight.sobolev (-s)) q =>
      (ab.1.snd,ab.2.snd)) := (has.comp continuous_fst).prodMk (hbs.comp continuous_snd)
  unfold sobolevSesquilinearPairing
  apply Continuous.add
  · change Continuous ((fun ab : WeightedCoeff (Weight.sobolev s) p × WeightedCoeff (Weight.sobolev (-s)) q =>
        WeightedCoeff.sobolevSesquilinearPairing s ab.1 ab.2) ∘
      (fun ab : WeightedCoeffPair (Weight.sobolev s) p × WeightedCoeffPair (Weight.sobolev (-s)) q => (ab.1.fst,ab.2.fst)))
    exact Continuous.comp (WeightedCoeff.continuous_sobolevSesquilinearPairing (p := p) (q := q) s) hf
  · change Continuous ((fun ab : WeightedCoeff (Weight.sobolev s) p × WeightedCoeff (Weight.sobolev (-s)) q =>
        WeightedCoeff.sobolevSesquilinearPairing s ab.1 ab.2) ∘
      (fun ab : WeightedCoeffPair (Weight.sobolev s) p × WeightedCoeffPair (Weight.sobolev (-s)) q => (ab.1.snd,ab.2.snd)))
    exact Continuous.comp (WeightedCoeff.continuous_sobolevSesquilinearPairing (p := p) (q := q) s) hs

/-- Hölder on the two components gives the constant-one bound in the original finite norms. -/
theorem norm_sobolevSesquilinearPairing_le_one (s : ℝ) (hp : p ≠ ⊤) (hq : q ≠ ⊤)
    (a : WeightedCoeffPair (Weight.sobolev s) p) (b : WeightedCoeffPair (Weight.sobolev (-s)) q) :
    ‖sobolevSesquilinearPairing s a b‖ ≤ ‖a‖*‖b‖ := by
  have hpp : 0 < p.toReal := ENNReal.toReal_pos
    (ne_of_gt (zero_lt_one.trans_le (show 1 ≤ p from Fact.out))) hp
  have hqq : 0 < q.toReal := ENNReal.toReal_pos
    (ne_of_gt (zero_lt_one.trans_le (show 1 ≤ q from Fact.out))) hq
  apply (norm_add_le _ _).trans
  apply (add_le_add (WeightedCoeff.norm_sobolevSesquilinearPairing_le s a.fst b.fst)
    (WeightedCoeff.norm_sobolevSesquilinearPairing_le s a.snd b.snd)).trans
  rw [WithLp.prod_norm_eq_add hpp,WithLp.prod_norm_eq_add hqq]
  have hh := Real.inner_le_Lp_mul_Lq_of_nonneg (s := Finset.univ)
    (f := fun i : Bool => if i then ‖a.fst‖ else ‖a.snd‖)
    (g := fun i : Bool => if i then ‖b.fst‖ else ‖b.snd‖)
    (ENNReal.HolderConjugate.toReal_of_ne_top hp hq)
    (fun i _ => by cases i <;> simp) (fun i _ => by cases i <;> simp)
  simpa [add_comm] using hh

theorem sobolevSesquilinearPairing_smul_right (s : ℝ) (c : ℂ)
    (a : WeightedCoeffPair (Weight.sobolev s) p) (b : WeightedCoeffPair (Weight.sobolev (-s)) q) :
    sobolevSesquilinearPairing s a (c • b) = star c*sobolevSesquilinearPairing s a b := by
  simp only [sobolevSesquilinearPairing,WithLp.smul_fst,WithLp.smul_snd,
    WeightedCoeff.sobolevSesquilinearPairing_smul_right,mul_add]

/-- The opposite endpoint uses the source frequencywise sum norm for its second input. -/
def sobolevSesquilinearOneInfinity (s : ℝ)
    (a : WeightedCoeffPair (Weight.sobolev s) 1) (b : WeightedCoeffPairInfty (Weight.sobolev (-s))) : ℂ :=
  WeightedCoeff.sobolevSesquilinearPairing s a.fst b.1 +
    WeightedCoeff.sobolevSesquilinearPairing s a.snd b.2

theorem sobolevSesquilinearOneInfinity_eq_tsum (s : ℝ)
    (a : WeightedCoeffPair (Weight.sobolev s) 1) (b : WeightedCoeffPairInfty (Weight.sobolev (-s))) :
    sobolevSesquilinearOneInfinity s a b = ∑' n : ℤ,
      (a.fst.val n*star (b.1.val n)+a.snd.val n*star (b.2.val n)) := by
  rw [sobolevSesquilinearOneInfinity,WeightedCoeff.sobolevSesquilinearPairing_apply,
    WeightedCoeff.sobolevSesquilinearPairing_apply,
    ← (WeightedCoeff.summable_norm_sobolevSesquilinearPairing s a.fst b.1).of_norm.tsum_add
      (WeightedCoeff.summable_norm_sobolevSesquilinearPairing s a.snd b.2).of_norm]

theorem sobolevSesquilinearOneInfinity_summable (s : ℝ)
    (a : WeightedCoeffPair (Weight.sobolev s) 1) (b : WeightedCoeffPairInfty (Weight.sobolev (-s))) :
    Summable (fun n : ℤ => ‖a.fst.val n*star (b.1.val n)+a.snd.val n*star (b.2.val n)‖) :=
  Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun _ => norm_add_le _ _)
    ((WeightedCoeff.summable_norm_sobolevSesquilinearPairing s a.fst b.1).add
      (WeightedCoeff.summable_norm_sobolevSesquilinearPairing s a.snd b.2))

theorem norm_sobolevSesquilinearOneInfinity_le (s : ℝ)
    (a : WeightedCoeffPair (Weight.sobolev s) 1) (b : WeightedCoeffPairInfty (Weight.sobolev (-s))) :
    ‖sobolevSesquilinearOneInfinity s a b‖ ≤ ‖a‖*‖b‖ := by
  have h1 : ‖b.1‖ ≤ ‖b‖ := (norm_fst_le (WeightedCoeffPairInfty.toMax _ b)).trans
    (WeightedCoeffPairInfty.norm_toMax_le _ b)
  have h2 : ‖b.2‖ ≤ ‖b‖ := (norm_snd_le (WeightedCoeffPairInfty.toMax _ b)).trans
    (WeightedCoeffPairInfty.norm_toMax_le _ b)
  apply (norm_add_le _ _).trans
  calc
    _ ≤ ‖a.fst‖*‖b.1‖+‖a.snd‖*‖b.2‖ := add_le_add
      (WeightedCoeff.norm_sobolevSesquilinearPairing_le s _ _)
      (WeightedCoeff.norm_sobolevSesquilinearPairing_le s _ _)
    _ ≤ ‖a.fst‖*‖b‖+‖a.snd‖*‖b‖ := by gcongr
    _ = ‖a‖*‖b‖ := by
      rw [← add_mul]
      congr 1
      symm
      simpa only [ENNReal.toReal_one,div_self (one_ne_zero : (1 : ℝ) ≠ 0),Real.rpow_one] using
        WithLp.prod_norm_eq_add (by norm_num : 0 < (1 : ℝ≥0∞).toReal) a

end WeightedCoeffPair
namespace WeightedCoeffPairInfty

/-- Pairing of an original infinity-norm pair with an original l1 pair. -/
def sobolevSesquilinearPairing (s : ℝ)
    (a : WeightedCoeffPairInfty (Weight.sobolev s)) (b : WeightedCoeffPair (Weight.sobolev (-s)) 1) : ℂ :=
  WeightedCoeff.sobolevSesquilinearPairing s a.1 b.fst +
    WeightedCoeff.sobolevSesquilinearPairing s a.2 b.snd

theorem sobolevSesquilinearPairing_eq_tsum (s : ℝ)
    (a : WeightedCoeffPairInfty (Weight.sobolev s)) (b : WeightedCoeffPair (Weight.sobolev (-s)) 1) :
    sobolevSesquilinearPairing s a b = ∑' n : ℤ,
      (a.1.val n*star (b.fst.val n)+a.2.val n*star (b.snd.val n)) := by
  rw [sobolevSesquilinearPairing,WeightedCoeff.sobolevSesquilinearPairing_apply,
    WeightedCoeff.sobolevSesquilinearPairing_apply,
    ← (WeightedCoeff.summable_norm_sobolevSesquilinearPairing s a.1 b.fst).of_norm.tsum_add
      (WeightedCoeff.summable_norm_sobolevSesquilinearPairing s a.2 b.snd).of_norm]

theorem sobolevSesquilinearPairing_summable (s : ℝ)
    (a : WeightedCoeffPairInfty (Weight.sobolev s)) (b : WeightedCoeffPair (Weight.sobolev (-s)) 1) :
    Summable (fun n : ℤ => ‖a.1.val n*star (b.fst.val n)+a.2.val n*star (b.snd.val n)‖) :=
  Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun _ => norm_add_le _ _)
    ((WeightedCoeff.summable_norm_sobolevSesquilinearPairing s a.1 b.fst).add
      (WeightedCoeff.summable_norm_sobolevSesquilinearPairing s a.2 b.snd))

/-- The exact endpoint norms give the constant-one bound. -/
theorem norm_sobolevSesquilinearPairing_le (s : ℝ)
    (a : WeightedCoeffPairInfty (Weight.sobolev s)) (b : WeightedCoeffPair (Weight.sobolev (-s)) 1) :
    ‖sobolevSesquilinearPairing s a b‖ ≤ ‖a‖*‖b‖ := by
  have h1 : ‖a.1‖ ≤ ‖a‖ := (norm_fst_le (toMax _ a)).trans (norm_toMax_le _ a)
  have h2 : ‖a.2‖ ≤ ‖a‖ := (norm_snd_le (toMax _ a)).trans (norm_toMax_le _ a)
  apply (norm_add_le _ _).trans
  calc
    _ ≤ ‖a.1‖*‖b.fst‖+‖a.2‖*‖b.snd‖ := add_le_add
      (WeightedCoeff.norm_sobolevSesquilinearPairing_le s _ _)
      (WeightedCoeff.norm_sobolevSesquilinearPairing_le s _ _)
    _ ≤ ‖a‖*‖b.fst‖+‖a‖*‖b.snd‖ := by gcongr
    _ = ‖a‖*‖b‖ := by rw [← mul_add]; congr 1; symm; simpa only [ENNReal.toReal_one,div_self (one_ne_zero : (1 : ℝ) ≠ 0),Real.rpow_one] using WithLp.prod_norm_eq_add (by norm_num : 0 < (1 : ℝ≥0∞).toReal) b

/-- Auxiliary continuous change of norm, used only to transfer continuity. -/
private def auxiliaryPairCLM (w : Weight) : WeightedCoeffPairInfty w →L[ℂ] WeightedCoeffPair w ⊤ :=
  (WeightedCoeffPair.toMax w ⊤).symm.toContinuousLinearMap.comp (toMax w).toContinuousLinearMap

theorem continuous_sobolevSesquilinearPairing (s : ℝ) :
    Continuous (fun ab : WeightedCoeffPairInfty (Weight.sobolev s) × WeightedCoeffPair (Weight.sobolev (-s)) 1 =>
      sobolevSesquilinearPairing s ab.1 ab.2) := by
  have hc : Continuous (fun ab : WeightedCoeffPairInfty (Weight.sobolev s) × WeightedCoeffPair (Weight.sobolev (-s)) 1 =>
      (auxiliaryPairCLM _ ab.1,ab.2)) :=
    ((auxiliaryPairCLM _).continuous.comp continuous_fst).prodMk continuous_snd
  change Continuous ((fun ab : WeightedCoeffPair (Weight.sobolev s) ⊤ × WeightedCoeffPair (Weight.sobolev (-s)) 1 =>
    WeightedCoeffPair.sobolevSesquilinearPairing s ab.1 ab.2) ∘
    (fun ab : WeightedCoeffPairInfty (Weight.sobolev s) × WeightedCoeffPair (Weight.sobolev (-s)) 1 =>
      (auxiliaryPairCLM _ ab.1,ab.2)))
  exact (WeightedCoeffPair.continuous_sobolevSesquilinearPairing (p := ⊤) (q := 1) s).comp hc

theorem sobolevSesquilinearPairing_physical (s : ℝ)
    (a : WeightedCoeffPairInfty (Weight.sobolev s)) (b : WeightedCoeffPair (Weight.sobolev (-s)) 1) :
    sobolevSesquilinearPairing s a b =
      WeightedCoeff.sobolevSesquilinearPairing s (WeightedCoeff.reflection s a.1)
        (WeightedCoeff.reflection (-s) b.fst) + WeightedCoeff.sobolevSesquilinearPairing s a.2 b.snd := by
  rw [WeightedCoeff.sobolevSesquilinearPairing_reflection]
  rfl

end WeightedCoeffPairInfty
namespace WeightedCoeffPair

theorem continuous_sobolevSesquilinearOneInfinity (s : ℝ) :
    Continuous (fun ab : WeightedCoeffPair (Weight.sobolev s) 1 × WeightedCoeffPairInfty (Weight.sobolev (-s)) =>
      sobolevSesquilinearOneInfinity s ab.1 ab.2) := by
  have hc : Continuous (fun ab : WeightedCoeffPair (Weight.sobolev s) 1 × WeightedCoeffPairInfty (Weight.sobolev (-s)) =>
      (ab.1,WeightedCoeffPairInfty.auxiliaryPairCLM _ ab.2)) :=
    continuous_fst.prodMk ((WeightedCoeffPairInfty.auxiliaryPairCLM _).continuous.comp continuous_snd)
  change Continuous ((fun ab : WeightedCoeffPair (Weight.sobolev s) 1 × WeightedCoeffPair (Weight.sobolev (-s)) ⊤ =>
    sobolevSesquilinearPairing s ab.1 ab.2) ∘
    (fun ab : WeightedCoeffPair (Weight.sobolev s) 1 × WeightedCoeffPairInfty (Weight.sobolev (-s)) =>
      (ab.1,WeightedCoeffPairInfty.auxiliaryPairCLM _ ab.2)))
  exact (continuous_sobolevSesquilinearPairing (p := 1) (q := ⊤) s).comp hc

theorem sobolevSesquilinearOneInfinity_physical (s : ℝ)
    (a : WeightedCoeffPair (Weight.sobolev s) 1) (b : WeightedCoeffPairInfty (Weight.sobolev (-s))) :
    sobolevSesquilinearOneInfinity s a b =
      WeightedCoeff.sobolevSesquilinearPairing s (WeightedCoeff.reflection s a.fst)
        (WeightedCoeff.reflection (-s) b.1) + WeightedCoeff.sobolevSesquilinearPairing s a.snd b.2 := by
  rw [WeightedCoeff.sobolevSesquilinearPairing_reflection]
  rfl

end WeightedCoeffPair
end NLS
