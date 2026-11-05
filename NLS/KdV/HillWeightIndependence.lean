import NLS.KdV.HillL2EnergyDiscriminant

/-! # Independence of the Hill reduction from the auxiliary sequence weight

The literal coefficient inclusion commutes with convolution and the
complementary inverse. Uniqueness of the actual Neumann solution therefore
identifies the weighted and unit-weight finite operators and determinants.
Thus the weighted roots are the actual rough physical Hill characteristic
roots, rather than roots of a separately assumed spectral package.
-/

noncomputable section
open scoped ENNReal
namespace NLS.KdV

/-- Forget the auxiliary weight while retaining every raw coefficient. -/
def hillForgetWeight (w : SpectralWeight) (p : ℝ≥0∞) [Fact (1 ≤ p)] :
    WeightedCoeff w.toWeight p →L[ℂ] WeightedCoeff SpectralWeight.one.toWeight p :=
  WeightedCoeff.inclusionCLM _ _ (fun k => w.one_le k)

@[simp] theorem hillForgetWeight_apply (w : SpectralWeight) (p : ℝ≥0∞) [Fact (1 ≤ p)]
    (a : WeightedCoeff w.toWeight p) (k : ℤ) : (hillForgetWeight w p a).val k = a.val k :=
  WeightedCoeff.inclusionCLM_apply _ _ _ a k

theorem norm_hillForgetWeight_le (w : SpectralWeight) (p : ℝ≥0∞) [Fact (1 ≤ p)]
    (a : WeightedCoeff w.toWeight p) : ‖hillForgetWeight w p a‖ ≤ ‖a‖ :=
  WeightedCoeff.norm_inclusionCLM_le _ _ _ a

theorem toCoeff_hillForgetWeight (w : SpectralWeight) (p : ℝ≥0∞) [Fact (1 ≤ p)]
    (a : WeightedCoeff w.toWeight p) :
    SpectralWeight.one.toCoeff (hillForgetWeight w p a) = w.toCoeff a := by
  ext k
  simp only [SpectralWeight.toCoeff_apply, hillForgetWeight_apply]

theorem hillForgetWeight_convolution (w : SpectralWeight)
    (q : WeightedCoeff w.toWeight 2) (a : WeightedCoeff w.toWeight 1) :
    hillForgetWeight w 2 (w.convolution q a) =
      SpectralWeight.one.convolution (hillForgetWeight w 2 q) (hillForgetWeight w 1 a) := by
  apply Subtype.ext
  funext k
  simp only [hillForgetWeight_apply, SpectralWeight.convolution_apply]

theorem hillForgetWeight_complement (w : SpectralWeight) (n : ℕ) (hn : 1 ≤ n)
    (z : ℂ) (hz : z ∈ reducedHillStrip n) (a : WeightedCoeff w.toWeight 2) :
    hillForgetWeight w 1 (hillComplementToL1 w.toWeight n hn z hz a) =
      hillComplementToL1 SpectralWeight.one.toWeight n hn z hz (hillForgetWeight w 2 a) := by
  apply Subtype.ext
  funext k
  simp only [hillForgetWeight_apply, hillComplementToL1_apply]

theorem hillForgetWeight_tail (w : SpectralWeight) (q : WeightedCoeff w.toWeight 2)
    (n : ℕ) (hn : 1 ≤ n) (z : ℂ) (hz : z ∈ reducedHillStrip n) (a : WeightedCoeff w.toWeight 2) :
    hillForgetWeight w 2 (hillTailPerturbation w q n hn z hz a) =
      hillTailPerturbation SpectralWeight.one (hillForgetWeight w 2 q) n hn z hz (hillForgetWeight w 2 a) := by
  change hillForgetWeight w 2 (w.convolution q (hillComplementToL1 w.toWeight n hn z hz a)) =
    SpectralWeight.one.convolution (hillForgetWeight w 2 q)
      (hillComplementToL1 SpectralWeight.one.toWeight n hn z hz (hillForgetWeight w 2 a))
  rw [hillForgetWeight_convolution, hillForgetWeight_complement]

/-- Uniqueness identifies the actual inverse solutions in the two spaces. -/
theorem hillForgetWeight_tailInverse (w : SpectralWeight) (q : WeightedCoeff w.toWeight 2)
    (n : ℕ) (hn : 1 ≤ n) (z : ℂ) (hz : z ∈ reducedHillStrip n)
    (hcut : 8*‖q‖ ≤ (n : ℝ)) (hcut1 : 8*‖hillForgetWeight w 2 q‖ ≤ (n : ℝ))
    (a : WeightedCoeff w.toWeight 2) :
    hillForgetWeight w 2 (hillTailInverse w q n hn z hz hcut a) =
      hillTailInverse SpectralWeight.one (hillForgetWeight w 2 q) n hn z hz hcut1 (hillForgetWeight w 2 a) := by
  apply hillTailInverse_unique
  rw [← hillForgetWeight_tail, ← map_sub, hillTailInverse_right]

theorem hillForgetWeight_modes (w : SpectralWeight) (n : ℕ) (u : ℂ × ℂ) :
    hillForgetWeight w 1 (hillModes w.toWeight n u) = hillModes SpectralWeight.one.toWeight n u := by
  apply Subtype.ext
  funext k
  simp only [hillForgetWeight_apply, hillModes_apply]

theorem hillForgetWeight_modePotential (w : SpectralWeight) (q : WeightedCoeff w.toWeight 2)
    (n : ℕ) (u : ℂ × ℂ) :
    hillForgetWeight w 2 (hillModePotential w q n u) =
      hillModePotential SpectralWeight.one (hillForgetWeight w 2 q) n u := by
  change hillForgetWeight w 2 (w.convolution q (hillModes w.toWeight n u)) =
    SpectralWeight.one.convolution (hillForgetWeight w 2 q) (hillModes SpectralWeight.one.toWeight n u)
  rw [hillForgetWeight_convolution, hillForgetWeight_modes]

theorem hillForgetWeight_effectivePotential (w : SpectralWeight) (q : WeightedCoeff w.toWeight 2)
    (n : ℕ) (hn : 1 ≤ n) (z : ℂ) (hz : z ∈ reducedHillStrip n)
    (hcut : 8*‖q‖ ≤ (n : ℝ)) (hcut1 : 8*‖hillForgetWeight w 2 q‖ ≤ (n : ℝ)) (u : ℂ × ℂ) :
    hillForgetWeight w 2 (hillEffectivePotential w q n hn z hz hcut u) =
      hillEffectivePotential SpectralWeight.one (hillForgetWeight w 2 q) n hn z hz hcut1 u := by
  change hillForgetWeight w 2 (hillTailInverse w q n hn z hz hcut (hillModePotential w q n u)) =
    hillTailInverse SpectralWeight.one (hillForgetWeight w 2 q) n hn z hz hcut1
      (hillModePotential SpectralWeight.one (hillForgetWeight w 2 q) n u)
  rw [hillForgetWeight_tailInverse w q n hn z hz hcut hcut1, hillForgetWeight_modePotential]

/-- The finite operator is independent of the auxiliary spectral weight. -/
theorem hillReducedOperator_weight_independent (w : SpectralWeight) (q : WeightedCoeff w.toWeight 2)
    (n : ℕ) (hn : 1 ≤ n) (z : ℂ) (hz : z ∈ reducedHillStrip n)
    (hcut : 8*‖q‖ ≤ (n : ℝ)) (hcut1 : 8*‖hillForgetWeight w 2 q‖ ≤ (n : ℝ)) :
    hillReducedOperator w q n hn z hz hcut =
      hillReducedOperator SpectralWeight.one (hillForgetWeight w 2 q) n hn z hz hcut1 := by
  apply ContinuousLinearMap.ext
  intro u
  have he := hillForgetWeight_effectivePotential w q n hn z hz hcut hcut1 u
  have hc := congrArg (fun a : WeightedCoeff SpectralWeight.one.toWeight 2 => (a.val n,a.val (-(n : ℤ)))) he
  simp only [hillForgetWeight_apply] at hc
  change (z-(freeHillValue n : ℂ)) • u-
      ((hillEffectivePotential w q n hn z hz hcut u).val n,
        (hillEffectivePotential w q n hn z hz hcut u).val (-(n : ℤ))) = _
  rw [hc]
  rfl

theorem hillReducedDeterminant_weight_independent (w : SpectralWeight) (q : WeightedCoeff w.toWeight 2)
    (n : ℕ) (hn : 1 ≤ n) (z : ℂ) (hz : z ∈ reducedHillStrip n) (hcut : 8*‖q‖ ≤ (n : ℝ)) :
    hillReducedDeterminant w n (q,z) =
      hillReducedDeterminant SpectralWeight.one n (hillForgetWeight w 2 q,z) := by
  have hc : 8*‖hillForgetWeight w 2 q‖ ≤ (n : ℝ) := by
    nlinarith [norm_hillForgetWeight_le w 2 q]
  have he := congrArg (fun T : (ℂ × ℂ) →L[ℂ] (ℂ × ℂ) => T.toLinearMap.det)
    (hillReducedOperator_weight_independent w q n hn z hz hcut hc)
  exact (hillReducedDeterminant_eq w n hn (q,z) hz hcut).trans
    (he.trans (hillReducedDeterminant_eq SpectralWeight.one n hn (hillForgetWeight w 2 q,z) hz hc).symm)

/-- Weighted roots are precisely the actual rough Hill characteristic roots. -/
theorem hillReduced_weighted_zero_iff_l2Discriminant (w : SpectralWeight)
    (q : WeightedCoeff w.toWeight 2) (hq : w.toCoeff q ∈ Coeff.paritySubspace 0)
    (n : ℕ) (hn : 1 ≤ n) (z : ℂ) (hz : z ∈ reducedHillStrip n) (hcut : 8*‖q‖ ≤ (n : ℝ)) :
    hillReducedDeterminant w n (q,z) = 0 ↔ hillL2Discriminant (w.toCoeff q) z ^ 2 = 4 := by
  have hc : 8*‖hillForgetWeight w 2 q‖ ≤ (n : ℝ) := by
    nlinarith [norm_hillForgetWeight_le w 2 q]
  have hq1 : SpectralWeight.one.toCoeff (hillForgetWeight w 2 q) ∈ Coeff.paritySubspace 0 := by
    rwa [toCoeff_hillForgetWeight]
  rw [hillReducedDeterminant_weight_independent w q n hn z hz hcut]
  simpa only [toCoeff_hillForgetWeight] using
    hillReduced_zero_iff_l2Discriminant (hillForgetWeight w 2 q) hq1 n hn z hz hc

/-- The same physical discriminant is analytic in each of the source's
weighted Banach norms, via the proved bounded raw-coefficient inclusion. -/
theorem analyticOnNhd_weighted_hillL2Discriminant_joint (w : SpectralWeight) :
    AnalyticOnNhd ℂ (fun p : ℂ × WeightedCoeff w.toWeight 2 =>
      hillL2Discriminant (w.toCoeff p.2) p.1) Set.univ := by
  intro p _
  have hq : AnalyticAt ℂ (fun r : ℂ × WeightedCoeff w.toWeight 2 => w.toCoeff r.2) p :=
    (w.toCoeff.analyticAt p.2).comp
      (f := fun r : ℂ × WeightedCoeff w.toWeight 2 => r.2) analyticAt_snd
  exact (analyticOnNhd_hillL2Discriminant_joint (p.1,w.toCoeff p.2) (Set.mem_univ _)).comp
    (f := fun r : ℂ × WeightedCoeff w.toWeight 2 => (r.1,w.toCoeff r.2))
    (analyticAt_fst.prod hq)

end NLS.KdV
