import NLS.Poisson.SobolevCommonBracket
import NLS.Poisson.SourceBracketJacobi

/-! # Compatibility of signed Sobolev and physical source coordinates

At order zero, reflecting the first signed component gives the physical
coefficient coordinates used by `sourceBracket`. The comparison below
uses full differentials, rather than merely identifying formal gradients.
-/
noncomputable section
open scoped ENNReal
namespace NLS.Poisson

/-- Order-zero signed coefficients in the physical scalar Fourier convention. -/
def zeroOrderPhysicalEquiv (s : ℝ) (_hs : s = 0) (p : ℝ≥0∞) [Fact (1 ≤ p)] :
    WeightedCoeffPair (Weight.sobolev s) p ≃L[ℂ] CoeffPair p :=
  (WeightedCoeffPair.toMax _ p).trans
    ((((WeightedCoeff.weightIsometry (Weight.sobolev s) p).toContinuousLinearEquiv.trans
      Coeff.reflection.toContinuousLinearEquiv).prodCongr
      (WeightedCoeff.weightIsometry (Weight.sobolev s) p).toContinuousLinearEquiv).trans
      (CoeffPair.toMax p).symm)

@[simp] theorem zeroOrderPhysicalEquiv_fst {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (s : ℝ) (hs : s = 0) (a : WeightedCoeffPair (Weight.sobolev s) p) (n : ℤ) :
    (zeroOrderPhysicalEquiv s hs p a).fst n = a.fst.val (-n) := by
  change (Weight.sobolev s (-n) : ℂ)*a.fst.val (-n) = _
  simp [hs]

@[simp] theorem zeroOrderPhysicalEquiv_snd {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (s : ℝ) (hs : s = 0) (a : WeightedCoeffPair (Weight.sobolev s) p) (n : ℤ) :
    (zeroOrderPhysicalEquiv s hs p a).snd n = a.snd.val n := by
  change (Weight.sobolev s n : ℂ)*a.snd.val n = _
  simp [hs]

@[simp] theorem zeroOrderPhysicalEquiv_inl_mode {p : ℝ≥0∞} [Fact (1 ≤ p)] (s : ℝ) (hs : s = 0) (n : ℤ) :
    zeroOrderPhysicalEquiv s hs p (WeightedCoeffPair.inlCLM _
      (WeightedCoeff.ofFinsupp (Weight.sobolev s) p (Finsupp.single n 1))) =
      CoeffPair.inlCLM (lp.single p (-n) 1) := by
  apply (CoeffPair.toMax p).injective
  apply Prod.ext <;> ext k <;>
    simp [WeightedCoeff.ofFinsupp_apply,Finsupp.single_apply,lp.single_apply,Pi.single_apply]
  split_ifs <;> first | rfl | omega

@[simp] theorem zeroOrderPhysicalEquiv_inr_mode {p : ℝ≥0∞} [Fact (1 ≤ p)] (s : ℝ) (hs : s = 0) (n : ℤ) :
    zeroOrderPhysicalEquiv s hs p (WeightedCoeffPair.inrCLM _
      (WeightedCoeff.ofFinsupp (Weight.sobolev s) p (Finsupp.single n 1))) =
      CoeffPair.inrCLM (lp.single p n 1) := by
  apply (CoeffPair.toMax p).injective
  apply Prod.ext <;> ext k <;>
    simp [WeightedCoeff.ofFinsupp_apply,Finsupp.single_apply,lp.single_apply,Pi.single_apply,eq_comm]

/-- The complete differential formula, in the original signed mode directions. -/
theorem conjugateBivector_eq_tsum {p q : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ q)]
    [p.HolderConjugate q] (s : ℝ) (hp : p ≠ ⊤) (hq : q ≠ ⊤)
    (L : WeightedCoeffPair (Weight.sobolev (-s)) q →L[ℂ] ℂ)
    (M : WeightedCoeffPair (Weight.sobolev s) p →L[ℂ] ℂ) :
    conjugateBivector s hp hq L M = -Complex.I * ∑' n : ℤ,
      (L (WeightedCoeffPair.inlCLM _ (WeightedCoeff.ofFinsupp _ q (Finsupp.single (-n) 1))) *
        M (WeightedCoeffPair.inrCLM _ (WeightedCoeff.ofFinsupp _ p (Finsupp.single (-n) 1))) -
       L (WeightedCoeffPair.inrCLM _ (WeightedCoeff.ofFinsupp _ q (Finsupp.single (-n) 1))) *
        M (WeightedCoeffPair.inlCLM _ (WeightedCoeff.ofFinsupp _ p (Finsupp.single (-n) 1)))) := by
  change signedBivector s
    (negNegComponents s (WeightedCoeffPair.sobolevCotangentComponentsCLM (-s) hq L))
    (WeightedCoeffPair.sobolevCotangentComponentsCLM s hp M) = _
  rw [signedBivector_eq_tsum]
  simp only [negNegComponents_fst_val,negNegComponents_snd_val,
    WeightedCoeffPair.sobolevCotangentComponentsCLM_fst,
    WeightedCoeffPair.sobolevCotangentComponentsCLM_snd,
    WeightedCoeff.sobolevCotangent_val,ContinuousLinearMap.comp_apply]

/-- Full cotangent pairing agrees with the established physical Hilbert bivector. -/
theorem conjugateBivector_zero_source (L M : CoeffPair 2 →L[ℂ] ℂ) :
    conjugateBivector (p := 2) (q := 2) 0 (by norm_num) (by norm_num)
      (L.comp (zeroOrderPhysicalEquiv (-0) neg_zero 2).toContinuousLinearMap)
      (M.comp (zeroOrderPhysicalEquiv 0 rfl 2).toContinuousLinearMap) =
      sourceBivector (p := 2) le_rfl L M := by
  rw [conjugateBivector_eq_tsum]
  simp only [ContinuousLinearMap.comp_apply,ContinuousLinearEquiv.coe_coe,
    zeroOrderPhysicalEquiv_inl_mode,zeroOrderPhysicalEquiv_inr_mode,neg_neg]
  change _ = hilbertPairBivector (CoeffPair.cotangentCoefficients le_rfl L)
    (CoeffPair.cotangentCoefficients le_rfl M)
  rw [hilbertPairBivector_apply,reflectedHilbertPairing_apply,reflectedHilbertPairing_apply]
  have h1 := (summable_norm_reflectedHilbertPairing
    (CoeffPair.cotangentCoefficients le_rfl L).1 (CoeffPair.cotangentCoefficients le_rfl M).2).of_norm
  have h2 := (summable_norm_reflectedHilbertPairing
    (CoeffPair.cotangentCoefficients le_rfl L).2 (CoeffPair.cotangentCoefficients le_rfl M).1).of_norm
  simp only [CoeffPair.cotangentCoefficients_fst,CoeffPair.cotangentCoefficients_snd] at h1 h2 ⊢
  have h2' : Summable (fun n : ℤ => L (CoeffPair.inrCLM (lp.single 2 (-n) 1))*
      M (CoeffPair.inlCLM (lp.single 2 n 1))) := by
    have h := (Equiv.neg ℤ).summable_iff.mpr h2
    change Summable (fun n : ℤ => L (CoeffPair.inrCLM (lp.single 2 (-n) 1))*
      M (CoeffPair.inlCLM (lp.single 2 (-(-n)) 1))) at h
    simpa only [neg_neg] using h
  rw [Summable.tsum_sub h1 h2']
  congr 2
  simpa only [Equiv.neg_apply,neg_neg] using (Equiv.neg ℤ).tsum_eq (fun n => L (CoeffPair.inrCLM (lp.single 2 n 1))*M (CoeffPair.inlCLM (lp.single 2 (-n) 1)))

/-- Coefficient-preserving inclusion after the signed-to-physical conversion. -/
def zeroOrderSourceMap {p r : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ r)]
    (s : ℝ) (hs : s = 0) (hpr : p ≤ r) :
    WeightedCoeffPair (Weight.sobolev s) p →L[ℂ] CoeffPair r :=
  (CoeffPair.exponentInclusion hpr).comp (zeroOrderPhysicalEquiv s hs p).toContinuousLinearMap

@[simp] theorem zeroOrderSourceMap_inl_mode {p r : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ r)]
    (s : ℝ) (hs : s = 0) (hpr : p ≤ r) (n : ℤ) :
    zeroOrderSourceMap s hs hpr (WeightedCoeffPair.inlCLM _
      (WeightedCoeff.ofFinsupp _ p (Finsupp.single n 1))) =
      CoeffPair.inlCLM (lp.single r (-n) 1) := by
  rw [zeroOrderSourceMap,ContinuousLinearMap.comp_apply,ContinuousLinearEquiv.coe_coe,
    zeroOrderPhysicalEquiv_inl_mode]
  rfl

@[simp] theorem zeroOrderSourceMap_inr_mode {p r : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ r)]
    (s : ℝ) (hs : s = 0) (hpr : p ≤ r) (n : ℤ) :
    zeroOrderSourceMap s hs hpr (WeightedCoeffPair.inrCLM _
      (WeightedCoeff.ofFinsupp _ p (Finsupp.single n 1))) =
      CoeffPair.inrCLM (lp.single r n 1) := by
  rw [zeroOrderSourceMap,ContinuousLinearMap.comp_apply,ContinuousLinearEquiv.coe_coe,
    zeroOrderPhysicalEquiv_inr_mode]
  rfl

/-- Agreement on every finite conjugate overlap with the established source bivector. -/
theorem conjugateBivector_zero_source_restrict {p q r : ℝ≥0∞}
    [Fact (1 ≤ p)] [Fact (1 ≤ q)] [Fact (1 ≤ r)] [p.HolderConjugate q]
    (hp : p ≠ ⊤) (hq : q ≠ ⊤) (h2r : 2 ≤ r) (hpr : p ≤ r) (hqr : q ≤ r)
    (L M : CoeffPair r →L[ℂ] ℂ) :
    conjugateBivector 0 hp hq (L.comp (zeroOrderSourceMap (-0) neg_zero hqr))
      (M.comp (zeroOrderSourceMap 0 rfl hpr)) = sourceBivector h2r L M := by
  rw [conjugateBivector_eq_tsum]
  simp only [ContinuousLinearMap.comp_apply,zeroOrderSourceMap_inl_mode,
    zeroOrderSourceMap_inr_mode,neg_neg]
  change _ = hilbertPairBivector (CoeffPair.cotangentCoefficients h2r L)
    (CoeffPair.cotangentCoefficients h2r M)
  rw [hilbertPairBivector_apply,reflectedHilbertPairing_apply,reflectedHilbertPairing_apply]
  have h1 := (summable_norm_reflectedHilbertPairing
    (CoeffPair.cotangentCoefficients h2r L).1 (CoeffPair.cotangentCoefficients h2r M).2).of_norm
  have h2 := (summable_norm_reflectedHilbertPairing
    (CoeffPair.cotangentCoefficients h2r L).2 (CoeffPair.cotangentCoefficients h2r M).1).of_norm
  simp only [CoeffPair.cotangentCoefficients_fst,CoeffPair.cotangentCoefficients_snd] at h1 h2 ⊢
  have h2' : Summable (fun n : ℤ => L (CoeffPair.inrCLM (lp.single r (-n) 1))*
      M (CoeffPair.inlCLM (lp.single r n 1))) := by
    have h := (Equiv.neg ℤ).summable_iff.mpr h2
    change Summable (fun n : ℤ => L (CoeffPair.inrCLM (lp.single r (-n) 1))*
      M (CoeffPair.inlCLM (lp.single r (-(-n)) 1))) at h
    simpa only [neg_neg] using h
  rw [Summable.tsum_sub h1 h2']
  congr 2
  simpa only [Equiv.neg_apply,neg_neg] using (Equiv.neg ℤ).tsum_eq
    (fun n => L (CoeffPair.inrCLM (lp.single r n 1))*M (CoeffPair.inlCLM (lp.single r (-n) 1)))

/-- The two inclusions of a common state are the same original physical state. -/
theorem zeroOrderSourceMap_common {p q r : ℝ≥0∞}
    [Fact (1 ≤ p)] [Fact (1 ≤ q)] [Fact (1 ≤ r)]
    (hpr : p ≤ r) (hqr : q ≤ r) (x : SobolevCommonState 0 p q) :
    zeroOrderSourceMap (-0) neg_zero hqr x.val.1 = zeroOrderSourceMap 0 rfl hpr x.val.2 := by
  apply (CoeffPair.toMax r).injective
  apply Prod.ext <;> ext n
  · change (zeroOrderPhysicalEquiv (-0) neg_zero q x.val.1).fst n =
      (zeroOrderPhysicalEquiv 0 rfl p x.val.2).fst n
    simp only [zeroOrderPhysicalEquiv_fst]
    exact (commonState_coefficients 0 x (-n)).1
  · change (zeroOrderPhysicalEquiv (-0) neg_zero q x.val.1).snd n =
      (zeroOrderPhysicalEquiv 0 rfl p x.val.2).snd n
    simp only [zeroOrderPhysicalEquiv_snd]
    exact (commonState_coefficients 0 x n).2

/-- Actual function brackets agree at every common physical base point in the overlap. -/
theorem commonSobolevBracket_zero_source {p q r : ℝ≥0∞}
    [Fact (1 ≤ p)] [Fact (1 ≤ q)] [Fact (1 ≤ r)] [p.HolderConjugate q]
    (hp : p ≠ ⊤) (hq : q ≠ ⊤) (h2r : 2 ≤ r) (hpr : p ≤ r) (hqr : q ≤ r)
    (F G : CoeffPair r → ℂ) (x : SobolevCommonState 0 p q)
    (hF : DifferentiableAt ℂ F (zeroOrderSourceMap 0 rfl hpr x.val.2))
    (hG : DifferentiableAt ℂ G (zeroOrderSourceMap 0 rfl hpr x.val.2)) :
    commonSobolevBracket 0 hp hq (F ∘ zeroOrderSourceMap (-0) neg_zero hqr)
      (G ∘ zeroOrderSourceMap 0 rfl hpr) x =
      sourceBracket h2r F G (zeroOrderSourceMap 0 rfl hpr x.val.2) := by
  have hx := zeroOrderSourceMap_common hpr hqr x
  have hF' : DifferentiableAt ℂ F (zeroOrderSourceMap (-0) neg_zero hqr x.val.1) := hx.symm ▸ hF
  rw [commonSobolevBracket,fderiv_comp _ hF' (zeroOrderSourceMap (-0) neg_zero hqr).differentiableAt,
    fderiv_comp _ hG (zeroOrderSourceMap 0 rfl hpr).differentiableAt,
    ContinuousLinearMap.fderiv,ContinuousLinearMap.fderiv,hx]
  exact conjugateBivector_zero_source_restrict hp hq h2r hpr hqr _ _

end NLS.Poisson
