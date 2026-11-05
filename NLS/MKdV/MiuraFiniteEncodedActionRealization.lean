import NLS.MKdV.MiuraExponentialActionEncoding
import NLS.MKdV.MiuraSobolevActionRealization

/-! # Finite nonnegative encoded data have actual H1 representatives

The positive entries decode to finite physical action data with weight
three. The central logarithm is real on the nonnegative real axis.
-/
noncomputable section
open Set Complex NLS.ZakharovShabat
open scoped ENNReal ComplexConjugate
namespace NLS.MKdV

theorem miuraSobolevActionSequence_L2_coefficients (s : ℕ) (a : MiuraRealSobolevSource s) (n : ℤ) :
    (miuraSobolevActionSequence s a.val).val n =
      (miuraL2ActionSequence (miuraPhysicalSobolevL2SourceInclusion s a).val).val n := by
  let u := miuraPhysicalSobolevL2SourceInclusion s a
  have hn := congrArg (fun J : WeightedCoeff (miuraSpectralActionWeight s) 1 => J.val n)
    (miuraSobolevCartesianActions_sequence_eq s a.val a.property).symm
  change (miuraSobolevActionSequence s a.val).val n =
    (miuraSobolevCartesianActions s (miuraSobolevCartesianSequence s a.val)).val n at hn
  rw [miuraSobolevCartesianActions_apply] at hn
  have hl := congrArg (fun J : WeightedCoeff (Weight.sobolev 1) 1 => J.val n)
    (miuraL2CartesianActions_sequence_eq u.val u.property).symm
  change (miuraL2ActionSequence u.val).val n =
    (miuraL2CartesianActions (miuraL2CartesianSequence u.val)).val n at hl
  rw [miuraL2CartesianActions_apply] at hl
  have hraw := miuraSobolevCartesianSequence_L2_coefficients s a.val a.property n
  change ((miuraSobolevCartesianSequence s a.val).1.val n,(miuraSobolevCartesianSequence s a.val).2.val n) =
    ((miuraL2CartesianSequence u.val).1.val n,(miuraL2CartesianSequence u.val).2.val n) at hraw
  have hx := congrArg Prod.fst hraw
  have hy := congrArg Prod.snd hraw
  change (miuraSobolevCartesianSequence s a.val).1.val n = (miuraL2CartesianSequence u.val).1.val n at hx
  change (miuraSobolevCartesianSequence s a.val).2.val n = (miuraL2CartesianSequence u.val).2.val n at hy
  rw [hn,hl,hx,hy]

/-- Every finite nonnegative encoded action sequence decodes to the
physical action/mean data of a genuine original real H1 profile. -/
theorem exists_H1_profile_of_finite_encoded_actions (q : Coeff 1)
    (hq : Coeff.HasFiniteSupport q) (hpos : q ∈ Coeff.nonnegativeLocus 1) :
    ∃ a : MiuraRealSobolevSource 1,
      miuraRealL2ActionMeanMap (miuraPhysicalSobolevL2SourceInclusion 1 a) = miuraLogActionParameters q := by
  classical
  obtain ⟨S,hS⟩ := hq
  let v : ℤ →₀ ℂ := Finsupp.onFinset S (fun n => (miuraLogActionParameters q).1.val n) (by
    intro n hn
    by_contra hns
    apply hn
    simp only [miuraLogActionParameters_apply,hS n hns,zero_div,ite_self])
  let J := WeightedCoeff.ofFinsupp (miuraSpectralActionWeight 1) 1 v
  have hJ (n : ℤ) : J.val n = (miuraLogActionParameters q).1.val n := rfl
  have hJpos (n : ℤ) : (J.val n).im = 0 ∧ 0 ≤ (J.val n).re := by
    rw [hJ,miuraLogActionParameters_apply]
    by_cases hn : 0 < n
    · rw [if_pos hn]
      have he : q n = ((q n).re : ℂ) := by apply Complex.ext <;> simp [(hpos n).1]
      rw [he,← Complex.ofReal_div]
      exact ⟨rfl,div_nonneg (hpos n).2 ((Weight.sobolev 1).positive n).le⟩
    · simp only [if_neg hn,Complex.zero_im,Complex.zero_re,le_refl,and_self]
  have hJzero (n : ℤ) (hn : ¬0 < n) : J.val n = 0 := by
    rw [hJ,miuraLogActionParameters_apply,if_neg hn]
  have hlog : Complex.log (q 0) = (Real.log (q 0).re : ℂ) := by
    have he : q 0 = ((q 0).re : ℂ) := by apply Complex.ext <;> simp [(hpos 0).1]
    rw [he]
    exact (Complex.ofReal_log (hpos 0).2).symm
  obtain ⟨a,hact,hmean⟩ := exists_miuraSobolev_profile_of_nonnegative_actions 1 le_rfl J hJpos hJzero (Real.log (q 0).re)
  refine ⟨a,?_⟩
  apply Prod.ext
  · apply Subtype.ext
    funext n
    change (miuraL2ActionSequence (miuraPhysicalSobolevL2SourceInclusion 1 a).val).val n = _
    rw [← miuraSobolevActionSequence_L2_coefficients 1 a n,hact,hJ]
  · change (miuraPhysicalSobolevL2SourceInclusion 1 a).val 0 = Complex.log (q 0)
    rw [miuraPhysicalSobolevL2SourceInclusion_apply,hmean,hlog]

end NLS.MKdV
