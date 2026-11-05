import NLS.MKdV.MiuraNativeActionMeanDifferential

/-! # The full native action/mean differential of an actual angle direction

The identity holds in the weighted summable action space itself, retaining
the raw selected action unit and zero signed-mean direction. Coordinate
identification avoids an unjustified exchange of an infinite derivative sum.
-/
noncomputable section
open Set Complex NLS.ZakharovShabat
open scoped ENNReal ComplexConjugate
namespace NLS.MKdV

def miuraRealSobolevLower (s : ℕ) (a : MiuraRealSobolevSource (s+1)) : MiuraRealSobolevSource s :=
  ⟨hierarchySobolevInclusion (s+1) s (by omega) a.val,by
    intro j
    simpa only [hierarchySobolevInclusion_apply] using! a.property j⟩

theorem miuraThetaNativeActionMean_differential (s : ℕ) (a : MiuraRealSobolevSource (s+1))
    (n : ℕ) (hn : 1 ≤ n)
    (hgap : canonicalPeriodicGap (by simp) (by norm_num)
      (periodOnePotential (miuraSobolevActionSource (s+1) a.val)) (periodOnePotential_mem _) n ≠ 0) :
    fderiv ℂ (miuraNativeActionMeanMap s) (miuraRealSobolevLower s a).val
      (miuraThetaNativeGardnerDirection s a n hgap) =
        -(WeightedCoeff.single (p := 1) (miuraSpectralActionWeight s) (n : ℤ) 1,0) := by
  let b := miuraRealSobolevLower s a
  let v := miuraThetaNativeGardnerDirection s a n hgap
  have hd : fderiv ℂ (miuraNativeActionMeanMap s) b.val =
      (fderiv ℂ (miuraSobolevActionSequence s) b.val).prod
        (WeightedCoeff.evalCLM (Weight.sobolev (s : ℝ)) 2 0) :=
    ((analyticAt_miuraSobolevActionSequence s b).differentiableAt.hasFDerivAt.prodMk
      (WeightedCoeff.evalCLM (Weight.sobolev (s : ℝ)) 2 0).hasFDerivAt).fderiv
  have hbase : hierarchySobolevJetL2 s 0 (Nat.zero_le _) b.val =
      hierarchySobolevJetL2 (s+1) 0 (Nat.zero_le _) a.val := by
    ext j
    simp only [b,miuraRealSobolevLower,hierarchySobolevJetL2_apply,pow_zero,one_mul,hierarchySobolevInclusion_apply]
  rw [hd]
  apply Prod.ext
  · apply Subtype.ext
    funext j
    change (fderiv ℂ (miuraSobolevActionSequence s) b.val v).val j =
      -(WeightedCoeff.single (p := 1) (miuraSpectralActionWeight s) (n : ℤ) 1).val j
    rw [WeightedCoeff.single_val]
    by_cases hj : 0 < j
    · obtain ⟨k,hk⟩ : ∃ k : ℕ, (k : ℤ) = j := ⟨j.toNat,Int.toNat_of_nonneg (by omega)⟩
      subst j
      rw [fderiv_miuraSobolevActionSequence_eval_positive s b k (by omega) v,hbase]
      have h := miuraThetaNativeGardnerDirection_L2_action s a n k hn (by omega) hgap
      simpa only [Pi.single_apply,Int.natCast_inj,eq_comm] using h
    · rw [fderiv_miuraSobolevActionSequence_eval_nonpositive s b j hj v,
        Pi.single_eq_of_ne (by omega : j ≠ (n : ℤ)),neg_zero]
  · change v.val 0 = -0
    rw [neg_zero]
    exact miuraThetaNativeGardnerDirection_mean_zero s a n hgap

end NLS.MKdV
