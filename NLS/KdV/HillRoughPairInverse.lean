import NLS.Articles.KdVKdV2Frequencies.GlobalRoughAbelianRealInverse
import NLS.Articles.KdVKdV2Frequencies.GlobalRoughAbelianRegularity
import NLS.SequenceSpaces.SignedHilbertPairs

/-! # Actual local rough inverse potentials in normalized Hilbert pair coordinates -/
noncomputable section
set_option autoImplicit false
open Set Complex Filter Topology
namespace NLS.KdV
open NLS.Articles.KdVKdV2Frequencies

/-- At every real mean-zero Hminus1 source, construct a complex analytic
local inverse potential on a pair neighborhood, with exact signed inverse
identity and reality on that neighborhood's real pair locus. -/
theorem exists_hillRough_pair_inverse
    (D : GlobalRoughAbelianForwardData) (e : ℤ ≃ ℕ+)
    (q0 : PeriodOneHminusOne) (hr : IsRealPeriodOneHminusOne q0) (hm : q0.val 0 = 0) :
    ∃ z0 : Coeff 2 × Coeff 2, z0 ∈ Coeff.realPairLocus 2 ∧
      ∃ U : Set (Coeff 2 × Coeff 2), IsOpen U ∧ z0 ∈ U ∧
      ∃ Q : (Coeff 2 × Coeff 2) → PeriodOneHminusOne,
        AnalyticOnNhd ℂ Q U ∧ Q z0 = q0 ∧ ∀ z ∈ U,
          (Q z).val 0 = 0 ∧
          D.signed (Q z) = WeightedCoeff.meanZeroWeightedLiftCLM (Weight.sobolev (-1/2))
            (signedPairToDeleted e z) ∧
          (z ∈ Coeff.realPairLocus 2 → IsRealPeriodOneHminusOne (Q z)) := by
  let L := WeightedCoeff.meanZeroWeightedLiftCLM (Weight.sobolev (-1))
  let a := WeightedCoeff.meanZeroWeightedProjectionCLM (Weight.sobolev (-1)) q0
  have hLa : L a = q0 := WeightedCoeff.meanZeroWeightedLift_projection _ q0 hm
  have hra : IsRealPeriodOneHminusOne (L a) := by rwa [hLa]
  let b := D.meanZeroForward a
  have hJa : deletedL2Conjugation a = a :=
    (WeightedCoeff.meanZeroWeightedLift_real_iff _ (Weight.sobolev_neg (-1)) a).mp hra
  have hJb : deletedL2Conjugation b = b := by
    change deletedL2Conjugation (D.meanZeroForward a) = D.meanZeroForward a
    rw [←D.meanZeroForward_conjugation,hJa]
  obtain ⟨V,hV,hbV,G,hG,hGa,hd⟩ := D.exists_real_weak_inverse_germ a hra
  let z0 := deletedToSignedPair e b
  let U := signedPairToDeleted e ⁻¹' V
  let Q : (Coeff 2 × Coeff 2) → PeriodOneHminusOne := fun z => L (G (signedPairToDeleted e z))
  refine ⟨z0,deletedToSignedPair_real e b hJb,U,hV.preimage (signedPairToDeleted e).continuous,
    ?_,Q,?_,?_,?_⟩
  · change signedPairToDeleted e (deletedToSignedPair e b) ∈ V
    rwa [signedPairToDeleted_apply_inverse]
  · intro z hz
    exact (L.analyticAt _).comp ((hG _ hz).comp ((signedPairToDeleted e).analyticAt z))
  · change L (G (signedPairToDeleted e (deletedToSignedPair e b))) = q0
    rw [signedPairToDeleted_apply_inverse]
    have hGb : G b = a := hGa
    rw [hGb,hLa]
  · intro z hz
    have hh := hd (signedPairToDeleted e z) hz
    exact ⟨WeightedCoeff.meanZeroWeightedLift_zero _ _,hh.2.2.1,
      fun hzr => hh.2.2.2 (signedPairToDeleted_real e z hzr)⟩

theorem positive_eq_signedPair_of_inverse_identity
    (D : GlobalRoughAbelianForwardData) (e : ℤ ≃ ℕ+) (q : PeriodOneHminusOne)
    (hr : IsRealPeriodOneHminusOne q) (z : Coeff 2 × Coeff 2)
    (hi : D.signed q = WeightedCoeff.meanZeroWeightedLiftCLM (Weight.sobolev (-1/2))
      (signedPairToDeleted e z)) (k : ℤ) :
    D.positive q (positiveIndexInjection e k) =
      (z.1 k-I*z.2 k)/(Real.sqrt 2 : ℂ) := by
  have hn : (0 : ℤ) < positiveIndexInjection e k := by
    dsimp only [positiveIndexInjection]; exact_mod_cast (e k).pos
  have h := congrArg (fun b : WeightedCoeff (Weight.sobolev (-1/2)) 2 =>
    b.val (positiveIndexInjection e k)) hi
  rw [D.signed_positive_real q hr _ hn,WeightedCoeff.meanZeroWeightedLift_apply] at h
  rw [←signedPairToDeleted_positive]
  exact (div_left_inj' (Weight.complex_ne_zero _ _)).mp h

end NLS.KdV
