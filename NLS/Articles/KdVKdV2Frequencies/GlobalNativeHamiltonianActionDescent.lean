import NLS.Articles.KdVKdV2Frequencies.GlobalNativeHamiltonianActionInvariance
import NLS.SequenceSpaces.SignedCartesianActions
import NLS.SequenceSpaces.ScalarActionDescentFromRealGerms

/-! # Analytic action descent for the SAME original native Hamiltonians

Actual complex inverse germs, complete real action invariance and the
exact signed/Cartesian normalization give a globally glued analytic
factor near the entire nonnegative normalized action cone.
-/
noncomputable section
set_option autoImplicit false
open Set Complex NLS.KdV NLS.ZakharovShabat
open scoped ENNReal ComplexConjugate
namespace NLS.Articles.KdVKdV2Frequencies.GlobalRoughAbelianForwardData

/-- A genuine complex native source germ equals the SAME fixed inverse
on its entire physical real slice, at EVERY target and native order. -/
theorem nativeIntegerInverseSource_has_complex_germ (D : GlobalRoughAbelianForwardData)
    (s : ℕ) (z : physicalRealDeletedSubmodule) :
    ∃ T : Set (DeletedCoeff 2 0), IsOpen T ∧ z.val ∈ T ∧
      ∃ G : DeletedCoeff 2 0 → ScalarSobolev s, AnalyticOnNhd ℂ G T ∧
        ∀ y : physicalRealDeletedSubmodule, y.val ∈ T → G y.val = D.nativeIntegerInverseSource s y := by
  obtain ⟨T,hT,hz,G,hG,hmatch⟩ := D.realNativeInverse_has_complex_germ ((s : ℝ)+1) (by positivity) z
  let L := WeightedCoeff.meanZeroWeightedLiftCLM (Weight.sobolev (s : ℝ))
  refine ⟨T,hT,hz,L ∘ G,?_,?_⟩
  · intro a ha
    exact (L.analyticAt _).comp (hG a ha)
  · intro y hy
    exact congrArg L (hmatch y hy)

/-- Raw lifting and native normalization cancel exactly, in the original norms. -/
theorem rawIntegerInverseSource_real_lift (D : GlobalRoughAbelianForwardData)
    (s : ℕ) (a : physicalRealDeletedSubmodule) :
    D.rawIntegerInverseSource s
      (physicalRealMeanZeroWeightedIsometry (Weight.sobolev ((s : ℝ)+1/2))
        (Weight.sobolev_neg _) a) = D.nativeIntegerInverseSource s a := by
  change D.nativeIntegerInverseSource s
    ((physicalRealMeanZeroWeightedIsometry (Weight.sobolev ((s : ℝ)+1/2))
      (Weight.sobolev_neg _)).symm
      (physicalRealMeanZeroWeightedIsometry (Weight.sobolev ((s : ℝ)+1/2))
        (Weight.sobolev_neg _) a)) = _
  rw [LinearIsometryEquiv.symm_apply_apply]

/-- Complete normalized signed products determine the original entire inverse
Hill discriminant, with the native weights canceled explicitly. -/
theorem nativeIntegerInverseSource_discriminant_eq_of_products
    (D : GlobalRoughAbelianForwardData) (s : ℕ) (a b : physicalRealDeletedSubmodule)
    (h : ∀ n : ℕ+, a.val.val (n : ℤ)*a.val.val (-(n : ℤ)) =
      b.val.val (n : ℤ)*b.val.val (-(n : ℤ))) :
    hillHminusDiscriminant (nativeHillSource s (D.nativeIntegerInverseSource s a)) =
      hillHminusDiscriminant (nativeHillSource s (D.nativeIntegerInverseSource s b)) := by
  let E := physicalRealMeanZeroWeightedIsometry (Weight.sobolev ((s : ℝ)+1/2)) (Weight.sobolev_neg _)
  have he := D.rawIntegerInverseSource_discriminant_eq_of_actions_eq s s (E a) (E b) (by
    intro n
    change (a.val.val (n : ℤ)/_)*(a.val.val (-(n : ℤ))/_)=
      (b.val.val (n : ℤ)/_)*(b.val.val (-(n : ℤ))/_)
    rw [div_mul_div_comm,div_mul_div_comm,h n])
  rw [D.rawIntegerInverseSource_real_lift,D.rawIntegerInverseSource_real_lift] at he
  exact he

/-- A global extension used only through its real Cartesian values. Its
holomorphic germs below are built from the actual complex inverse. -/
def nativeCartesianHamiltonian (D : GlobalRoughAbelianForwardData) (s : ℕ)
    (H : ScalarSobolev s → ℂ) (z : Coeff 2 × Coeff 2) : ℂ :=
  H (D.nativeIntegerInverseSource s (physicalRealDeletedProjection (Coeff.cartesianToSigned z)))

/-- Every real Cartesian target has a genuine holomorphic physical Hamiltonian germ. -/
theorem nativeCartesianHamiltonian_has_complex_germ (D : GlobalRoughAbelianForwardData)
    (s : ℕ) (H : ScalarSobolev s → ℂ) (hH : AnalyticOnNhd ℂ H univ)
    (z : Coeff 2 × Coeff 2) (hz : z ∈ Coeff.realPairLocus 2) :
    ∃ U : Set (Coeff 2 × Coeff 2), IsOpen U ∧ z ∈ U ∧
      ∃ F : (Coeff 2 × Coeff 2) → ℂ, AnalyticOnNhd ℂ F U ∧
        ∀ y ∈ U, y ∈ Coeff.realPairLocus 2 → F y = D.nativeCartesianHamiltonian s H y := by
  let a : physicalRealDeletedSubmodule := ⟨Coeff.cartesianToSigned z,Coeff.cartesianToSigned_real z hz⟩
  obtain ⟨T,hT,hzT,G,hG,hmatch⟩ := D.nativeIntegerInverseSource_has_complex_germ s a
  refine ⟨Coeff.cartesianToSigned ⁻¹' T,hT.preimage Coeff.cartesianToSigned.continuous,hzT,
    H ∘ G ∘ Coeff.cartesianToSigned,?_,?_⟩
  · intro y hy
    exact (hH _ (mem_univ _)).comp ((hG _ hy).comp (Coeff.cartesianToSigned.analyticAt y))
  · intro y hy hyr
    let b : physicalRealDeletedSubmodule := ⟨Coeff.cartesianToSigned y,Coeff.cartesianToSigned_real y hyr⟩
    have hp : physicalRealDeletedProjection (Coeff.cartesianToSigned y) = b := physicalRealDeletedProjection_coe b
    change H (G (Coeff.cartesianToSigned y)) = H (D.nativeIntegerInverseSource s _)
    rw [hp,hmatch b hy]

/-- A native spectral Hamiltonian has a globally glued analytic factor near
ALL normalized nonnegative actions, with exact recovery at EVERY actual
physical real target and with closed gaps allowed. -/
theorem exists_nativeHamiltonian_analytic_action_factor
    (D : GlobalRoughAbelianForwardData) (s : ℕ) (H : ScalarSobolev s → ℂ)
    (hH : AnalyticOnNhd ℂ H univ)
    (hiso : ∀ u v : ScalarSobolev s,
      (∀ n : ℤ, u.val (-n) = conj (u.val n)) → (∀ n : ℤ, v.val (-n) = conj (v.val n)) →
      u.val 0 = 0 → v.val 0 = 0 →
      hillHminusDiscriminant (nativeHillSource s u) = hillHminusDiscriminant (nativeHillSource s v) → H u = H v) :
    ∃ U : Set (Coeff 1), ∃ g : Coeff 1 → ℂ,
      IsOpen U ∧ Coeff.nonnegativeLocus 1 ⊆ U ∧ AnalyticOnNhd ℂ g U ∧
      ∀ a : physicalRealDeletedSubmodule,
        g (quadraticActionsExponent (q := 1) (Coeff.signedToCartesian a.val)) =
          H (D.nativeIntegerInverseSource s a) := by
  have hinv : ∀ z w : Coeff 2 × Coeff 2,
      z ∈ Coeff.realPairLocus 2 → w ∈ Coeff.realPairLocus 2 →
      quadraticActionsExponent (q := 1) w = quadraticActionsExponent z →
      D.nativeCartesianHamiltonian s H w = D.nativeCartesianHamiltonian s H z := by
    intro z w hz hw he
    let a := physicalRealDeletedProjection (Coeff.cartesianToSigned w)
    let b := physicalRealDeletedProjection (Coeff.cartesianToSigned z)
    have ha : a.val = Coeff.cartesianToSigned w := congrArg Subtype.val
      (physicalRealDeletedProjection_coe ⟨Coeff.cartesianToSigned w,Coeff.cartesianToSigned_real w hw⟩)
    have hb : b.val = Coeff.cartesianToSigned z := congrArg Subtype.val
      (physicalRealDeletedProjection_coe ⟨Coeff.cartesianToSigned z,Coeff.cartesianToSigned_real z hz⟩)
    apply hiso _ _ (D.nativeIntegerInverseSource_real s a) (D.nativeIntegerInverseSource_real s b)
      (D.nativeIntegerInverseSource_zero s a) (D.nativeIntegerInverseSource_zero s b)
    apply D.nativeIntegerInverseSource_discriminant_eq_of_products s a b
    intro n
    rw [ha,hb,Coeff.cartesianToSigned_product w (n : ℤ) (by exact_mod_cast n.property),
      Coeff.cartesianToSigned_product z (n : ℤ) (by exact_mod_cast n.property),he]
  obtain ⟨U,g,hU,hpos,hg,hrec⟩ := Coeff.exists_analytic_action_factor_of_real_germs
    (p := 2) (q := 1) (by simp) (D.nativeCartesianHamiltonian s H) hinv
    (D.nativeCartesianHamiltonian_has_complex_germ s H hH)
  refine ⟨U,g,hU,hpos,hg,?_⟩
  intro a
  have he := hrec (Coeff.signedToCartesian a.val) (Coeff.signedToCartesian_real a)
  simpa only [nativeCartesianHamiltonian,Coeff.cartesianToSigned_signedToCartesian,
    physicalRealDeletedProjection_coe] using he

/-- Printed H1 has an analytic factor on a complex neighborhood of the ENTIRE
nonnegative normalized action cone, including every closed-gap point. -/
theorem exists_birkhoffKdV_analytic_action_factor (D : GlobalRoughAbelianForwardData) :
    ∃ U : Set (Coeff 1), ∃ g : Coeff 1 → ℂ,
      IsOpen U ∧ Coeff.nonnegativeLocus 1 ⊆ U ∧ AnalyticOnNhd ℂ g U ∧
      ∀ a : physicalRealDeletedSubmodule,
        g (quadraticActionsExponent (q := 1) (Coeff.signedToCartesian a.val)) =
          nativeKdVHamiltonian (D.nativeIntegerInverseSource 1 a) := by
  exact D.exists_nativeHamiltonian_analytic_action_factor 1 nativeKdVHamiltonian
    (fun q _ => analyticAt_nativeKdVHamiltonian q) nativeKdVHamiltonian_eq_of_discriminant_eq

/-- Printed H2 has the corresponding full native analytic action factor. -/
theorem exists_birkhoffKdV2_analytic_action_factor (D : GlobalRoughAbelianForwardData) :
    ∃ U : Set (Coeff 1), ∃ g : Coeff 1 → ℂ,
      IsOpen U ∧ Coeff.nonnegativeLocus 1 ⊆ U ∧ AnalyticOnNhd ℂ g U ∧
      ∀ a : physicalRealDeletedSubmodule,
        g (quadraticActionsExponent (q := 1) (Coeff.signedToCartesian a.val)) =
          nativeKdV2Hamiltonian (D.nativeIntegerInverseSource 2 a) := by
  exact D.exists_nativeHamiltonian_analytic_action_factor 2 nativeKdV2Hamiltonian
    (fun q _ => analyticAt_nativeKdV2Hamiltonian q) nativeKdV2Hamiltonian_eq_of_discriminant_eq

end NLS.Articles.KdVKdV2Frequencies.GlobalRoughAbelianForwardData
