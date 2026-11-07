import NLS.Articles.KdVPseudomeasures.OriginalHillH1ModeEnergyVariation
import NLS.Articles.KdVPseudomeasures.OriginalHillRoughKdVFrequency
import NLS.SequenceSpaces.OddPositiveFrequency

/-! The ACTUAL physical energy differential determines the full signed
canonical velocity of its bounded rough cotangent. The hypothesis is
only agreement of this cotangent with the actual H1 differential; it
never assumes an ambient rough Hamiltonian or an open selected gap. -/
noncomputable section
open Set Complex NLS.KdV NLS.Poisson NLS.WeightedCoeff NLS.ZakharovShabat NLS.LpSequence
namespace NLS.Articles.KdVPseudomeasures

theorem energy_cotangent_native_Hamiltonian_pair
    (q : RealSignedHilbert (signedStepOrder 0 1)) (L : PeriodOneHminusOne →L[ℂ] ℂ)
    (hL : ∀ h : RealSignedHilbert (signedStepOrder 0 1),
      L (hillRealMeanZeroInclusion (hillIntegerSourceInclusion 1 h))=
        (fderiv ℂ periodOneKdVHamiltonian (signedOneRealToScalarDomain q)) (signedOneRealToScalarDomain h))
    (n : ℕ+) :
    L (gardnerHamiltonianVector (hillHminusNativeCoordinate (n:ℤ))
      (hillRealMeanZeroInclusion (hillIntegerSourceInclusion 1 q)))=
        -I*(hillH1KdVFrequency n ((hillIntegerSobolevEquiv 1).equiv q):ℂ)*
          ((hillIntegerSobolevEquiv 1).equiv q).val.val.val (n:ℤ) ∧
    L (gardnerHamiltonianVector (hillHminusNativeCoordinate (-(n:ℤ)))
      (hillRealMeanZeroInclusion (hillIntegerSourceInclusion 1 q)))=
        I*(hillH1KdVFrequency n ((hillIntegerSobolevEquiv 1).equiv q):ℂ)*
          (starRingEnd ℂ) (((hillIntegerSobolevEquiv 1).equiv q).val.val.val (n:ℤ)) := by
  let z := ((hillIntegerSobolevEquiv 1).equiv q).val.val.val (n:ℤ)
  have h1 := energy_cotangent_on_native_mode_vector q L hL n 1
  have hi := energy_cotangent_on_native_mode_vector q L hL n I
  rw [hillNativeModeHamiltonianVector,map_add,map_smul,map_smul] at h1 hi
  norm_num [smul_eq_mul,Complex.mul_re,Complex.conj_re,Complex.conj_im] at h1 hi
  constructor
  · change _= -I*(hillH1KdVFrequency n ((hillIntegerSobolevEquiv 1).equiv q):ℂ)*z
    rw [← Complex.re_add_im z]
    linear_combination (norm := ring_nf) (-I*h1+hi)/2
    dsimp only [z]
    simp only [I_sq]
    ring
  · change _= I*(hillH1KdVFrequency n ((hillIntegerSobolevEquiv 1).equiv q):ℂ)*(starRingEnd ℂ) z
    rw [← Complex.re_add_im z]
    simp only [map_add,map_mul,Complex.conj_ofReal,Complex.conj_I]
    linear_combination (norm := ring_nf) (I*h1+hi)/2
    dsimp only [z]
    simp only [I_sq]
    ring

theorem energy_cotangent_native_positive_velocity
    (q : RealSignedHilbert (signedStepOrder 0 1)) (L : PeriodOneHminusOne →L[ℂ] ℂ)
    (hL : ∀ h : RealSignedHilbert (signedStepOrder 0 1),
      L (hillRealMeanZeroInclusion (hillIntegerSourceInclusion 1 h))=
        (fderiv ℂ periodOneKdVHamiltonian (signedOneRealToScalarDomain q)) (signedOneRealToScalarDomain h))
    (n : ℕ+) :
    (fderiv ℂ (hillHminusNativeCoordinate (n:ℤ)) (hillRealMeanZeroInclusion (hillIntegerSourceInclusion 1 q)))
      (gardnerHamiltonianDirection L)=
        I*(hillH1KdVFrequency n ((hillIntegerSobolevEquiv 1).equiv q):ℂ)*
          hillHminusNativeCoordinate (n:ℤ) (hillRealMeanZeroInclusion (hillIntegerSourceInclusion 1 q)) := by
  rw [apply_gardnerHamiltonianDirection,gardnerCotangentBivector_antisymm,← apply_gardnerHamiltonianDirection]
  change -L (gardnerHamiltonianVector (hillHminusNativeCoordinate (n:ℤ))
    (hillRealMeanZeroInclusion (hillIntegerSourceInclusion 1 q)))=_
  rw [(energy_cotangent_native_Hamiltonian_pair q L hL n).1,← hillIntegerSobolevEquiv_eq_nativeCoordinate]
  ring

theorem energy_cotangent_native_negative_velocity
    (q : RealSignedHilbert (signedStepOrder 0 1)) (L : PeriodOneHminusOne →L[ℂ] ℂ)
    (hL : ∀ h : RealSignedHilbert (signedStepOrder 0 1),
      L (hillRealMeanZeroInclusion (hillIntegerSourceInclusion 1 h))=
        (fderiv ℂ periodOneKdVHamiltonian (signedOneRealToScalarDomain q)) (signedOneRealToScalarDomain h))
    (n : ℕ+) :
    (fderiv ℂ (hillHminusNativeCoordinate (-(n:ℤ))) (hillRealMeanZeroInclusion (hillIntegerSourceInclusion 1 q)))
      (gardnerHamiltonianDirection L)=
        -I*(hillH1KdVFrequency n ((hillIntegerSobolevEquiv 1).equiv q):ℂ)*
          hillHminusNativeCoordinate (-(n:ℤ)) (hillRealMeanZeroInclusion (hillIntegerSourceInclusion 1 q)) := by
  rw [apply_gardnerHamiltonianDirection,gardnerCotangentBivector_antisymm,← apply_gardnerHamiltonianDirection]
  change -L (gardnerHamiltonianVector (hillHminusNativeCoordinate (-(n:ℤ)))
    (hillRealMeanZeroInclusion (hillIntegerSourceInclusion 1 q)))=_
  rw [(energy_cotangent_native_Hamiltonian_pair q L hL n).2,← hillIntegerSobolevEquiv_eq_nativeCoordinate,
    ((hillIntegerSobolevEquiv 1).equiv q).property (n:ℤ)]
  ring

theorem energy_cotangent_native_signed_velocity
    (q : RealSignedHilbert (signedStepOrder 0 1)) (L : PeriodOneHminusOne →L[ℂ] ℂ)
    (hL : ∀ h : RealSignedHilbert (signedStepOrder 0 1),
      L (hillRealMeanZeroInclusion (hillIntegerSourceInclusion 1 h))=
        (fderiv ℂ periodOneKdVHamiltonian (signedOneRealToScalarDomain q)) (signedOneRealToScalarDomain h))
    (k : ℤ) :
    (fderiv ℂ (hillHminusNativeCoordinate k) (hillRealMeanZeroInclusion (hillIntegerSourceInclusion 1 q)))
      (gardnerHamiltonianDirection L)=
        I*(oddPositiveFrequency (fun n => hillRoughKdVFrequency n (hillIntegerSourceInclusion 1 q)) k:ℂ)*
          hillHminusNativeCoordinate k (hillRealMeanZeroInclusion (hillIntegerSourceInclusion 1 q)) := by
  have hcases (j : ℤ) : j=0 ∨ (∃ n : ℕ+, j=(n:ℤ)) ∨ ∃ n : ℕ+, j= -(n:ℤ) := by
    cases j with
    | ofNat a =>
      cases a with
      | zero => exact Or.inl rfl
      | succ a => exact Or.inr (Or.inl ⟨⟨a+1,Nat.succ_pos a⟩,rfl⟩)
    | negSucc a => exact Or.inr (Or.inr ⟨⟨a+1,Nat.succ_pos a⟩,rfl⟩)
  rcases hcases k with rfl | ⟨n,rfl⟩ | ⟨n,rfl⟩
  · simp [hillHminusNativeCoordinate_zero_mode,oddPositiveFrequency_zero]
  · rw [oddPositiveFrequency_positive,hillRoughKdVFrequency_eq_physical_H1]
    exact energy_cotangent_native_positive_velocity q L hL n
  · rw [oddPositiveFrequency_neg,oddPositiveFrequency_positive,hillRoughKdVFrequency_eq_physical_H1,Complex.ofReal_neg]
    convert! energy_cotangent_native_negative_velocity q L hL n using 1; ring

end NLS.Articles.KdVPseudomeasures
