import NLS.KdV.HillCorrectedBoundaryGreen

noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology
open scoped ENNReal Classical

namespace NLS.KdV



/-- The boundary-forced equation is a scalar family of coefficient identities;
the constant parity source is not incorrectly treated as an l2 input. -/
def IsHillBoundaryForcedFourierSolution
    (q : WeightedCoeff SpectralWeight.one.toWeight 2) (z : ℂ) (r : ℤ) (J : ℂ)
    (f : WeightedCoeff SpectralWeight.one.toWeight 1) : Prop :=
  ∀ k : ℤ, (z-(freeHillValue k : ℂ))*f.val k =
    (SpectralWeight.one.convolution q f).val k-J*(if k%2=r%2 then 1 else 0)

variable (q : WeightedCoeff SpectralWeight.one.toWeight 2) (n : ℕ) (hn : 1 ≤ n)
  (r : ℤ) (z : ℂ) (hz : z ∈ reducedHillStrip n) (hcut : 8*‖q‖ ≤ (n : ℝ))

/-- Exact complementary decomposition of a genuine boundary-forced solution. -/
theorem hillBoundaryForcedFourier_decompose (J : ℂ)
    (f : WeightedCoeff SpectralWeight.one.toWeight 1)
    (hf : IsHillBoundaryForcedFourierSolution q z r J f) :
    f = hillModes SpectralWeight.one.toWeight n
        (hillModeCoordinates SpectralWeight.one.toWeight 1 n f) +
      hillComplementToL1 SpectralWeight.one.toWeight n hn z hz
        (SpectralWeight.one.convolution q f)-J • hillUnitFreeBoundaryGreen n r z := by
  apply Subtype.ext
  funext k
  simp only [WeightedCoeff.sub_val,WeightedCoeff.add_val,WeightedCoeff.smul_val,
    hillModes_apply,hillComplementToL1_apply,hillUnitFreeBoundaryGreen,hillUnitWeightLift_apply,
    hillFreeBoundaryGreen_apply n hn r z hz]
  by_cases hkp : k=(n : ℤ)
  · subst k
    simp [show (n : ℤ) ≠ -(n : ℤ) by omega,hillModeCoordinates_apply]
  by_cases hkm : k=-(n : ℤ)
  · subst k
    simp [show -(n : ℤ) ≠ (n : ℤ) by omega,hillModeCoordinates_apply]
  have hk : k.natAbs ≠ n := fun h => (Int.natAbs_eq_iff.mp h).elim hkp hkm
  rw [if_neg hkp,if_neg hkm,if_neg hk,zero_add,zero_add]
  have hh := congrArg (fun c : ℂ => (z-(freeHillValue k : ℂ))⁻¹*c) (hf k)
  rw [← mul_assoc,inv_mul_cancel₀ (freeHill_denominator_ne_zero hn hz hk),one_mul] at hh
  rw [hh]
  split_ifs <;> ring

/-- The potential of a forced solution is obtained by correcting the actual
summable boundary vector, alongside the two resonant amplitudes. -/
theorem hillBoundaryForcedFourier_potential (J : ℂ)
    (f : WeightedCoeff SpectralWeight.one.toWeight 1)
    (hf : IsHillBoundaryForcedFourierSolution q z r J f) :
    SpectralWeight.one.convolution q f =
      hillEffectivePotential SpectralWeight.one q n hn z hz hcut
        (hillModeCoordinates SpectralWeight.one.toWeight 1 n f)-
      J • hillBoundaryGreenPotential q n hn r z hz hcut := by
  have hd := hillBoundaryForcedFourier_decompose q n hn r z hz J f hf
  have he := congrArg (SpectralWeight.one.convolutionCLM q) hd
  simp only [map_sub,map_add,map_smul,SpectralWeight.convolutionCLM_apply] at he
  have hr : SpectralWeight.one.convolution q f-
      hillTailPerturbation SpectralWeight.one q n hn z hz (SpectralWeight.one.convolution q f) =
      hillModePotential SpectralWeight.one q n (hillModeCoordinates SpectralWeight.one.toWeight 1 n f)-
        J • SpectralWeight.one.convolution q (hillUnitFreeBoundaryGreen n r z) := by
    apply sub_eq_iff_eq_add.mpr
    calc
      _ = _ := he
      _ = _ := by
        simp only [hillModePotential,hillTailPerturbation,ContinuousLinearMap.comp_apply,
          SpectralWeight.convolutionCLM_apply]
        abel
  have hu := hillTailInverse_unique SpectralWeight.one q n hn z hz hcut _ _ hr
  rw [map_sub,map_smul] at hu
  exact hu

/-- Exact reconstruction including the original endpoint derivative jump. -/
theorem hillBoundaryForcedFourier_reconstruct (J : ℂ)
    (f : WeightedCoeff SpectralWeight.one.toWeight 1)
    (hf : IsHillBoundaryForcedFourierSolution q z r J f) :
    f = hillReconstruct SpectralWeight.one q n hn z hz hcut
        (hillModeCoordinates SpectralWeight.one.toWeight 1 n f)-
      J • hillCorrectedBoundaryGreen q n hn r z hz hcut := by
  have hd := hillBoundaryForcedFourier_decompose q n hn r z hz J f hf
  have hp := hillBoundaryForcedFourier_potential q n hn r z hz hcut J f hf
  rw [hp,map_sub,map_smul] at hd
  rw [hillCorrectedBoundaryGreen,smul_add]
  change f = _
  change f = hillModes SpectralWeight.one.toWeight n
      (hillModeCoordinates SpectralWeight.one.toWeight 1 n f)+
    hillComplementToL1 SpectralWeight.one.toWeight n hn z hz
      (hillEffectivePotential SpectralWeight.one q n hn z hz hcut
        (hillModeCoordinates SpectralWeight.one.toWeight 1 n f))-
    (J • hillUnitFreeBoundaryGreen n r z+J • hillComplementToL1 SpectralWeight.one.toWeight n hn z hz
      (hillBoundaryGreenPotential q n hn r z hz hcut))
  calc
    f = _ := hd
    _ = _ := by abel

/-- The finite two-mode equation has the same source in its two rows. -/
theorem hillBoundaryForcedFourier_reduced (J : ℂ)
    (f : WeightedCoeff SpectralWeight.one.toWeight 1)
    (hf : IsHillBoundaryForcedFourierSolution q z r J f) :
    hillReducedOperator SpectralWeight.one q n hn z hz hcut
        (hillModeCoordinates SpectralWeight.one.toWeight 1 n f) =
      -J • (((if (n : ℤ)%2=r%2 then 1 else 0),
        (if (n : ℤ)%2=r%2 then 1 else 0))+
        hillModeCoordinates SpectralWeight.one.toWeight 2 n
          (hillBoundaryGreenPotential q n hn r z hz hcut)) := by
  have hp := hillBoundaryForcedFourier_potential q n hn r z hz hcut J f hf
  apply Prod.ext
  · change (z-(freeHillValue n : ℂ))*f.val n-
      (hillEffectivePotential SpectralWeight.one q n hn z hz hcut
        (hillModeCoordinates SpectralWeight.one.toWeight 1 n f)).val n =
      -J*((if (n : ℤ)%2=r%2 then 1 else 0)+(hillBoundaryGreenPotential q n hn r z hz hcut).val n)
    have hh := hf n
    rw [hp,WeightedCoeff.sub_val,WeightedCoeff.smul_val] at hh
    linear_combination hh
  · change (z-(freeHillValue n : ℂ))*f.val (-(n : ℤ))-
      (hillEffectivePotential SpectralWeight.one q n hn z hz hcut
        (hillModeCoordinates SpectralWeight.one.toWeight 1 n f)).val (-(n : ℤ)) =
      -J*((if (n : ℤ)%2=r%2 then 1 else 0)+(hillBoundaryGreenPotential q n hn r z hz hcut).val (-(n : ℤ)))
    have hh := hf (-(n : ℤ))
    rw [freeHillValue_neg,hp,WeightedCoeff.sub_val,WeightedCoeff.smul_val] at hh
    have hnpar : (-(n : ℤ))%2=(n : ℤ)%2 := by omega
    rw [hnpar] at hh
    linear_combination hh

/-- Reconstruction from resonant amplitudes and the literal boundary source. -/
def hillBoundaryReconstruct (u : ℂ × ℂ) (J : ℂ) :
    WeightedCoeff SpectralWeight.one.toWeight 1 :=
  hillReconstruct SpectralWeight.one q n hn z hz hcut u-
    J • hillCorrectedBoundaryGreen q n hn r z hz hcut

/-- The boundary correction does not alter either raw resonant amplitude. -/
theorem hillModeCoordinates_boundaryReconstruct (u : ℂ × ℂ) (J : ℂ) :
    hillModeCoordinates SpectralWeight.one.toWeight 1 n
      (hillBoundaryReconstruct q n hn r z hz hcut u J) = u := by
  rw [hillBoundaryReconstruct,map_sub,map_smul,hillModeCoordinates_reconstruct,
    hillModeCoordinates_correctedBoundaryGreen,smul_zero,sub_zero]

theorem convolution_hillBoundaryReconstruct (u : ℂ × ℂ) (J : ℂ) :
    SpectralWeight.one.convolution q (hillBoundaryReconstruct q n hn r z hz hcut u J) =
      hillEffectivePotential SpectralWeight.one q n hn z hz hcut u-
        J • hillBoundaryGreenPotential q n hn r z hz hcut := by
  change SpectralWeight.one.convolutionCLM q (_-J • _) = _
  rw [map_sub,map_smul,SpectralWeight.convolutionCLM_apply,SpectralWeight.convolutionCLM_apply,
    convolution_hillReconstruct,convolution_hillCorrectedBoundaryGreen]

/-- The finite forced equation suffices to reconstruct an actual solution at
every Fourier frequency. It remains valid at singular periodic energies. -/
theorem hillBoundaryReconstruct_isForced (u : ℂ × ℂ) (J : ℂ)
    (hred : hillReducedOperator SpectralWeight.one q n hn z hz hcut u =
      -J • (((if (n : ℤ)%2=r%2 then 1 else 0),
        (if (n : ℤ)%2=r%2 then 1 else 0))+
        hillModeCoordinates SpectralWeight.one.toWeight 2 n
          (hillBoundaryGreenPotential q n hn r z hz hcut))) :
    IsHillBoundaryForcedFourierSolution q z r J (hillBoundaryReconstruct q n hn r z hz hcut u J) := by
  have hcoords := hillModeCoordinates_boundaryReconstruct q n hn r z hz hcut u J
  intro k
  change (z-(freeHillValue k : ℂ))*(hillBoundaryReconstruct q n hn r z hz hcut u J).val k =
    (SpectralWeight.one.convolution q (hillBoundaryReconstruct q n hn r z hz hcut u J)).val k-
      J*(if k%2=r%2 then 1 else 0)
  rw [convolution_hillBoundaryReconstruct,WeightedCoeff.sub_val,WeightedCoeff.smul_val]
  by_cases hkp : k=(n : ℤ)
  · subst k
    have hm := congrArg Prod.fst hcoords
    change (hillBoundaryReconstruct q n hn r z hz hcut u J).val n = u.1 at hm
    rw [hm]
    have hh := congrArg Prod.fst hred
    change (z-(freeHillValue n : ℂ))*u.1-
      (hillEffectivePotential SpectralWeight.one q n hn z hz hcut u).val n =
      -J*((if (n : ℤ)%2=r%2 then 1 else 0)+(hillBoundaryGreenPotential q n hn r z hz hcut).val n) at hh
    linear_combination hh
  by_cases hkm : k=-(n : ℤ)
  · subst k
    have hm := congrArg Prod.snd hcoords
    change (hillBoundaryReconstruct q n hn r z hz hcut u J).val (-(n : ℤ)) = u.2 at hm
    have hnpar : (-(n : ℤ))%2=(n : ℤ)%2 := by omega
    rw [hm,freeHillValue_neg,hnpar]
    have hh := congrArg Prod.snd hred
    change (z-(freeHillValue n : ℂ))*u.2-
      (hillEffectivePotential SpectralWeight.one q n hn z hz hcut u).val (-(n : ℤ)) =
      -J*((if (n : ℤ)%2=r%2 then 1 else 0)+(hillBoundaryGreenPotential q n hn r z hz hcut).val (-(n : ℤ))) at hh
    linear_combination hh
  have hk : k.natAbs ≠ n := fun h => (Int.natAbs_eq_iff.mp h).elim hkp hkm
  have hfval : (hillBoundaryReconstruct q n hn r z hz hcut u J).val k =
      (z-(freeHillValue k : ℂ))⁻¹*(hillEffectivePotential SpectralWeight.one q n hn z hz hcut u).val k-
        J*(hillCorrectedBoundaryGreen q n hn r z hz hcut).val k := by
    change ((hillModes SpectralWeight.one.toWeight n u).val k+
      (hillComplementToL1 SpectralWeight.one.toWeight n hn z hz
        (hillEffectivePotential SpectralWeight.one q n hn z hz hcut u)).val k)-_ = _
    rw [hillModes_apply,hillComplementToL1_apply,if_neg hkp,if_neg hkm,if_neg hk,zero_add,zero_add,WeightedCoeff.smul_val]
  rw [hfval]
  have hg := hillCorrectedBoundaryGreen_complement_equation q n hn r z hz hcut k hk
  have ha : (z-(freeHillValue k : ℂ))*((z-(freeHillValue k : ℂ))⁻¹*
      (hillEffectivePotential SpectralWeight.one q n hn z hz hcut u).val k) =
      (hillEffectivePotential SpectralWeight.one q n hn z hz hcut u).val k := by
    rw [← mul_assoc,mul_inv_cancel₀ (freeHill_denominator_ne_zero hn hz hk),one_mul]
  rw [mul_sub,ha]
  linear_combination -J*hg

/-- Exact equivalence with the finite forced equation, not just a necessary
resonant condition or a homogeneous-eigenfunction substitute. -/
theorem hillBoundaryReconstruct_isForced_iff (u : ℂ × ℂ) (J : ℂ) :
    IsHillBoundaryForcedFourierSolution q z r J (hillBoundaryReconstruct q n hn r z hz hcut u J) ↔
    hillReducedOperator SpectralWeight.one q n hn z hz hcut u =
      -J • (((if (n : ℤ)%2=r%2 then 1 else 0),
        (if (n : ℤ)%2=r%2 then 1 else 0))+
        hillModeCoordinates SpectralWeight.one.toWeight 2 n
          (hillBoundaryGreenPotential q n hn r z hz hcut)) := by
  constructor
  · intro hf
    have hh := hillBoundaryForcedFourier_reduced q n hn r z hz hcut J
      (hillBoundaryReconstruct q n hn r z hz hcut u J) hf
    rwa [hillModeCoordinates_boundaryReconstruct] at hh
  · exact hillBoundaryReconstruct_isForced q n hn r z hz hcut u J

end NLS.KdV
