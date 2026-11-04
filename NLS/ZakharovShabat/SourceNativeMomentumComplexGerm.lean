import NLS.ZakharovShabat.SourceNativeMomentumBirkhoff

/-! # Actual holomorphic physical momentum germs in the native target

The independent physical momentum polynomial is composed with the actual
complex weighted inverse germ. Agreement holds on a full real neighborhood;
normalized action invariance retains the same original raw actions.
-/
noncomputable section
set_option autoImplicit false
open Set Filter Topology
open scoped ENNReal
namespace NLS.ZakharovShabat
namespace SourceBirkhoffMapComplexData
variable {W₀ B W : Set (CoeffPair 2)} {s : (n : ℤ) → CoeffPair 2 → DeletedCoeff 2 n}

/-- Every native real fractional target has a genuine holomorphic physical
Hamiltonian germ agreeing on a full real neighborhood with the global momentum. -/
theorem exists_complex_nativeMomentumBirkhoff_germ
    (D : SourceBirkhoffMapComplexData (by simp) (by norm_num) W₀ B W s)
    (z₀ : FourthSobolevBirkhoffTarget) :
    ∃ F : WeightedCoeffPair (sourceFrequencyWeight fourthSobolevSpectralWeight) 2 → ℂ,
      AnalyticAt ℂ F (WeightedCoeffPair.complexCLM (sourceFrequencyWeight fourthSobolevSpectralWeight) z₀) ∧
      (fun z => F (WeightedCoeffPair.complexCLM (sourceFrequencyWeight fourthSobolevSpectralWeight) z)) =ᶠ[𝓝 z₀]
        D.nativeMomentumBirkhoff := by
  let e := D.originalWeightedRealSobolevEquiv (by rfl) (3/2) (by norm_num)
  let a := e.symm z₀
  have hm : D.originalWeightedRealMap fourthSobolevSpectralWeight a = z₀ := e.apply_symm_apply z₀
  obtain ⟨g,hg,_,he⟩ := D.exists_complex_sobolevInverse_germ (by rfl) (3/2) (by norm_num) a
  have hg' : AnalyticAt ℂ g (WeightedCoeffPair.complexCLM (sourceFrequencyWeight fourthSobolevSpectralWeight) z₀) := by
    rw [← hm]
    exact hg
  have he' : ∀ᶠ z in 𝓝 z₀,
      g (WeightedCoeffPair.complexCLM (sourceFrequencyWeight fourthSobolevSpectralWeight) z) = (e.symm z).val := by
    rw [← hm]
    exact he
  refine ⟨fun z => sourceComplexNativeMomentum (g z),
    (analyticAt_sourceComplexNativeMomentum _).comp hg',?_⟩
  filter_upwards [he'] with z hz
  rw [hz]
  rfl

/-- Physical momentum in the normalized real Hilbert pair coordinates. The raw
physical actions are recovered by division by the squared positive weight. -/
def normalizedNativeMomentum
    (D : SourceBirkhoffMapComplexData (by simp) (by norm_num) W₀ B W s)
    (x : RealCoeff 2 × RealCoeff 2) : ℂ :=
  D.nativeMomentumBirkhoff
    ((NLS.Birkhoff.weightedRealCoordinates (sourceFrequencyWeight fourthSobolevSpectralWeight)).symm x)

/-- Actual holomorphic germs exist in the ordinary normalized complex pair
space, with full agreement on its included real form. -/
theorem exists_complex_normalizedNativeMomentum_germ
    (D : SourceBirkhoffMapComplexData (by simp) (by norm_num) W₀ B W s)
    (x : RealCoeff 2 × RealCoeff 2) :
    ∃ F : (Coeff 2 × Coeff 2) → ℂ,
      AnalyticAt ℂ F (((RealCoeff.complexCLM 2).prodMap (RealCoeff.complexCLM 2)) x) ∧
      (fun y => F (((RealCoeff.complexCLM 2).prodMap (RealCoeff.complexCLM 2)) y)) =ᶠ[𝓝 x]
        D.normalizedNativeMomentum := by
  let w := sourceFrequencyWeight fourthSobolevSpectralWeight
  let C := NLS.Birkhoff.weightedComplexCoordinates (p := 2) w
  let R := NLS.Birkhoff.weightedRealCoordinates (p := 2) w
  let J := (RealCoeff.complexCLM 2).prodMap (RealCoeff.complexCLM 2)
  obtain ⟨F,hF,he⟩ := D.exists_complex_nativeMomentumBirkhoff_germ (R.symm x)
  have hc : C.symm (J x) = WeightedCoeffPair.complexCLM w (R.symm x) :=
    NLS.Birkhoff.weightedComplexCoordinates_symm_real w x
  have hFC : AnalyticAt ℂ F (C.symm (J x)) := by rw [hc]; exact hF
  refine ⟨fun z => F (C.symm z),hFC.comp (C.symm.analyticAt (J x)),?_⟩
  filter_upwards [R.symm.continuous.continuousAt.tendsto.eventually he] with y hy
  change F (C.symm (J y)) = D.normalizedNativeMomentum y
  rw [NLS.Birkhoff.weightedComplexCoordinates_symm_real w y]
  exact hy

/-- Equality of normalized actions preserves physical momentum, since both raw
action sequences differ by exactly the same squared positive weight. -/
theorem normalizedNativeMomentum_eq_of_actions
    (D : SourceBirkhoffMapComplexData (by simp) (by norm_num) W₀ B W s)
    (x y : RealCoeff 2 × RealCoeff 2)
    (h : ∀ n, RealCoeff.pairAction y n = RealCoeff.pairAction x n) :
    D.normalizedNativeMomentum y = D.normalizedNativeMomentum x := by
  let w := sourceFrequencyWeight fourthSobolevSpectralWeight
  let R := NLS.Birkhoff.weightedRealCoordinates (p := 2) w
  have hn (u : RealCoeff 2 × RealCoeff 2) (n : ℤ) : RealCoeff.pairAction u n =
      (w n)^2*RealCoeff.pairAction (originalWeightedRealTarget fourthSobolevSpectralWeight (R.symm u)) n := by
    have ht := NLS.Birkhoff.weightedRealCoordinates_pairAction w
      (fun n => fourthSobolevSpectralWeight.one_le (2*n)) (R.symm u) n
    have he : NLS.Birkhoff.weightedRealCoordinates w (R.symm u) = u := R.apply_symm_apply u
    rw [he] at ht
    exact ht
  apply D.nativeMomentumBirkhoff_eq_of_actions
  intro n
  apply mul_left_cancel₀ (pow_ne_zero 2 (w.positive n).ne')
  exact (hn y n).symm.trans ((h n).trans (hn x n))

end SourceBirkhoffMapComplexData
end NLS.ZakharovShabat
