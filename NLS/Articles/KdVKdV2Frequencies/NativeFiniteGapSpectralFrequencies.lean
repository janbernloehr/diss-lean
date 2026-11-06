import NLS.Articles.KdVKdV2Frequencies.NativeFiniteGapCoordinateJets
import NLS.Articles.KdVKdV2Frequencies.NativeFiniteGapContinuousSources
import NLS.Articles.KdVKdV2Frequencies.SmoothAbelianCoordinateMotion

/-! # Intrinsic physical frequencies equal actual finite Dirichlet spectral sums

Both sides are defined independently. Equality follows by comparing actual
physical PDE coordinate derivatives and cancelling a proved nonzero open
coordinate. Native finite-gap regularity supplies every smoothness premise.
-/
noncomputable section
set_option autoImplicit false
open Set Complex Filter Topology NLS.KdV NLS.ZakharovShabat NLS.Fourier
open scoped ContDiff
namespace NLS.Articles.KdVKdV2Frequencies.GlobalRoughAbelianForwardData

/-- The actual finite Dirichlet spectral sum for the canonical physical Kdv source. -/
def nativeKdVDirichletFrequency
    (q : physicalRealMeanZeroWeightedSubmodule (Weight.sobolev ((1 : ℕ) : ℝ)))
    (N : ℕ) (n : ℕ+) : ℂ :=
  let p := nativeHillPhysicalSource 1 q.val q.property.1
  ∑ j ∈ Finset.range N,
    hillAbelianSelectedGlobalPsi p.val p.property.1 p.property.2 n n.pos
      (hillDirichletEnergy p.val p.property.1 p.property.2 (j+1) (by omega))*
        kdvDirichletVelocityCoefficient (nativeHillContinuousSource 1 (by decide) q.val) p (j+1)

/-- At every actual native finite-gap source, the intrinsic physical Kdv
frequency equals the actual spectral Dirichlet sum at EVERY open own mode. -/
theorem native_finiteGap_kdv_frequency_eq_dirichlet (D : GlobalRoughAbelianForwardData)
    (q : physicalRealMeanZeroWeightedSubmodule (Weight.sobolev ((1 : ℕ) : ℝ))) (S : Finset ℕ+)
    (hq : ∀ n : ℕ+, n ∉ S → hillRealGapHalfLength
      (nativeHillPhysicalSource 1 q.val q.property.1).val
      (nativeHillPhysicalSource 1 q.val q.property.1).property.1
      (nativeHillPhysicalSource 1 q.val q.property.1).property.2 n=0)
    (N : ℕ) (hSN : ∀ k ∈ S, (k : ℕ)≤N) (n : ℕ+)
    (hopen : hillRealGapHalfLength (nativeHillPhysicalSource 1 q.val q.property.1).val
      (nativeHillPhysicalSource 1 q.val q.property.1).property.1
      (nativeHillPhysicalSource 1 q.val q.property.1).property.2 n≠0) :
    (D.nativeSourceHierarchyFrequency 1 3 (by norm_num) q n : ℂ) = nativeKdVDirichletFrequency q N n := by
  classical
  let Q := nativeHillContinuousSource 1 (by decide) q.val
  let p := nativeHillPhysicalSource 1 q.val q.property.1
  have hf := nativeHillContinuousSource_finiteGap_smooth 1 (by decide) q S hq
  have hp := nativeHillContinuousSource_periodic 1 (by decide) q.val
  have hr := nativeHillContinuousSource_real 1 (by decide) q.val q.property.1
  let pQ : RealPeriodOneHillPotential := ⟨hillContinuousCoefficients Q,
    hillContinuousCoefficients_mem_even Q hp,isRealHillPotential_hillContinuousCoefficients Q hr⟩
  have heq : pQ=p := Subtype.ext (hillContinuousCoefficients_nativeHillContinuousSource 1 (by decide) q.val q.property.1)
  have h0q : SpectralWeight.one.toCoeff (0 : WeightedCoeff SpectralWeight.one.toWeight 2)∈Coeff.paritySubspace 0 := by
    rw [map_zero]
    exact (Coeff.paritySubspace 0).zero_mem
  have h0r : IsRealHillPotential (SpectralWeight.one.toCoeff (0 : WeightedCoeff SpectralWeight.one.toWeight 2)) := by
    rw [map_zero]
    intro k
    simp
  obtain ⟨G,hG,_hG0,_hDZ,hmatch⟩ := exists_hillDirichletAbelianCoordinate_analytic_extension
    p.val p.property.1 p.property.2 h0q h0r n n.pos
  have hs := fderiv_hillDirichletAbelianCoordinate_finite_gap_both_pde Q hf hp hr n n.pos
  have hc : ∀ (k : ℕ) (_hk : 1≤k), N<k → hillRealGapHalfLength p.val p.property.1 p.property.2 k=0 := by
    intro k hk hNk
    apply hq ⟨k,by omega⟩
    intro hmem
    have h := hSN ⟨k,by omega⟩ hmem
    change k≤N at h
    omega
  have hcQ : ∀ (k : ℕ) (_hk : 1≤k), N<k → hillRealGapHalfLength pQ.val pQ.property.1 pQ.property.2 k=0 := by
    simpa only [heq] using hc
  have hGQ : DifferentiableAt ℂ G (SpectralWeight.one.toCoeff pQ.val) := by
    rw [heq]
    exact hG.differentiableAt
  have hmQ : ∀ᶠ a : RealPeriodOneHillPotential in 𝓝 pQ,
      G (SpectralWeight.one.toCoeff a.val)=hillDirichletAbelianCoordinate a.val a.property.1 a.property.2 n n.pos := by
    rw [heq]
    exact hmatch
  have hspec := (hs N hcQ G hGQ hmQ).1
  change (fderiv ℂ G (SpectralWeight.one.toCoeff pQ.val))
      (kdvFourierDirection (fun x : ℝ => Q (x : AddCircle (2 : ℝ))) hf) =
      (∑ j ∈ Finset.range N, hillAbelianSelectedGlobalPsi pQ.val pQ.property.1 pQ.property.2 n n.pos
        (hillDirichletEnergy pQ.val pQ.property.1 pQ.property.2 (j+1) (by omega))*
          kdvDirichletVelocityCoefficient Q pQ (j+1))*
            (I*hillDirichletAbelianCoordinate pQ.val pQ.property.1 pQ.property.2 n n.pos) at hspec
  rw [heq] at hspec
  have hcoeff (k : ℤ) : q.val.val k=periodOneCoefficient (fun x : ℝ => Q (x : AddCircle (2 : ℝ))) k :=
    (nativeHillContinuousSource_coefficient 1 (by decide) q.val k).symm
  have hjet := D.native_finiteGap_kdv_coordinate_jet q S hq _ hf hp hcoeff n G hG hmatch
  have hnS : n ∈ S := by by_contra h; exact hopen (hq n h)
  rw [if_pos hnS] at hjet
  have hz : hillDirichletAbelianCoordinate p.val p.property.1 p.property.2 n n.pos≠0 :=
    fun h => hopen ((hillDirichletAbelianCoordinate_eq_zero_iff p.val p.property.1 p.property.2 h0q h0r n n.pos).mp h)
  have hi : I*hillDirichletAbelianCoordinate p.val p.property.1 p.property.2 n n.pos≠0 := mul_ne_zero I_ne_zero hz
  apply mul_right_cancel₀ hi
  rw [←mul_assoc,←hjet]
  exact hspec

/-- The actual finite Dirichlet spectral sum for the canonical physical Kdv2 source. -/
def nativeKdV2DirichletFrequency
    (q : physicalRealMeanZeroWeightedSubmodule (Weight.sobolev ((2 : ℕ) : ℝ)))
    (N : ℕ) (n : ℕ+) : ℂ :=
  let p := nativeHillPhysicalSource 2 q.val q.property.1
  ∑ j ∈ Finset.range N,
    hillAbelianSelectedGlobalPsi p.val p.property.1 p.property.2 n n.pos
      (hillDirichletEnergy p.val p.property.1 p.property.2 (j+1) (by omega))*
        kdv2DirichletVelocityCoefficient (nativeHillContinuousSource 2 (by decide) q.val) p (j+1)

/-- At every actual native finite-gap source, the intrinsic physical Kdv2
frequency equals the actual spectral Dirichlet sum at EVERY open own mode. -/
theorem native_finiteGap_kdv2_frequency_eq_dirichlet (D : GlobalRoughAbelianForwardData)
    (q : physicalRealMeanZeroWeightedSubmodule (Weight.sobolev ((2 : ℕ) : ℝ))) (S : Finset ℕ+)
    (hq : ∀ n : ℕ+, n ∉ S → hillRealGapHalfLength
      (nativeHillPhysicalSource 2 q.val q.property.1).val
      (nativeHillPhysicalSource 2 q.val q.property.1).property.1
      (nativeHillPhysicalSource 2 q.val q.property.1).property.2 n=0)
    (N : ℕ) (hSN : ∀ k ∈ S, (k : ℕ)≤N) (n : ℕ+)
    (hopen : hillRealGapHalfLength (nativeHillPhysicalSource 2 q.val q.property.1).val
      (nativeHillPhysicalSource 2 q.val q.property.1).property.1
      (nativeHillPhysicalSource 2 q.val q.property.1).property.2 n≠0) :
    (D.nativeSourceHierarchyFrequency 2 5 (by norm_num) q n : ℂ) = nativeKdV2DirichletFrequency q N n := by
  classical
  let Q := nativeHillContinuousSource 2 (by decide) q.val
  let p := nativeHillPhysicalSource 2 q.val q.property.1
  have hf := nativeHillContinuousSource_finiteGap_smooth 2 (by decide) q S hq
  have hp := nativeHillContinuousSource_periodic 2 (by decide) q.val
  have hr := nativeHillContinuousSource_real 2 (by decide) q.val q.property.1
  let pQ : RealPeriodOneHillPotential := ⟨hillContinuousCoefficients Q,
    hillContinuousCoefficients_mem_even Q hp,isRealHillPotential_hillContinuousCoefficients Q hr⟩
  have heq : pQ=p := Subtype.ext (hillContinuousCoefficients_nativeHillContinuousSource 2 (by decide) q.val q.property.1)
  have h0q : SpectralWeight.one.toCoeff (0 : WeightedCoeff SpectralWeight.one.toWeight 2)∈Coeff.paritySubspace 0 := by
    rw [map_zero]
    exact (Coeff.paritySubspace 0).zero_mem
  have h0r : IsRealHillPotential (SpectralWeight.one.toCoeff (0 : WeightedCoeff SpectralWeight.one.toWeight 2)) := by
    rw [map_zero]
    intro k
    simp
  obtain ⟨G,hG,_hG0,_hDZ,hmatch⟩ := exists_hillDirichletAbelianCoordinate_analytic_extension
    p.val p.property.1 p.property.2 h0q h0r n n.pos
  have hs := fderiv_hillDirichletAbelianCoordinate_finite_gap_both_pde Q hf hp hr n n.pos
  have hc : ∀ (k : ℕ) (_hk : 1≤k), N<k → hillRealGapHalfLength p.val p.property.1 p.property.2 k=0 := by
    intro k hk hNk
    apply hq ⟨k,by omega⟩
    intro hmem
    have h := hSN ⟨k,by omega⟩ hmem
    change k≤N at h
    omega
  have hcQ : ∀ (k : ℕ) (_hk : 1≤k), N<k → hillRealGapHalfLength pQ.val pQ.property.1 pQ.property.2 k=0 := by
    simpa only [heq] using hc
  have hGQ : DifferentiableAt ℂ G (SpectralWeight.one.toCoeff pQ.val) := by
    rw [heq]
    exact hG.differentiableAt
  have hmQ : ∀ᶠ a : RealPeriodOneHillPotential in 𝓝 pQ,
      G (SpectralWeight.one.toCoeff a.val)=hillDirichletAbelianCoordinate a.val a.property.1 a.property.2 n n.pos := by
    rw [heq]
    exact hmatch
  have hspec := (hs N hcQ G hGQ hmQ).2
  change (fderiv ℂ G (SpectralWeight.one.toCoeff pQ.val))
      (kdv2FourierDirection (fun x : ℝ => Q (x : AddCircle (2 : ℝ))) hf) =
      (∑ j ∈ Finset.range N, hillAbelianSelectedGlobalPsi pQ.val pQ.property.1 pQ.property.2 n n.pos
        (hillDirichletEnergy pQ.val pQ.property.1 pQ.property.2 (j+1) (by omega))*
          kdv2DirichletVelocityCoefficient Q pQ (j+1))*
            (I*hillDirichletAbelianCoordinate pQ.val pQ.property.1 pQ.property.2 n n.pos) at hspec
  rw [heq] at hspec
  have hcoeff (k : ℤ) : q.val.val k=periodOneCoefficient (fun x : ℝ => Q (x : AddCircle (2 : ℝ))) k :=
    (nativeHillContinuousSource_coefficient 2 (by decide) q.val k).symm
  have hjet := D.native_finiteGap_kdv2_coordinate_jet q S hq _ hf hp hcoeff n G hG hmatch
  have hnS : n ∈ S := by by_contra h; exact hopen (hq n h)
  rw [if_pos hnS] at hjet
  have hz : hillDirichletAbelianCoordinate p.val p.property.1 p.property.2 n n.pos≠0 :=
    fun h => hopen ((hillDirichletAbelianCoordinate_eq_zero_iff p.val p.property.1 p.property.2 h0q h0r n n.pos).mp h)
  have hi : I*hillDirichletAbelianCoordinate p.val p.property.1 p.property.2 n n.pos≠0 := mul_ne_zero I_ne_zero hz
  apply mul_right_cancel₀ hi
  rw [←mul_assoc,←hjet]
  exact hspec

end NLS.Articles.KdVKdV2Frequencies.GlobalRoughAbelianForwardData
