import NLS.KdV.HillFreeAbelianDifferential
import NLS.KdV.HillAbelianCoordinateContinuity
/-! # Actual signed scalar Fourier differentials in the source period-one coefficients -/
noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology
open NLS.ComplexAnalysis NLS.ZakharovShabat NLS.KdV
open scoped ComplexConjugate
namespace NLS.Articles.KdVKdV2Frequencies

private theorem free_parity : SpectralWeight.one.toCoeff (0 : WeightedCoeff SpectralWeight.one.toWeight 2)∈Coeff.paritySubspace 0 := by
  rw [map_zero]
  exact (Coeff.paritySubspace 0).zero_mem

private theorem free_real : IsRealHillPotential (SpectralWeight.one.toCoeff (0 : WeightedCoeff SpectralWeight.one.toWeight 2)) := by
  rw [map_zero]
  intro k
  simp

private theorem periodOne_scalar_germ (k : ℤ) (c : ℂ) (g : RealPeriodOneHillPotential → ℂ)
    (Z : Coeff 2 → ℂ) (hZ : AnalyticAt ℂ Z 0) (hZ0 : Z 0=0)
    (hDZ : ∀ h : Coeff 2, h∈Coeff.paritySubspace 0 → h 0=0 → (fderiv ℂ Z 0) h=c*h (2*k))
    (hmatch : ∀ᶠ p : RealPeriodOneHillPotential in 𝓝 (⟨0,free_parity,free_real⟩ : RealPeriodOneHillPotential),
      Z (SpectralWeight.one.toCoeff p.val)=g p)
    (hg : ∀ p : RealHillWeightedPotential SpectralWeight.one,
      g (hillRealWeightedEmbedding SpectralWeight.one p)=(hillPhysicalAbelianMap SpectralWeight.one p).val k) :
    ∃ W : Coeff 2 → ℂ, AnalyticAt ℂ W 0 ∧ W 0=0 ∧
      (∀ h : Coeff 2, h 0=0 → (fderiv ℂ W 0) h=c*h k) ∧
      ∀ᶠ p : RealHillWeightedPotential SpectralWeight.one in 𝓝
        (⟨0,by intro j;simp⟩ : RealHillWeightedPotential SpectralWeight.one),
        W (SpectralWeight.one.doubleIndex.toCoeff p.val)=(hillPhysicalAbelianMap SpectralWeight.one p).val k := by
  let D : Coeff 2 →L[ℂ] Coeff 2 := Coeff.periodDouble.toContinuousLinearMap
  let W : Coeff 2 → ℂ := fun a => Z (D a)
  have hZa : AnalyticAt ℂ Z (D 0) := by simpa only [map_zero] using hZ
  have hW : AnalyticAt ℂ W 0 := hZa.comp (D.analyticAt 0)
  have hcoeff (p : RealHillWeightedPotential SpectralWeight.one) :
      SpectralWeight.one.toCoeff (hillRealWeightedEmbedding SpectralWeight.one p).val=
        D (SpectralWeight.one.doubleIndex.toCoeff p.val) := by
    dsimp only [hillRealWeightedEmbedding,D]
    rw [toCoeff_hillPeriodOneUnitPotential,toCoeff_hillPeriodOnePotential]
    rfl
  let p0 : RealHillWeightedPotential SpectralWeight.one := ⟨0,by intro j;simp⟩
  have hEmb0 : hillRealWeightedEmbedding SpectralWeight.one p0=
      (⟨0,free_parity,free_real⟩ : RealPeriodOneHillPotential) := by
    apply Subtype.ext
    simp only [hillRealWeightedEmbedding,p0,hillPeriodOneUnitPotential,map_zero]
  have hEmb : Tendsto (hillRealWeightedEmbedding SpectralWeight.one) (𝓝 p0)
      (𝓝 (⟨0,free_parity,free_real⟩ : RealPeriodOneHillPotential)) := by
    rw [← hEmb0]
    exact (continuous_hillRealWeightedEmbedding SpectralWeight.one).tendsto p0
  refine ⟨W,hW,by simp only [W,map_zero,hZ0],?_,?_⟩
  · intro h hm
    have hd := hZa.differentiableAt.hasFDerivAt.comp (0:Coeff 2) D.hasFDerivAt
    have he := congrArg (fun L : Coeff 2 →L[ℂ] ℂ => L h) hd.fderiv
    simp only [map_zero] at he
    change (fderiv ℂ W 0) h=(fderiv ℂ Z 0) (Coeff.periodDouble h) at he
    rw [hDZ _ (Coeff.periodDouble_mem h) (by simpa only [mul_zero,hm] using Coeff.periodDouble_even h (0:ℤ)),Coeff.periodDouble_even] at he
    exact he
  · filter_upwards [hEmb.eventually hmatch] with p hp
    dsimp only [W]
    rw [← hcoeff p,hp,hg]

/-- Every signed component of the actual physical map has a genuine
complex L2 germ with the source's normalized Fourier differential.
This is a scalar statement; native sequence-valued analyticity remains separate. -/
theorem exists_hillPhysicalAbelianMap_scalar_fourier_differential (k : ℤ) :
    ∃ W : Coeff 2 → ℂ, AnalyticAt ℂ W 0 ∧ W 0=0 ∧
      (∀ h : Coeff 2, h 0=0 → (fderiv ℂ W 0) h=
        (Real.sqrt (2*(k.natAbs:ℝ)*Real.pi):ℂ)⁻¹*h k) ∧
      ∀ᶠ p : RealHillWeightedPotential SpectralWeight.one in 𝓝
        (⟨0,by intro j;simp⟩ : RealHillWeightedPotential SpectralWeight.one),
        W (SpectralWeight.one.doubleIndex.toCoeff p.val)=(hillPhysicalAbelianMap SpectralWeight.one p).val k := by
  cases k with
  | ofNat n =>
    by_cases hn : n=0
    · subst n
      refine ⟨fun _ => 0,analyticAt_const,rfl,?_,?_⟩
      · intro h _hm
        simp
      · exact Eventually.of_forall (fun p => (hillPhysicalAbelianMap_real SpectralWeight.one p).1.symm)
    · have hn1 : 1≤n := by omega
      obtain ⟨Z,hZ,hZ0,hDZ,hmatch⟩ := exists_hillDirichletAbelianCoordinate_free_differential free_parity free_real n hn1
      apply periodOne_scalar_germ (n:ℤ) _
        (fun p => hillDirichletAbelianCoordinate p.val p.property.1 p.property.2 n hn1) Z hZ hZ0 hDZ hmatch
      intro p
      simp only [hillPhysicalAbelianMap,hillAbelianCoordinateSequence_apply,hillAbelianRawCoordinateSequence,
        Int.natCast_nonneg,if_true,Int.natAbs_natCast,hillAbelianPositiveCoefficient,dif_pos hn1]
  | negSucc n =>
    have hn1 : 1≤n+1 := by omega
    obtain ⟨Z,hZ,hZ0,hDZ,hmatch⟩ := exists_hillNegativeAbelianCoordinate_free_differential free_parity free_real (n+1) hn1
    have hk : Int.negSucc n= -((n+1:ℕ):ℤ) := by omega
    rw [hk]
    simp only [Int.natAbs_neg,Int.natAbs_natCast]
    apply periodOne_scalar_germ (-((n+1:ℕ):ℤ)) _
      (fun p => conj (hillDirichletAbelianCoordinate p.val p.property.1 p.property.2 (n+1) hn1)) Z hZ hZ0 hDZ hmatch
    intro p
    simp only [hillPhysicalAbelianMap,hillAbelianCoordinateSequence_apply,hillAbelianRawCoordinateSequence,
      show ¬0≤-((n+1:ℕ):ℤ) by omega,if_false,Int.natAbs_neg,Int.natAbs_natCast,
      hillAbelianPositiveCoefficient,dif_pos hn1]
end NLS.Articles.KdVKdV2Frequencies
