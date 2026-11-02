import NLS.KdV.HillSobolev
import NLS.Fourier.PhysicalConvolution
import NLS.Fourier.SobolevDistributionDerivative
import NLS.Fourier.SobolevIdentification

/-!
# Physical realization of the periodic Hill operator

The coefficient H2 domain has a continuous periodic representative. Its
second distributional derivative is exactly the negative free Hill symbol,
and the potential term is actual L2 multiplication by that representative.
This identifies the constructed operator with `-d²/dx²+q` in the weak H2
sense. Spectral compactness, self-adjointness and multiplicity statements
are not inferred from this realization.
-/

noncomputable section
open MeasureTheory
open scoped ENNReal SchwartzMap
namespace NLS.KdV

/-- The continuous period-two representative of domain data. -/
def hillRepresentative : HillSobolevDomain →L[ℂ] C(AddCircle (2 : ℝ), ℂ) :=
  (Fourier.sobolevSynthesis (by simp)).comp hillDomainToH1

@[simp] theorem hillRepresentative_coefficient (f : HillSobolevDomain) (k : ℤ) :
    fourierCoeff (hillRepresentative f) k = f.val k := by
  simp [hillRepresentative, hillDomainToH1]

theorem hillRepresentative_periodic (f : HillSobolevDomain) :
    Function.Periodic (fun x : ℝ => hillRepresentative f (x : AddCircle (2 : ℝ))) 2 :=
  Fourier.periodic_sobolevSynthesis (by simp) (hillDomainToH1 f)

theorem hillRepresentative_H1 (f : HillSobolevDomain) :
    Fourier.HasPeriodicH1Regularity (hillRepresentative f) :=
  Fourier.hasPeriodicH1Regularity_sobolevSynthesis (hillDomainToH1 f)

/-- A first derivative in the actual one-derivative Hilbert space. -/
def hillFirstDerivative : HillSobolevDomain →L[ℂ] WeightedCoeff (Weight.sobolev 1) 2 :=
  WeightedCoeff.weightedMultiplierCLM _ _ (fun k => Complex.I*(Real.pi : ℂ)*k)
    Real.pi Real.pi_pos.le (by
      intro k
      simpa only [show (1 : ℝ)+1=2 by norm_num] using Weight.sobolev_derivative_bound 1 k)

@[simp] theorem hillFirstDerivative_apply (f : HillSobolevDomain) (k : ℤ) :
    (hillFirstDerivative f).val k = Complex.I*(Real.pi : ℂ)*k*f.val k := rfl

/-- The first derivative has a continuous periodic H1 representative. -/
def hillDerivativeRepresentative (f : HillSobolevDomain) : C(AddCircle (2 : ℝ), ℂ) :=
  Fourier.sobolevSynthesis (by simp) (hillFirstDerivative f)

theorem hillDerivativeRepresentative_H1 (f : HillSobolevDomain) :
    Fourier.HasPeriodicH1Regularity (hillDerivativeRepresentative f) :=
  Fourier.hasPeriodicH1Regularity_sobolevSynthesis (hillFirstDerivative f)

/-- The continuous derivative representative is the actual first derivative
almost everywhere on a full physical period. -/
theorem hillRepresentative_deriv_ae (f : HillSobolevDomain) :
    deriv (fun x : ℝ => hillRepresentative f (x : AddCircle (2 : ℝ)))
      =ᵐ[volume.restrict (Set.Ioc 0 2)]
        (fun x : ℝ => hillDerivativeRepresentative f (x : AddCircle (2 : ℝ))) := by
  have he : Fourier.sobolevDerivative (hillDomainToH1 f) =
      ContinuousMap.toLp 2 AddCircle.haarAddCircle ℂ (hillDerivativeRepresentative f) := by
    rw [hillDerivativeRepresentative, Fourier.toLp_sobolevSynthesis]
    change Fourier.l2Synthesis (ZakharovShabat.derivative (hillDomainToH1 f)) =
      Fourier.l2Synthesis (ZakharovShabat.scalarInclusion (hillFirstDerivative f))
    congr 1
    ext k
    simp [hillDomainToH1]
  have h := Fourier.deriv_sobolevSynthesis_ae (hillDomainToH1 f)
  rw [he] at h
  exact h.trans (Fourier.circle_ae_pullback
    (ContinuousMap.coeFn_toLp AddCircle.haarAddCircle (hillDerivativeRepresentative f)))

/-- Periodic H2 regularity in physical terms: both the function and a
representative of its first derivative are periodic H1 functions. -/
def HasPeriodicHillH2 (F : C(AddCircle (2 : ℝ), ℂ)) : Prop :=
  ∃ G : C(AddCircle (2 : ℝ), ℂ),
    Fourier.HasPeriodicH1Regularity F ∧ Fourier.HasPeriodicH1Regularity G ∧
      deriv (fun x : ℝ => F (x : AddCircle (2 : ℝ)))
        =ᵐ[volume.restrict (Set.Ioc 0 2)] (fun x : ℝ => G (x : AddCircle (2 : ℝ)))

theorem hillRepresentative_H2 (f : HillSobolevDomain) :
    HasPeriodicHillH2 (hillRepresentative f) :=
  ⟨hillDerivativeRepresentative f, hillRepresentative_H1 f,
    hillDerivativeRepresentative_H1 f, hillRepresentative_deriv_ae f⟩

theorem hillRepresentative_injective : Function.Injective hillRepresentative := by
  intro f g h
  apply Subtype.ext
  funext k
  simpa using congrArg (fun F : C(AddCircle (2 : ℝ), ℂ) => fourierCoeff F k) h

/-- The coefficient domain is exactly physical periodic H2, with unique
representation; it is not merely a sufficient smoothness condition. -/
theorem hasPeriodicHillH2_iff_domain (F : C(AddCircle (2 : ℝ), ℂ)) :
    HasPeriodicHillH2 F ↔ ∃! f : HillSobolevDomain, hillRepresentative f = F := by
  constructor
  · rintro ⟨G, hF, hG, hd⟩
    have hc (k : ℤ) : fourierCoeff G k = Complex.I*(Real.pi : ℂ)*k*fourierCoeff F k := by
      have he := Fourier.periodTwoCoefficient_deriv_sobolevSynthesis
        (Fourier.sobolevCoefficients F hF) k
      simp only [Fourier.sobolevSynthesis_sobolevCoefficients,
        Fourier.sobolevCoefficients_apply] at he
      have hae := congrFun (fourierCoeffOn_congr_ae (by norm_num : (0 : ℝ) < 2) hd) k
      have hae' : Fourier.periodTwoCoefficient
          (deriv (fun x : ℝ => F (x : AddCircle (2 : ℝ)))) k =
          Fourier.periodTwoCoefficient (fun x : ℝ => G (x : AddCircle (2 : ℝ))) k := by
        simpa only [← Fourier.periodTwoCoefficient_eq_fourierCoeffOn] using hae
      rw [hae', Fourier.periodTwoCoefficient_circle] at he
      exact he
    have hs : Memℓp (fun k => (Weight.sobolev 2 k : ℂ)*fourierCoeff F k) 2 := by
      have hmem := WeightedCoeff.memlp_sobolev_succ_of_derivative (p := 2) 1
        (Fourier.memlp_sobolev_fourierCoeff F hF)
        (show Memℓp (fun k => (Weight.sobolev 1 k : ℂ)*
          (Complex.I*(Real.pi : ℂ)*k*fourierCoeff F k)) 2 from by
          simpa only [← hc] using Fourier.memlp_sobolev_fourierCoeff G hG)
      simpa only [show (1 : ℝ)+1=2 by norm_num] using hmem
    let f : HillSobolevDomain := ⟨fourierCoeff F, hs⟩
    have hf : hillRepresentative f = F :=
      (Fourier.eq_sobolevSynthesis_of_fourierCoeff (by simp) (hillDomainToH1 f) F
        (fun k => (WeightedCoeff.sobolevInclusion_apply _ f k).symm)).symm
    exact ⟨f, hf, fun g hg => hillRepresentative_injective (hg.trans hf.symm)⟩
  · rintro ⟨f, rfl, _⟩
    exact hillRepresentative_H2 f

theorem hill_distribution_first_derivative (f : HillSobolevDomain) :
    TemperedDistribution.derivCLM ℂ (Fourier.sobolevDistributionSynthesisCLM 2 f) =
      Fourier.sobolevDistributionSynthesisCLM 1 (hillFirstDerivative f) :=
  (Fourier.sobolevDistributionDerivative_eq_iff 2 1 f (hillFirstDerivative f)).mpr
    (fun _ => rfl)

private def hillLaplacianOrderZero (f : HillSobolevDomain) : WeightedCoeff (Weight.sobolev 0) 2 :=
  (WeightedCoeff.weightIsometry (Weight.sobolev 0) 2).symm (hillLaplacian f)

private theorem hillLaplacianOrderZero_apply (f : HillSobolevDomain) (k : ℤ) :
    (hillLaplacianOrderZero f).val k = (freeHillValue k : ℂ)*f.val k := by
  change hillLaplacian f k / (Weight.sobolev 0 k : ℂ) = _
  simp

private theorem hillLaplacianOrderZero_synthesis (f : HillSobolevDomain) :
    Fourier.sobolevDistributionSynthesisCLM 0 (hillLaplacianOrderZero f) =
      Fourier.distributionSynthesis (hillLaplacian f) := by
  ext g
  simp only [Fourier.sobolevDistributionSynthesisCLM_apply,
    Fourier.distributionSynthesis_apply, hillLaplacianOrderZero_apply, hillLaplacian_apply]

/-- The free second-order term is precisely the second weak derivative,
with the sign fixed by the physical period-two convention. -/
theorem hill_distribution_second_derivative (f : HillSobolevDomain) :
    TemperedDistribution.derivCLM ℂ
      (TemperedDistribution.derivCLM ℂ (Fourier.sobolevDistributionSynthesisCLM 2 f)) =
      -Fourier.distributionSynthesis (hillLaplacian f) := by
  rw [hill_distribution_first_derivative]
  have he : TemperedDistribution.derivCLM ℂ
      (Fourier.sobolevDistributionSynthesisCLM 1 (hillFirstDerivative f)) =
      Fourier.sobolevDistributionSynthesisCLM 0 (-hillLaplacianOrderZero f) := by
    apply (Fourier.sobolevDistributionDerivative_eq_iff 1 0 _ _).mpr
    intro k
    simp only [WeightedCoeff.neg_val, hillLaplacianOrderZero_apply, hillFirstDerivative_apply,
      freeHillValue]
    push_cast
    ring_nf
    simp [Complex.I_sq]
  rw [he, map_neg, hillLaplacianOrderZero_synthesis]

/-- The physical operator has an L2 potential term given by actual multiplication. -/
def physicalHillOperator (q : Fourier.CircleL2) (f : HillSobolevDomain) : Fourier.CircleL2 :=
  Fourier.l2Synthesis (hillLaplacian f) + Fourier.circleMul (hillRepresentative f) q

private theorem hillDerivative_L2 (f : HillSobolevDomain) :
    Fourier.sobolevDerivative (hillFirstDerivative f) =
      -Fourier.l2Synthesis (hillLaplacian f) := by
  change Fourier.l2Synthesis (ZakharovShabat.derivative (hillFirstDerivative f)) = _
  rw [← map_neg]
  congr 1
  ext k
  simp only [ZakharovShabat.derivative_apply, hillFirstDerivative_apply,
    lp.coeFn_neg, Pi.neg_apply, hillLaplacian_apply, freeHillValue]
  push_cast
  ring_nf
  simp [Complex.I_sq]

/-- The actual physical output is `-G' + q*F` almost everywhere, where `G`
is the periodic H1 representative of the first derivative of `F`. -/
theorem physicalHillOperator_pointwise (q : Fourier.CircleL2) (f : HillSobolevDomain) :
    Fourier.circlePullback (physicalHillOperator q f)
      =ᵐ[volume.restrict (Set.Ioc 0 2)] (fun x : ℝ =>
        -deriv (fun y : ℝ => hillDerivativeRepresentative f (y : AddCircle (2 : ℝ))) x +
          Fourier.circlePullback q x * hillRepresentative f (x : AddCircle (2 : ℝ))) := by
  have hd := Fourier.deriv_sobolevSynthesis_ae (hillFirstDerivative f)
  rw [hillDerivative_L2] at hd
  have hn := Fourier.circle_ae_pullback (Lp.coeFn_neg (Fourier.l2Synthesis (hillLaplacian f)))
  have hd' := hd.trans hn
  have ha := Fourier.circle_ae_pullback (Lp.coeFn_add (Fourier.l2Synthesis (hillLaplacian f))
    (Fourier.circleMul (hillRepresentative f) q))
  have hm := Fourier.circlePullback_circleMul (hillRepresentative f) q
  filter_upwards [ha, hm, hd'] with x hx hp hg
  change Fourier.circleMul (hillRepresentative f) q (x : AddCircle (2 : ℝ)) = _ at hp
  change deriv (fun y : ℝ => hillDerivativeRepresentative f (y : AddCircle (2 : ℝ))) x =
    -Fourier.l2Synthesis (hillLaplacian f) (x : AddCircle (2 : ℝ)) at hg
  change (Fourier.l2Synthesis (hillLaplacian f) +
    Fourier.circleMul (hillRepresentative f) q) (x : AddCircle (2 : ℝ)) = _
  rw [hx]
  simp only [Pi.add_apply]
  rw [hp, hg]
  ring

/-- Physical multiplication agrees with the previously constructed coefficient operator. -/
theorem l2Synthesis_hillOperator (q : Coeff 2) (f : HillSobolevDomain) :
    Fourier.l2Synthesis (hillOperator q f) =
      physicalHillOperator (Fourier.l2Synthesis q) f := by
  change Fourier.l2Synthesis (hillLaplacian f + Coeff.convolution q (hillDomainToL1 f)) = _
  rw [map_add, ← Fourier.circleMul_continuousSynthesis]
  rfl

/-- The continuous representative is the same L2 vector as the domain inclusion. -/
theorem hillRepresentative_toLp (f : HillSobolevDomain) :
    ContinuousMap.toLp 2 AddCircle.haarAddCircle ℂ (hillRepresentative f) =
      Fourier.l2Synthesis (hillDomainToL2 f) := by
  rw [hillRepresentative, ContinuousLinearMap.comp_apply, Fourier.toLp_sobolevSynthesis]
  congr 1
  ext k
  simp [hillDomainToH1]

/-- The physical L2 eigen-equation and the coefficient-domain eigen-equation coincide. -/
theorem physicalHillOperator_eigen_iff (q : Coeff 2) (z : ℂ) (f : HillSobolevDomain) :
    physicalHillOperator (Fourier.l2Synthesis q) f =
      z • ContinuousMap.toLp 2 AddCircle.haarAddCircle ℂ (hillRepresentative f) ↔
    hillOperator q f = z • hillDomainToL2 f := by
  rw [hillRepresentative_toLp, ← l2Synthesis_hillOperator, ← map_smul]
  exact Fourier.l2Synthesis.injective.eq_iff

/-- A physical eigenvector satisfies the source differential equation almost
everywhere, with both function and derivative periodic and in H1. -/
theorem physicalHillOperator_eigen_ae (q : Fourier.CircleL2) (z : ℂ)
    (f : HillSobolevDomain)
    (he : physicalHillOperator q f =
      z • ContinuousMap.toLp 2 AddCircle.haarAddCircle ℂ (hillRepresentative f)) :
    (fun x : ℝ =>
      -deriv (fun y : ℝ => hillDerivativeRepresentative f (y : AddCircle (2 : ℝ))) x +
        Fourier.circlePullback q x * hillRepresentative f (x : AddCircle (2 : ℝ)))
      =ᵐ[volume.restrict (Set.Ioc 0 2)]
        (fun x : ℝ => z*hillRepresentative f (x : AddCircle (2 : ℝ))) := by
  have hp := physicalHillOperator_pointwise q f
  rw [he] at hp
  have hs := Fourier.circle_ae_pullback (Lp.coeFn_smul z
    (ContinuousMap.toLp 2 AddCircle.haarAddCircle ℂ (hillRepresentative f)))
  have hc := Fourier.circle_ae_pullback
    (ContinuousMap.coeFn_toLp (p := 2) (𝕜 := ℂ) AddCircle.haarAddCircle (hillRepresentative f))
  filter_upwards [hp, hs, hc] with x hx hz hf
  exact hx.symm.trans (hz.trans (congrArg (fun v : ℂ => z*v) hf))

/-- The reduction determinant now detects the constructed physical H2 Hill eigen-equation. -/
theorem hillReduced_det_eq_zero_iff_physicalEigenvector
    (q : WeightedCoeff SpectralWeight.one.toWeight 2) (n : ℕ) (hn : 1 ≤ n)
    (z : ℂ) (hz : z ∈ reducedHillStrip n) (hcut : 8*‖q‖ ≤ (n : ℝ)) :
    (hillReducedOperator SpectralWeight.one q n hn z hz hcut).toLinearMap.det = 0 ↔
      ∃ f : HillSobolevDomain, f ≠ 0 ∧
        physicalHillOperator (Fourier.l2Synthesis (SpectralWeight.one.toCoeff q)) f =
          z • ContinuousMap.toLp 2 AddCircle.haarAddCircle ℂ (hillRepresentative f) := by
  simp_rw [physicalHillOperator_eigen_iff]
  exact hillReduced_det_eq_zero_iff_domainEigenvector q n hn z hz hcut

end NLS.KdV
