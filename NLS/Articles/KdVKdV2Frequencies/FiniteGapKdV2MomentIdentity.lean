import NLS.KdV.HillIntrinsicOddFrequencyPeriods
import NLS.Articles.KdVKdV2Frequencies.FiniteGapQuinticVelocityContours

/-! # The actual finite-gap KdV2 velocity and source mass-renormalized moments

The finite-hole deformation uses the actual Hill spectrum, canonical
normalized numerator, primitive and root. The Hamiltonian frequency/action
realization remains separate from this physical coordinate coefficient.
-/
noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology
open NLS.ComplexAnalysis NLS.ZakharovShabat NLS.KdV
open scoped ContDiff
namespace NLS.Articles.KdVKdV2Frequencies

/-- The source coefficients -160*pi² and 80, leading fifth power and mass correction for the actual physical
KdV Dirichlet velocity sum, including a closed selected gap. -/
theorem kdv2DirichletVelocitySum_eq_intrinsicMoment_finite_sum
    (Q : C(AddCircle (2:ℝ),ℂ))
    (hreal : ∀ x : AddCircle (2:ℝ), (Q x).im=0)
    (hf : ContDiff ℝ ∞ (fun x : ℝ => Q (x : AddCircle (2:ℝ))))
    (hp : Function.Periodic (fun x : ℝ => Q (x : AddCircle (2:ℝ))) 1)
    (hmean : (∫ x in (0:ℝ)..1, Q (x : AddCircle (2:ℝ)))=0)
    (n : ℕ) (hn : 1≤n) :
    let q : RealPeriodOneHillPotential := ⟨hillContinuousCoefficients Q,
      hillContinuousCoefficients_mem_even Q hp,isRealHillPotential_hillContinuousCoefficients Q hreal⟩
    ∀ N : ℕ, n≤N →
      (∀ (k : ℕ) (_hk : 1≤k), N<k → hillRealGapHalfLength q.val q.property.1 q.property.2 k=0) →
    kdv2DirichletVelocitySum Q q n hn N-
      20*(2*(n:ℂ)*Real.pi)*classicalQuadraticInvariant (fun x : ℝ => Q (x : AddCircle (2:ℝ)))-
      (2*(n:ℂ)*Real.pi)^5=
      -160*(Real.pi:ℂ)^2*(∑ k∈Finset.Icc 1 N, (k:ℂ)^3*hillIntrinsicFrequencyMoment q.val q.property.1 q.property.2 n hn k 2)+
      80*(∑ k∈Finset.Icc 1 N, (k:ℂ)*hillIntrinsicFrequencyMoment q.val q.property.1 q.property.2 n hn k 4) := by
  dsimp only
  intro N hnN hclosed
  let q : RealPeriodOneHillPotential := ⟨hillContinuousCoefficients Q,
    hillContinuousCoefficients_mem_even Q hp,isRealHillPotential_hillContinuousCoefficients Q hreal⟩
  obtain ⟨R₀,_hR₀,hvelocity⟩ := exists_kdv2DirichletVelocity_quintic_contour_identity Q hreal hf hp hmean n hn N hnN hclosed
  obtain ⟨R₁,_hR₁,hmoments⟩ := exists_hillFiniteGap_fifth_frequency_moments q.val q.property.1 q.property.2 n N hn hnN hclosed
  let S := max R₀ R₁+1
  have hS₀ : R₀<S := by dsimp only [S];linarith [le_max_left R₀ R₁]
  have hS₁ : R₁<S := by dsimp only [S];linarith [le_max_right R₀ R₁]
  have he := hmoments S hS₁
  have hv := (hvelocity S hS₀).2
  change kdv2DirichletVelocitySum Q q n hn N-
    20*(2*(n:ℂ)*Real.pi)*classicalQuadraticInvariant (fun x : ℝ => Q (x : AddCircle (2:ℝ)))=
    (-16/(I*Real.pi) : ℂ)*(∮ E in C(0,S),
      hillL2OddKernel q.val 2 (hillAbelianSelectedGlobalPsi q.val q.property.1 q.property.2 n hn) E) at hv
  rw [← hv] at he
  exact he

/-- The literal countable source sum is genuine: its weighted zeroth
index is zero and its positive tail vanishes at the actual closed gaps. -/
theorem kdv2DirichletVelocitySum_eq_intrinsicMoment_tsum
    (Q : C(AddCircle (2:ℝ),ℂ))
    (hreal : ∀ x : AddCircle (2:ℝ), (Q x).im=0)
    (hf : ContDiff ℝ ∞ (fun x : ℝ => Q (x : AddCircle (2:ℝ))))
    (hp : Function.Periodic (fun x : ℝ => Q (x : AddCircle (2:ℝ))) 1)
    (hmean : (∫ x in (0:ℝ)..1, Q (x : AddCircle (2:ℝ)))=0)
    (n : ℕ) (hn : 1≤n) :
    let q : RealPeriodOneHillPotential := ⟨hillContinuousCoefficients Q,
      hillContinuousCoefficients_mem_even Q hp,isRealHillPotential_hillContinuousCoefficients Q hreal⟩
    ∀ N : ℕ, n≤N →
      (∀ (k : ℕ) (_hk : 1≤k), N<k → hillRealGapHalfLength q.val q.property.1 q.property.2 k=0) →
    kdv2DirichletVelocitySum Q q n hn N-
      20*(2*(n:ℂ)*Real.pi)*classicalQuadraticInvariant (fun x : ℝ => Q (x : AddCircle (2:ℝ)))-
      (2*(n:ℂ)*Real.pi)^5=
      -160*(Real.pi:ℂ)^2*(∑' k : ℕ, (k:ℂ)^3*hillIntrinsicFrequencyMoment q.val q.property.1 q.property.2 n hn k 2)+
      80*(∑' k : ℕ, (k:ℂ)*hillIntrinsicFrequencyMoment q.val q.property.1 q.property.2 n hn k 4) := by
  dsimp only
  intro N hnN hclosed
  let q : RealPeriodOneHillPotential := ⟨hillContinuousCoefficients Q,
    hillContinuousCoefficients_mem_even Q hp,isRealHillPotential_hillContinuousCoefficients Q hreal⟩
  have he := kdv2DirichletVelocitySum_eq_intrinsicMoment_finite_sum Q hreal hf hp hmean n hn N hnN hclosed
  have ht2 : (∑' k : ℕ, (k:ℂ)^3*hillIntrinsicFrequencyMoment q.val q.property.1 q.property.2 n hn k 2)=
      ∑ k∈Finset.Icc 1 N, (k:ℂ)^3*hillIntrinsicFrequencyMoment q.val q.property.1 q.property.2 n hn k 2 :=
    (hasSum_hillIntrinsicFrequencyMoment_closed_tail q.val q.property.1 q.property.2 n hn N hclosed
      (fun k => (k:ℂ)^3) (by norm_num) 1).tsum_eq
  have ht4 : (∑' k : ℕ, (k:ℂ)*hillIntrinsicFrequencyMoment q.val q.property.1 q.property.2 n hn k 4)=
      ∑ k∈Finset.Icc 1 N, (k:ℂ)*hillIntrinsicFrequencyMoment q.val q.property.1 q.property.2 n hn k 4 :=
    (hasSum_hillIntrinsicFrequencyMoment_closed_tail q.val q.property.1 q.property.2 n hn N hclosed
      (fun k => (k:ℂ)) (by norm_num) 3).tsum_eq
  rw [← ht2,← ht4] at he
  exact he

/-- The literal physical KdV coordinate derivative has the source
fourth/second-moment and mass correction. This holds for every matching scalar germ,
including when the selected coordinate is zero at a closed own gap. -/
theorem fderiv_hillDirichletAbelianCoordinate_kdv2_intrinsicMoment_tsum
    (Q : C(AddCircle (2:ℝ),ℂ))
    (hreal : ∀ x : AddCircle (2:ℝ), (Q x).im=0)
    (hf : ContDiff ℝ ∞ (fun x : ℝ => Q (x : AddCircle (2:ℝ))))
    (hp : Function.Periodic (fun x : ℝ => Q (x : AddCircle (2:ℝ))) 1)
    (hmean : (∫ x in (0:ℝ)..1, Q (x : AddCircle (2:ℝ)))=0)
    (n : ℕ) (hn : 1≤n) :
    let q : RealPeriodOneHillPotential := ⟨hillContinuousCoefficients Q,
      hillContinuousCoefficients_mem_even Q hp,isRealHillPotential_hillContinuousCoefficients Q hreal⟩
    ∀ N : ℕ, n≤N →
      (∀ (k : ℕ) (_hk : 1≤k), N<k → hillRealGapHalfLength q.val q.property.1 q.property.2 k=0) →
    ∀ (C : Coeff 2 → ℂ) (_hC : DifferentiableAt ℂ C (SpectralWeight.one.toCoeff q.val)),
      (∀ᶠ p : RealPeriodOneHillPotential in 𝓝 q,
        C (SpectralWeight.one.toCoeff p.val)=hillDirichletAbelianCoordinate p.val p.property.1 p.property.2 n hn) →
      (fderiv ℂ C (SpectralWeight.one.toCoeff q.val))
        (kdv2FourierDirection (fun x : ℝ => Q (x : AddCircle (2:ℝ))) hf)=
        ((2*(n:ℂ)*Real.pi)^5+
          20*(2*(n:ℂ)*Real.pi)*classicalQuadraticInvariant (fun x : ℝ => Q (x : AddCircle (2:ℝ)))-
          160*(Real.pi:ℂ)^2*(∑' k : ℕ, (k:ℂ)^3*hillIntrinsicFrequencyMoment q.val q.property.1 q.property.2 n hn k 2)+
          80*(∑' k : ℕ, (k:ℂ)*hillIntrinsicFrequencyMoment q.val q.property.1 q.property.2 n hn k 4))*
            (I*hillDirichletAbelianCoordinate q.val q.property.1 q.property.2 n hn) := by
  dsimp only
  intro N hnN hclosed C hC hmatch
  let q : RealPeriodOneHillPotential := ⟨hillContinuousCoefficients Q,
    hillContinuousCoefficients_mem_even Q hp,isRealHillPotential_hillContinuousCoefficients Q hreal⟩
  have hjet := (fderiv_hillDirichletAbelianCoordinate_finite_gap_both_pde Q hf hp hreal n hn
    N hclosed C hC hmatch).2
  change (fderiv ℂ C (SpectralWeight.one.toCoeff q.val)) (kdv2FourierDirection _ hf)=
    kdv2DirichletVelocitySum Q q n hn N*(I*hillDirichletAbelianCoordinate q.val q.property.1 q.property.2 n hn) at hjet
  have he := kdv2DirichletVelocitySum_eq_intrinsicMoment_tsum Q hreal hf hp hmean n hn N hnN hclosed
  have hV : kdv2DirichletVelocitySum Q q n hn N=(2*(n:ℂ)*Real.pi)^5+
          20*(2*(n:ℂ)*Real.pi)*classicalQuadraticInvariant (fun x : ℝ => Q (x : AddCircle (2:ℝ)))-
          160*(Real.pi:ℂ)^2*(∑' k : ℕ, (k:ℂ)^3*hillIntrinsicFrequencyMoment q.val q.property.1 q.property.2 n hn k 2)+
          80*(∑' k : ℕ, (k:ℂ)*hillIntrinsicFrequencyMoment q.val q.property.1 q.property.2 n hn k 4) := by linear_combination he
  rw [hV] at hjet
  exact hjet

end NLS.Articles.KdVKdV2Frequencies
