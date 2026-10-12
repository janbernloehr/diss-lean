import NLS.ZakharovShabat.L2SourceDirichletGradient
import NLS.ZakharovShabat.SourceDirichletComplexFourierGradient

/-! # Actual source Fourier values of normalized physical L2 eigenfunctions -/
noncomputable section
open Set Complex MeasureTheory NLS.LinearVolterra NLS.Fourier
open scoped ENNReal
namespace NLS.ZakharovShabat

theorem continuous_l2DirichletNormalizedGradient (u : IntervalPairL2) (z : ℂ) :
    Continuous (l2DirichletNormalizedGradient u z) := by
  have hy := continuous_extend (l2SolutionCurve u z (1,1))
  exact ((hy.snd.pow 2).div_const _).prodMk ((hy.fst.pow 2).div_const _)

/-- Pairing with a finite Fourier direction depends only on its physical representative. -/
theorem source_physical_gradient_pairing_finite (g : ℝ → ℂ × ℂ)
    (a : (ℤ →₀ ℂ) × (ℤ →₀ ℂ)) :
    (∫ s in (0 : ℝ)..1, (g s).1*(physicalBase (periodOnePotential (CoeffPair.ofFinsupp (p := 2) a)) s).1+
      (g s).2*(physicalBase (periodOnePotential (CoeffPair.ofFinsupp (p := 2) a)) s).2) =
      ∫ s in (0 : ℝ)..1, (g s).1*(extend (finiteSourceCurve a) s).1+
        (g s).2*(extend (finiteSourceCurve a) s).2 := by
  apply intervalIntegral.integral_congr_ae_restrict
  rw [uIoc_of_le (by norm_num : (0 : ℝ) ≤ 1)]
  filter_upwards [(finiteSource_physical_compatibility a).1] with s hs
  rw [hs]

/-- A first-component unit source mode has reversed physical Fourier index. -/
theorem source_physical_gradient_pairing_single_fst (g : ℝ → ℂ × ℂ) (k : ℤ) :
    (∫ s in (0 : ℝ)..1,
      (g s).1*(physicalBase (periodOnePotential (CoeffPair.ofFinsupp (p := 2) (Finsupp.single k 1,0))) s).1+
      (g s).2*(physicalBase (periodOnePotential (CoeffPair.ofFinsupp (p := 2) (Finsupp.single k 1,0))) s).2) =
      unitFourierCoefficient (fun s => (g s).1) (-k) := by
  rw [source_physical_gradient_pairing_finite]
  unfold unitFourierCoefficient
  rw [show -(2*(-k)) = 2*k by ring]
  apply intervalIntegral.integral_congr
  intro s hs
  have hs' : s ∈ Icc (0 : ℝ) 1 := by simpa only [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] using hs
  simp [NLS.LinearVolterra.extend,projIcc_of_mem _ hs',finiteSourceCurve,BoundaryCondition.periodOnePair,polynomial]

/-- The second source component has the same reversed unit-direction index. -/
theorem source_physical_gradient_pairing_single_snd (g : ℝ → ℂ × ℂ) (k : ℤ) :
    (∫ s in (0 : ℝ)..1,
      (g s).1*(physicalBase (periodOnePotential (CoeffPair.ofFinsupp (p := 2) (0,Finsupp.single k 1))) s).1+
      (g s).2*(physicalBase (periodOnePotential (CoeffPair.ofFinsupp (p := 2) (0,Finsupp.single k 1))) s).2) =
      unitFourierCoefficient (fun s => (g s).2) (-k) := by
  rw [source_physical_gradient_pairing_finite]
  unfold unitFourierCoefficient
  rw [show -(2*(-k)) = 2*k by ring]
  apply intervalIntegral.integral_congr
  intro s hs
  have hs' : s ∈ Icc (0 : ℝ) 1 := by simpa only [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] using hs
  simp [NLS.LinearVolterra.extend,projIcc_of_mem _ hs',finiteSourceCurve,BoundaryCondition.periodOnePair,polynomial]

/-- The actual source root cotangent has both normalized L2 Fourier coefficients
on one common complex domain, including all rough Hilbert potentials there. -/
theorem exists_global_source_dirichlet_l2_fourier
    {p : ℝ≥0∞} [Fact (1 ≤ p)] (hp : p ≠ ⊤) (hp1 : 1 < p) (h2p : (2 : ℝ≥0∞) ≤ p) :
    ∃ W : Set (CoeffPair p), IsOpen W ∧ realTypeSourceLocus p ⊆ W ∧
      ∀ φ : CoeffPair 2, CoeffPair.exponentInclusion h2p φ ∈ W → ∀ n : ℤ,
        let z := canonicalPeriodOneBoundaryRoots hp hp1 .dirichlet (CoeffPair.exponentInclusion h2p φ) n
        let L := fderiv ℂ (fun ψ : CoeffPair p => canonicalPeriodOneBoundaryRoots hp hp1 .dirichlet ψ n)
          (CoeffPair.exponentInclusion h2p φ)
        l2DirichletNormalization (sourcePhysicalL2 φ) z ≠ 0 ∧ ∀ k : ℤ,
          L (CoeffPair.inlCLM (lp.single p k 1)) =
            unitFourierCoefficient (fun s => (l2DirichletNormalizedGradient (sourcePhysicalL2 φ) z s).1) (-k) ∧
          L (CoeffPair.inrCLM (lp.single p k 1)) =
            unitFourierCoefficient (fun s => (l2DirichletNormalizedGradient (sourcePhysicalL2 φ) z s).2) (-k) := by
  obtain ⟨W,hW,hreal,hgradient⟩ := exists_global_source_dirichlet_l2_normalized_integral hp hp1 h2p
  refine ⟨W,hW,hreal,?_⟩
  intro φ hφ n
  dsimp only
  obtain ⟨hQ,hint⟩ := hgradient φ hφ n
  refine ⟨hQ,fun k => ?_⟩
  constructor
  · have hdir : CoeffPair.inlCLM (lp.single p k (1 : ℂ)) =
        CoeffPair.exponentInclusion h2p (CoeffPair.ofFinsupp (p := 2) (Finsupp.single k 1,0)) := by
      rw [CoeffPair.exponentInclusion_ofFinsupp]
      apply (CoeffPair.toMax p).injective
      apply Prod.ext <;> ext m <;> simp [lp.single_apply,Pi.single_apply,Finsupp.single_apply,eq_comm]
    rw [hdir,hint]
    exact source_physical_gradient_pairing_single_fst _ k
  · have hdir : CoeffPair.inrCLM (lp.single p k (1 : ℂ)) =
        CoeffPair.exponentInclusion h2p (CoeffPair.ofFinsupp (p := 2) (0,Finsupp.single k 1)) := by
      rw [CoeffPair.exponentInclusion_ofFinsupp]
      apply (CoeffPair.toMax p).injective
      apply Prod.ext <;> ext m <;> simp [lp.single_apply,Pi.single_apply,Finsupp.single_apply,eq_comm]
    rw [hdir,hint]
    exact source_physical_gradient_pairing_single_snd _ k

end NLS.ZakharovShabat
