import NLS.KdV.HillIndexedNormingVariations

noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology MeasureTheory
open NLS.ComplexAnalysis NLS.ZakharovShabat
open scoped ENNReal ComplexConjugate Classical

namespace NLS.KdV



/-- The actual physical sheet has an analytic germ whose indexed isospectral velocity
is half discriminant times energy derivative, even at a zero terminal sheet. -/
theorem exists_hillDirichletSheet_indexedDiscriminantSource_variations
    (q : RealPeriodOneHillPotential) (n : ℕ) (hn : 1≤n) :
    ∃ S : Coeff 2 → ℂ, AnalyticAt ℂ S (SpectralWeight.one.toCoeff q.val) ∧
      (∀ᶠ p : RealPeriodOneHillPotential in 𝓝 q,
        S (SpectralWeight.one.toCoeff p.val)=hillDirichletSheetRoot (SpectralWeight.one.toCoeff p.val)
          (hillDirichletEnergy p.val p.property.1 p.property.2 n hn)) ∧
      ∀ k : ℕ, ∀ hk : 1≤k,
        (fderiv ℂ S (SpectralWeight.one.toCoeff q.val))
          (SpectralWeight.one.toCoeff (hillIndexedDiscriminantHamiltonianSource q k hk))=
          if n=k then hillL2Discriminant (SpectralWeight.one.toCoeff q.val)
              (hillDirichletEnergy q.val q.property.1 q.property.2 n hn)*
            deriv (hillL2Discriminant (SpectralWeight.one.toCoeff q.val))
              (hillDirichletEnergy q.val q.property.1 q.property.2 n hn)/2 else 0 := by
  obtain ⟨F,hF,hFreal,hFD⟩ := exists_hillLogNorming_indexedDiscriminantSource_variations q n hn
  let S : Coeff 2 → ℂ := fun p => (-1 : ℂ)^n*2*Complex.sinh (F p)
  have hS : AnalyticAt ℂ S (SpectralWeight.one.toCoeff q.val) :=
    analyticAt_const.mul ((Complex.analyticAt_sinh).comp hF)
  have hmatch : ∀ᶠ p : RealPeriodOneHillPotential in 𝓝 q,
      S (SpectralWeight.one.toCoeff p.val)=hillDirichletSheetRoot (SpectralWeight.one.toCoeff p.val)
        (hillDirichletEnergy p.val p.property.1 p.property.2 n hn) := by
    filter_upwards [hFreal] with p hp
    dsimp only [S]
    rw [hp,hillDirichletSheetRoot_at_dirichlet_eq_norming p.val p.property.1 p.property.2 n hn]
    simp only [ofReal_mul,ofReal_pow,ofReal_neg,ofReal_one,ofReal_ofNat,ofReal_sinh]
  let Δ := hillL2Discriminant (SpectralWeight.one.toCoeff q.val)
    (hillDirichletEnergy q.val q.property.1 q.property.2 n hn)
  have hΔ : (Δ.re : ℂ)=Δ := by
    apply Complex.ext
    · rfl
    · exact (hillL2Discriminant_real _ q.property.2 _).symm
  have hcosh := congrArg Complex.ofReal (hillDirichletLogMultiplier_cosh q.val q.property.1 q.property.2 n hn)
  rw [ofReal_div,ofReal_mul,ofReal_pow,ofReal_neg,ofReal_one,ofReal_ofNat] at hcosh
  change (Real.cosh (hillDirichletLogMultiplier q.val q.property.1 q.property.2 n hn) : ℂ)=(-1 : ℂ)^n*(Δ.re : ℂ)/2 at hcosh
  rw [hΔ] at hcosh
  have hsign : ((-1 : ℂ)^n)^2=1 := by
    rw [←pow_mul,Nat.mul_comm n 2,pow_mul]
    norm_num
  have hc : (-1 : ℂ)^n*2*Complex.cosh (F (SpectralWeight.one.toCoeff q.val))=Δ := by
    rw [hFreal.self_of_nhds,←ofReal_cosh,hcosh]
    calc
      _ = ((-1 : ℂ)^n)^2*Δ := by ring
      _ = Δ := by rw [hsign,one_mul]
  refine ⟨S,hS,hmatch,?_⟩
  intro k hk
  have hd := hF.differentiableAt.hasFDerivAt.csinh.const_mul ((-1 : ℂ)^n*2)
  change HasFDerivAt S _ (SpectralWeight.one.toCoeff q.val) at hd
  rw [hd.fderiv]
  simp only [smul_apply,smul_eq_mul]
  rw [hFD k hk]
  by_cases hnk : n=k
  · simp only [if_pos hnk]
    calc
      _ = ((-1 : ℂ)^n*2*Complex.cosh (F (SpectralWeight.one.toCoeff q.val)))*
          (deriv (hillL2Discriminant (SpectralWeight.one.toCoeff q.val))
            (hillDirichletEnergy q.val q.property.1 q.property.2 n hn)/2) := by ring
      _ = _ := by rw [hc];dsimp only [Δ];ring
  · simp only [if_neg hnk,mul_zero]

/-- Physical matching fixes the actual terminal-sheet velocity intrinsically. -/
theorem hillDirichletSheetGerm_indexedDiscriminantSource_fderiv
    (q : RealPeriodOneHillPotential) (n : ℕ) (hn : 1≤n)
    (G : Coeff 2 → ℂ) (hG : AnalyticAt ℂ G (SpectralWeight.one.toCoeff q.val))
    (hGreal : ∀ᶠ p : RealPeriodOneHillPotential in 𝓝 q,
      G (SpectralWeight.one.toCoeff p.val)=hillDirichletSheetRoot (SpectralWeight.one.toCoeff p.val)
        (hillDirichletEnergy p.val p.property.1 p.property.2 n hn))
    (k : ℕ) (hk : 1≤k) :
    (fderiv ℂ G (SpectralWeight.one.toCoeff q.val))
      (SpectralWeight.one.toCoeff (hillIndexedDiscriminantHamiltonianSource q k hk))=
      if n=k then hillL2Discriminant (SpectralWeight.one.toCoeff q.val)
          (hillDirichletEnergy q.val q.property.1 q.property.2 n hn)*
        deriv (hillL2Discriminant (SpectralWeight.one.toCoeff q.val))
          (hillDirichletEnergy q.val q.property.1 q.property.2 n hn)/2 else 0 := by
  obtain ⟨S,hS,hSreal,hSD⟩ := exists_hillDirichletSheet_indexedDiscriminantSource_variations q n hn
  have heq : ∀ᶠ p : RealPeriodOneHillPotential in 𝓝 q,
      G (SpectralWeight.one.toCoeff p.val)=S (SpectralWeight.one.toCoeff p.val) := by
    filter_upwards [hGreal,hSreal] with p hpG hpS
    exact hpG.trans hpS.symm
  exact (hillPhysicalCoefficientGerm_fderiv_eq_of_eventuallyEq q.val q.property.1 q.property.2 G S hG hS heq
    (hillIndexedDiscriminantHamiltonianSource q k hk) (hillEnergyHamiltonianSource_mem_even _ _)).trans (hSD k hk)

end NLS.KdV
