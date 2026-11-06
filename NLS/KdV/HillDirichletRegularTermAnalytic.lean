import NLS.KdV.HillSelectedDirichletAngle
import NLS.KdV.HillDirichletAbelianIntegralAnalytic
import NLS.KdV.HillClosedGapAbelianCorrections

/-! # Analytic regular Abelian terms through every closed Dirichlet gap

The globally specified term is locally represented by an actual complex
analytic functional of the original L² Hill potential. Closed gaps use
the quadratic correction; open gaps use an analytic sheeted terminal.
-/
noncomputable section
open Set Complex Filter Topology
open NLS.ComplexAnalysis NLS.ZakharovShabat
namespace NLS.KdV

theorem exists_hillDirichletRegularAbelianTerm_analytic_extension
    (q : RealPeriodOneHillPotential) (n : ℕ) (hn : 1 ≤ n) (k : ℕ) (hk : 1 ≤ k) :
    ∃ β : Coeff 2 → ℂ, AnalyticAt ℂ β (SpectralWeight.one.toCoeff q.val) ∧
      β (SpectralWeight.one.toCoeff q.val) = hillDirichletRegularAbelianTerm q n hn k hk ∧
      ∀ᶠ p : RealPeriodOneHillPotential in 𝓝 q,
        β (SpectralWeight.one.toCoeff p.val) = hillDirichletRegularAbelianTerm p n hn k hk := by
  have h0q : SpectralWeight.one.toCoeff (0 : WeightedCoeff SpectralWeight.one.toWeight 2) ∈
      Coeff.paritySubspace 0 := by rw [map_zero];exact (Coeff.paritySubspace 0).zero_mem
  have h0r : IsRealHillPotential (SpectralWeight.one.toCoeff (0 : WeightedCoeff SpectralWeight.one.toWeight 2)) := by
    rw [map_zero]
    intro j
    simp
  by_cases hc : hillRealGapHalfLength q.val q.property.1 q.property.2 k = 0
  · have he : hillRealLabels q.val q.property.1 q.property.2 (2*k-1) =
        hillRealLabels q.val q.property.1 q.property.2 (2*k) := by
      dsimp only [hillRealGapHalfLength] at hc
      linarith
    obtain ⟨β,hβ,hβ0,hmatch⟩ := exists_hillRegularAbelian_analytic_closed_gap_correction
      q.val q.property.1 q.property.2 h0q h0r n k hn hk he
    refine ⟨β,hβ,by rw [hβ0,hillDirichletRegularAbelianTerm_closed q n hn k hk hc],?_⟩
    filter_upwards [hmatch] with p hp
    by_cases hpc : hillRealGapHalfLength p.val p.property.1 p.property.2 k = 0
    · rw [hillDirichletRegularAbelianTerm_closed p n hn k hk hpc]
      exact hp.2.1 hpc
    · have hs := hillSelectedDirichletAngle_spec p k hk hpc
      rw [hillDirichletRegularAbelianTerm_eq_terminal p n hn k hk hpc _ hs.2.1 hs.2.2.2]
      exact hp.2.2 hpc _ hs.2.1 hs.2.2.2
  · obtain ⟨B,ε,e,hB,hε,_,_,hmatch⟩ := exists_hillDirichletAbelianIntegral_analytic_open_gap_extension
      q.val q.property.1 q.property.2 h0q h0r n k hn hk hc
    let β : Coeff 2 → ℂ := fun p => B p-(if k=n then 1 else 0)*(ε p-(Real.pi : ℂ))
    have hβ : AnalyticAt ℂ β (SpectralWeight.one.toCoeff q.val) :=
      hB.sub (analyticAt_const.mul (hε.sub analyticAt_const))
    have hm : ∀ᶠ p : RealPeriodOneHillPotential in 𝓝 q,
        β (SpectralWeight.one.toCoeff p.val) = hillDirichletRegularAbelianTerm p n hn k hk := by
      filter_upwards [hmatch] with p hp
      let z := ε (SpectralWeight.one.toCoeff p.val)
      have hre : z = (z.re : ℂ) := by
        apply Complex.ext
        · rfl
        · exact hp.2.1
      have hpoint := hp.2.2.1
      have hsin := hp.2.2.2.1
      change cosineGapPoint _ _ z = _ at hpoint
      change sin z = _ at hsin
      rw [hre] at hpoint hsin
      rw [hillDirichletRegularAbelianTerm_eq_terminal p n hn k hk hp.1 z.re hpoint hsin]
      dsimp only [β,hillRegularAbelianPrimitive]
      rw [hp.2.2.2.2.1]
      change hillAbelianCosinePrimitive p.val p.property.1 p.property.2 n hn k z-
        (if k=n then 1 else 0)*(z-(Real.pi : ℂ)) = _
      rw [hre]
      simp only [ofReal_re]
    exact ⟨β,hβ,Filter.EventuallyEq.eq_of_nhds hm,hm⟩

end NLS.KdV
