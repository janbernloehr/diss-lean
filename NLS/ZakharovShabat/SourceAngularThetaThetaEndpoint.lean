import NLS.ZakharovShabat.SourceAngularEtaEndpointCotangent
import NLS.ZakharovShabat.SourceBoundaryEndpointCotangents
import NLS.ZakharovShabat.SourceAngularBetaSeriesDifferential

/-! # Actual angle/angle involution at periodic-terminal basepoints

At a source whose Dirichlet terminals are all periodic, each beta
cotangent and each selected eta cotangent is a scalar multiple of a
moving terminal anti-discriminant cotangent. These terminal cotangents
commute. Finite symmetric angle cotangent sums therefore commute, and
the proved operator-norm convergence gives zero for the full actual
angle/angle bracket. No finite-gap, supplied chart, or convergence
hypothesis is required. Transport to general sources remains separate.
-/

noncomputable section
open Set Metric Complex Filter Topology NLS.ComplexAnalysis NLS.Poisson
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The normalized actual psi data construct the charts needed for the
full off-diagonal beta endpoint cotangent reduction at every real source. -/
theorem SourcePsiIsolatingComplexExtension.exists_fderiv_beta_eq_anti_smul_of_eq_zero
    {hp : p ≠ ⊤} {hp1 : 1 < p} {W₀ : Set (CoeffPair p)}
    {s : (j : ℤ) → CoeffPair p → DeletedCoeff p j}
    (hs : SourcePsiIsolatingComplexExtension hp hp1 W₀ s)
    (n m : ℤ) (hmn : m ≠ n) (φ : realTypeSourceLocus p)
    (hzero : sourceBoundaryTerminalAntiDiscriminant hp hp1 .dirichlet m φ.val = 0) :
    ∃ a : ℂ, fderiv ℂ (sourceAngularBeta hp hp1 n m s) φ.val =
      a • fderiv ℂ (sourceBoundaryTerminalAntiDiscriminant hp hp1 .dirichlet m) φ.val := by
  obtain ⟨a,ha,_,_,_,_,hball,_,_,_,_⟩ := hs.isolation φ
  obtain ⟨A,hA,_,hAreal,hMG⟩ := exists_global_source_analytic_midpoint_squaredGap hp hp1
  let O := ball φ.val a ∩ A
  have hO : IsOpen O := isOpen_ball.inter hA
  have hOW₀ : O ⊆ W₀ := fun ψ hψ => hball hψ.1
  have hφO : φ.val ∈ O := ⟨mem_ball_self ha,hAreal φ.property⟩
  obtain ⟨V,c,T,r,R,z₀,hφV,C⟩ := hs.exists_local_joint_angular_annulus_primitives
    O hO hOW₀ (fun ψ hψ => hMG ψ hψ.2) φ.val hφO φ.property m
  let ρ := (r+R)/2
  have hrρ : r < ρ := by dsimp only [ρ]; linarith [C.inner_lt_outer]
  have hρR : ρ < R := by dsimp only [ρ]; linarith [C.inner_lt_outer]
  exact ⟨_,C.fderiv_beta_eq_anti_smul_of_eq_zero n hmn ρ hrρ hρR φ hφV hzero⟩

namespace SourceAngularThetaCommonDomainData
variable {hp : p ≠ ⊤} {hp1 : 1 < p} {W₀ B W : Set (CoeffPair p)}
  {s : (j : ℤ) → CoeffPair p → DeletedCoeff p j}

/-- Every term of the actual beta correction has its endpoint cotangent
in the corresponding moving terminal span; the omitted diagonal is zero. -/
theorem exists_fderiv_betaSeriesTerm_eq_anti_smul_of_eq_zero
    (D : SourceAngularThetaCommonDomainData hp hp1 W₀ B W s)
    (n m : ℤ) (φ : realTypeSourceLocus p)
    (hzero : sourceBoundaryTerminalAntiDiscriminant hp hp1 .dirichlet m φ.val = 0) :
    ∃ a : ℂ, fderiv ℂ (fun ψ => sourceAngularBetaSeriesTerm hp hp1 n s ψ m) φ.val =
      a • fderiv ℂ (sourceBoundaryTerminalAntiDiscriminant hp hp1 .dirichlet m) φ.val := by
  classical
  by_cases hmn : m = n
  · refine ⟨0,?_⟩
    apply ContinuousLinearMap.ext
    intro h
    simp [sourceAngularBetaSeriesTerm,hmn]
  · simpa only [sourceAngularBetaSeriesTerm,if_neg hmn] using
      D.psi.toSourcePsiIsolatingComplexExtension.exists_fderiv_beta_eq_anti_smul_of_eq_zero n m hmn φ hzero

/-- At every actual real basepoint with all Dirichlet terminals periodic,
the full actual angle/angle bracket is zero for finite exponents at least
two and any two open selected angle gaps. All other gaps may be collapsed. -/
theorem thetaThetaBracket_eq_zero_of_all_terminals_periodic
    (D : SourceAngularThetaCommonDomainData hp hp1 W₀ B W s)
    (h2p : (2 : ℝ≥0∞) ≤ p) (n m : ℤ) (φ : realTypeSourceLocus p)
    (hn : canonicalPeriodicGap hp hp1 (periodOnePotential φ.val) (periodOnePotential_mem φ.val) n ≠ 0)
    (hm : canonicalPeriodicGap hp hp1 (periodOnePotential φ.val) (periodOnePotential_mem φ.val) m ≠ 0)
    (hterminal : ∀ j : ℤ, sourceBoundaryTerminalAntiDiscriminant hp hp1 .dirichlet j φ.val = 0) :
    sourceAngularThetaThetaBracket hp hp1 h2p n m s φ.val = 0 := by
  classical
  have hφ := D.real_subset φ.property
  obtain ⟨Vn,Un,cn,Tn,rn,Rn,zn,ρn,δn,εn,hφn,hnW,_,Cn⟩ := D.local_charts n φ.val hφ hn
  obtain ⟨Vm,Um,cm,Tm,rm,Rm,zm,ρm,δm,εm,hφm,hmW,_,Cm⟩ := D.local_charts m φ.val hφ hm
  obtain ⟨an,hen⟩ := Cn.exists_etaDifferential_eq_anti_smul_of_eq_zero φ hφn (hterminal n)
  obtain ⟨am,hem⟩ := Cm.exists_etaDifferential_eq_anti_smul_of_eq_zero φ hφm (hterminal m)
  let L : ℤ → (CoeffPair p →L[ℂ] ℂ) := fun j =>
    fderiv ℂ (sourceBoundaryTerminalAntiDiscriminant hp hp1 .dirichlet j) φ.val
  have hpair (i j : ℤ) : sourceBivector h2p (L i) (L j) = 0 :=
    sourceBracket_boundaryTerminalAntiDiscriminants_eq_zero_of_eq_zero hp hp1 h2p .dirichlet i j φ
      (hterminal i) (hterminal j)
  have hterms : ∀ i j : ℤ, ∃ a : ℂ,
      fderiv ℂ (fun ψ => sourceAngularBetaSeriesTerm hp hp1 i s ψ j) φ.val = a • L j := by
    intro i j
    exact D.exists_fderiv_betaSeriesTerm_eq_anti_smul_of_eq_zero i j φ (hterminal j)
  choose a ha using hterms
  have hfinite (N : ℕ) : sourceBivector h2p
      (sourceAngularEtaDifferential hp hp1 n s φ.val+
        ∑ j ∈ Finset.Icc (-(N:ℤ)) N, fderiv ℂ (fun ψ => sourceAngularBetaSeriesTerm hp hp1 n s ψ j) φ.val)
      (sourceAngularEtaDifferential hp hp1 m s φ.val+
        ∑ j ∈ Finset.Icc (-(N:ℤ)) N, fderiv ℂ (fun ψ => sourceAngularBetaSeriesTerm hp hp1 m s ψ j) φ.val) = 0 := by
    rw [hen,hem]
    change sourceBivector h2p (an • L n+_) (am • L m+_) = 0
    simp only [ha,map_add,add_apply,map_sum,sum_apply,map_smul,smul_apply,smul_eq_mul,
      hpair,mul_zero,Finset.sum_const_zero,add_zero]
  have ht := D.tendsto_thetaThetaSeriesBrackets h2p n m Cn Cm hnW hmW φ.val hφn hφm
  have hz : Tendsto (fun _ : ℕ => (0:ℂ)) atTop
      (𝓝 (sourceAngularThetaThetaBracket hp hp1 h2p n m s φ.val)) := by
    simpa only [hfinite] using ht
  exact tendsto_nhds_unique hz tendsto_const_nhds

/-- The actual angle/angle bracket vanishes whenever every Dirichlet
terminal is either of its own periodic endpoints. In particular this
covers the all-left-endpoint basepoint used for isospectral transport. -/
theorem thetaThetaBracket_eq_zero_of_all_dirichlet_endpoints
    (D : SourceAngularThetaCommonDomainData hp hp1 W₀ B W s)
    (h2p : (2 : ℝ≥0∞) ≤ p) (n m : ℤ) (φ : realTypeSourceLocus p)
    (hn : canonicalPeriodicGap hp hp1 (periodOnePotential φ.val) (periodOnePotential_mem φ.val) n ≠ 0)
    (hm : canonicalPeriodicGap hp hp1 (periodOnePotential φ.val) (periodOnePotential_mem φ.val) m ≠ 0)
    (hend : ∀ j : ℤ, canonicalPeriodOneBoundaryRoots hp hp1 .dirichlet φ.val j =
      canonicalPeriodicLeft hp hp1 (periodOnePotential φ.val) (periodOnePotential_mem φ.val) j ∨
      canonicalPeriodOneBoundaryRoots hp hp1 .dirichlet φ.val j =
        canonicalPeriodicRight hp hp1 (periodOnePotential φ.val) (periodOnePotential_mem φ.val) j) :
    sourceAngularThetaThetaBracket hp hp1 h2p n m s φ.val = 0 :=
  D.thetaThetaBracket_eq_zero_of_all_terminals_periodic h2p n m φ hn hm
    (fun j => sourceBoundaryTerminalAntiDiscriminant_eq_zero_of_endpoint hp hp1 .dirichlet j φ.val (hend j))

end SourceAngularThetaCommonDomainData
end NLS.ZakharovShabat
