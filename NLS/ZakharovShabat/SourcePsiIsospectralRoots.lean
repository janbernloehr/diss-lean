import NLS.ZakharovShabat.SourcePsiIsospectralContour
import NLS.ZakharovShabat.SourcePsiGapRootDerivative
import NLS.ZakharovShabat.SourcePsiLemma12_10
import NLS.ZakharovShabat.SourceHolomorphicRealCenteredBalls

/-! # Actual normalized psi roots are stationary in isospectral directions

The actual canonical real solution has an analytic local extension
solving a fixed selected contour equation with a bijective root Jacobian.
Its source partial derivative vanishes in an isospectral direction.
Differentiating the implicit equation and using injectivity proves zero
root variation. Real-form uniqueness identifies this derivative with
that of every actual common-domain analytic psi extension.
-/

noncomputable section
set_option maxHeartbeats 800000
open Set Metric Filter Topology Complex
open scoped ENNReal ContDiff
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- An actual local canonical psi branch is stationary in every
isospectral source direction, by its actual fixed contour equation
and the proved bijective selected-root Jacobian. -/
theorem exists_sourcePsiGapRoot_isospectral_local_derivative
    (hp : p ≠ ⊤) (hp1 : 1 < p) (n : ℤ) (φ : realTypeSourceLocus p)
    (h : CoeffPair p) (hiso : SourceIsospectralDirection hp φ.val h) :
    ∃ t : CoeffPair p → DeletedCoeff p n, AnalyticAt ℂ t φ.val ∧
      (∀ᶠ χ in 𝓝 φ.val, ∀ hχ : IsRealType (CoeffPair.toMax p χ),
        t χ = sourcePsiGapRoot hp hp1 n ⟨χ,hχ⟩) ∧
      (fderiv ℂ t φ.val) h = 0 := by
  let a := sourcePsiGapRoot hp hp1 n φ
  obtain ⟨hgap,c,R,hcenter,hgeom,hcoord,hzero⟩ := sourcePsiGapRoot_solution hp hp1 n φ
  obtain ⟨b,σ,U,c₀,R₀,_,_,_,hUopen,hbase,hcenter₀,hgeom₀,hcoord₀,hC1,_,hbij,
      t,V,_,_,ht,htb,_,_,hbranch⟩ :=
    exists_limit_sourcePsi_gap_solution hp hp1 φ.val φ.property
      (fun _ : ℕ => φ.val) tendsto_const_nhds (fun _ => φ.property) n (fun _ => a)
      (fun _ => hgap) (fun _ => c) (fun _ => R) (fun _ => hcenter)
      (fun _ => hgeom) (fun _ => hcoord) (fun _ => hzero)
  let F : DeletedCoeff p n × CoeffPair p → DeletedCoeff p n :=
    fun q => sourcePsiSelectedEquationSequence hp hp1 n c₀ R₀ q.1 q.2
  have hF : DifferentiableAt ℂ F (b,φ.val) :=
    (hC1.contDiffAt (hUopen.mem_nhds hbase)).differentiableAt (by norm_num)
  have hzeros : ∀ᶠ χ in 𝓝 φ.val, F (t χ,χ) = 0 := hbranch.mono (fun χ hχ => hχ.2.1)
  have hFanalytic : AnalyticAt ℂ F (b,φ.val) := by
    obtain ⟨_,_,hbaseAna,_,hFana⟩ := exists_analytic_sourcePsi_deletedEquation_on_contourChart
      hp hp1 φ.val φ.property n b c₀ R₀ hUopen hbase
      (fun q hq m => ⟨(hgeom₀ q hq m).1,(hgeom₀ q hq m).2.2.2⟩)
      hcoord₀ (hC1.differentiableOn (by norm_num))
    exact hFana (b,φ.val) hbaseAna
  have htanalytic : AnalyticAt ℂ t φ.val :=
    analyticAt_sourcePsi_implicit_solution_of_analytic hp hp1 n c₀ R₀ t φ.val
      (by simpa only [htb] using hFanalytic) ht.continuousAt hzeros
      (by simpa only [htb] using hbij)
  have hpartial := sourcePsiSelectedEquation_partial_fderiv_eq_rootJacobian hp hp1 n c₀ R₀ b φ.val hF
  have hsourcezero := fderiv_sourcePsiSelectedEquation_isospectral_eq_zero hp hp1 n b φ.val φ.property h hiso
    c₀ R₀ U hUopen hbase hcoord₀ hF
    (fun m => ⟨(hgeom₀ (b,φ.val) hbase m).1.le,(hgeom₀ (b,φ.val) hbase m).2.2.2⟩)
  have hstationary : (fderiv ℂ t φ.val) h = 0 := by
    apply hbij.1
    rw [map_zero]
    have hbalance := NLS.ComplexAnalysis.implicitBanachRoot_fderiv_balance F t φ.val
      (by simpa only [htb] using hF) htanalytic.differentiableAt hzeros h
    have hsplit : ((fderiv ℂ t φ.val) h,h) =
        ((fderiv ℂ t φ.val) h,(0 : CoeffPair p)) + ((0 : DeletedCoeff p n),h) := by
      ext <;> simp
    rw [htb,hsplit,map_add,hsourcezero,add_zero] at hbalance
    have hQ := congrArg (fun L : DeletedCoeff p n →L[ℂ] DeletedCoeff p n => L ((fderiv ℂ t φ.val) h)) hpartial
    simp only [ContinuousLinearMap.comp_apply,ContinuousLinearMap.inl_apply] at hQ
    rw [hQ] at hbalance
    exact hbalance
  have hrealEvent : ∀ᶠ χ in 𝓝 φ.val, ∀ hχ : IsRealType (CoeffPair.toMax p χ),
      t χ = sourcePsiGapRoot hp hp1 n ⟨χ,hχ⟩ := by
    filter_upwards [hbranch] with χ hχ hreal
    have hsol : SourcePsiGapSolution hp hp1 n χ (t χ) :=
      ⟨(hχ.2.2 hreal).2,c₀,R₀,hcenter₀,
        (fun m => let hg := hgeom₀ (t χ,χ) hχ.1 m; ⟨hg.1,hg.2.1,hg.2.2.1⟩),
        hcoord₀ (t χ,χ) hχ.1,hχ.2.1⟩
    exact hsol.eq_sourcePsiGapRoot hp hp1 n ⟨χ,hreal⟩ (t χ)
  exact ⟨t,htanalytic,hrealEvent,hstationary⟩

namespace SourcePsiIsolatingComplexExtension
variable {hp : p ≠ ⊤} {hp1 : 1 < p} {W : Set (CoeffPair p)}
  {s : (n : ℤ) → CoeffPair p → DeletedCoeff p n}

/-- The actual common-domain psi root family has zero variation in
every isospectral source direction at every real source in its domain.
No finite-support, open-gap, or canonical-bracket premise is assumed. -/
theorem fderiv_isospectral_eq_zero
    (hs : SourcePsiIsolatingComplexExtension hp hp1 W s)
    (n : ℤ) (φ : realTypeSourceLocus p) (hφ : φ.val ∈ W)
    (h : CoeffPair p) (hiso : SourceIsospectralDirection hp φ.val h) :
    (fderiv ℂ (s n) φ.val) h = 0 := by
  obtain ⟨t,ht,hrealEvent,hstationary⟩ := exists_sourcePsiGapRoot_isospectral_local_derivative hp hp1 n φ h hiso
  have hsbase := hs.analytic n φ.val hφ
  obtain ⟨r,hr,hball⟩ := Metric.mem_nhds_iff.mp
    ((hsbase.eventually_analyticAt.and ht.eventually_analyticAt).and hrealEvent)
  have hsa : DifferentiableOn ℂ (s n) (ball φ.val r) :=
    fun ψ hψ => (hball hψ).1.1.differentiableAt.differentiableWithinAt
  have hta : DifferentiableOn ℂ t (ball φ.val r) :=
    fun ψ hψ => (hball hψ).1.2.differentiableAt.differentiableWithinAt
  have heq := eqOn_sourceRealCenteredBalls_of_real_agreement hp φ φ r r (s n) t hsa hta
    (fun χ hχ => (hs.real_agreement n χ).trans ((hball hχ.1).2 χ.property).symm)
  have hnear : s n =ᶠ[𝓝 φ.val] t := by
    filter_upwards [isOpen_ball.mem_nhds (mem_ball_self hr)] with ψ hψ
    exact heq ⟨hψ,hψ⟩
  rw [hnear.fderiv_eq]
  exact hstationary

/-- Every actual action Hamiltonian direction fixes every actual
normalized psi root vector, including at collapsed periodic gaps. -/
theorem fderiv_sourceHamiltonianVector_action_eq_zero
    (hs : SourcePsiIsolatingComplexExtension hp hp1 W s)
    (h2p : (2 : ℝ≥0∞) ≤ p) (n m : ℤ)
    (φ : realTypeSourceLocus p) (hφ : φ.val ∈ W) :
    (fderiv ℂ (s n) φ.val)
      (NLS.Poisson.sourceHamiltonianVector h2p (sourceComplexAction hp hp1 m) φ.val) = 0 :=
  hs.fderiv_isospectral_eq_zero n φ hφ _
    (sourceHamiltonianVector_action_isospectral hp hp1 h2p φ.val φ.property m)

/-- Every actual entire normalized numerator is stationary at every
spectral parameter in an isospectral direction. No spectral cut
restriction is needed for this entire function. -/
theorem fderiv_numerator_isospectral_eq_zero
    (hs : SourcePsiIsolatingComplexExtension hp hp1 W s)
    (n : ℤ) (φ : realTypeSourceLocus p) (hφ : φ.val ∈ W)
    (h : CoeffPair p) (hiso : SourceIsospectralDirection hp φ.val h) (z : ℂ) :
    (fderiv ℂ (fun ψ : CoeffPair p => sourcePsiCandidate n (z,(s n ψ : Coeff p))) φ.val) h = 0 := by
  let i : DeletedCoeff p n →L[ℂ] Coeff p := (lp.evalCLM ℂ (fun _ : ℤ => ℂ) p n).ker.subtypeL
  let C : DeletedCoeff p n → ℂ := fun b => sourcePsiCandidate n (z,(b : Coeff p))
  have hC : DifferentiableAt ℂ C (s n φ.val) := by
    exact ((analyticOnNhd_sourcePsiCandidate hp hp1 n (z,(s n φ.val : Coeff p)) (mem_univ _)).comp
      (f := fun b : DeletedCoeff p n => (z,i b)) (analyticAt_const.prod (i.analyticAt _))).differentiableAt
  have hchain := hC.hasFDerivAt.comp φ.val (hs.analytic n φ.val hφ).differentiableAt.hasFDerivAt
  have heval := congrArg (fun L : CoeffPair p →L[ℂ] ℂ => L h) hchain.fderiv
  simp only [Function.comp_def,ContinuousLinearMap.comp_apply,
    hs.fderiv_isospectral_eq_zero n φ hφ h hiso,map_zero] at heval
  exact heval

/-- The actual entire normalized psi numerator commutes with every
actual indexed action at every real source in its common domain. -/
theorem sourceBracket_numerator_action_eq_zero
    (hs : SourcePsiIsolatingComplexExtension hp hp1 W s)
    (h2p : (2 : ℝ≥0∞) ≤ p) (n m : ℤ)
    (φ : realTypeSourceLocus p) (hφ : φ.val ∈ W) (z : ℂ) :
    NLS.Poisson.sourceBracket h2p
      (fun ψ : CoeffPair p => sourcePsiCandidate n (z,(s n ψ : Coeff p)))
      (sourceComplexAction hp hp1 m) φ.val = 0 := by
  rw [← NLS.Poisson.fderiv_apply_sourceHamiltonianVector]
  exact hs.fderiv_numerator_isospectral_eq_zero n φ hφ _
    (sourceHamiltonianVector_action_isospectral hp hp1 h2p φ.val φ.property m) z

end SourcePsiIsolatingComplexExtension
end NLS.ZakharovShabat
