import NLS.ZakharovShabat.SourcePsiGapRootMap
import NLS.ComplexAnalysis.BanachC1ImplicitDerivative
import NLS.ZakharovShabat.SourcePsiGlobalEquationTaylorTruncation

/-!
# Derivative of the canonical real gap psi roots

At each real-type source, a local complex `C¹` extension of the
canonical root map solves a selected psi equation with bijective root
Jacobian. Differentiating that equation gives the source-direction
derivative of the root map through the Jacobian.
-/

noncomputable section
open Set Metric Filter Topology Complex
open scoped ENNReal ContDiff
namespace NLS.ZakharovShabat

/-- In a local contour chart, the derivative of the canonical root
branch solves the linearized psi equation. The Jacobian is bijective,
so this equation determines that derivative uniquely. -/
theorem exists_sourcePsiGapRoot_derivative_equation
    {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (hp : p ≠ ⊤) (hp1 : 1 < p) (n : ℤ)
    (φ : realTypeSourceLocus p) :
    ∃ c : ℤ → ℂ, ∃ R : ℤ → ℝ,
      ∃ s : CoeffPair p → DeletedCoeff p n,
        ContDiffAt ℂ 1 s φ.val ∧
        s φ.val = sourcePsiGapRoot hp hp1 n φ ∧
        (∀ᶠ χ in 𝓝 φ.val,
          ∀ hχ : IsRealType (CoeffPair.toMax p χ),
            s χ = sourcePsiGapRoot hp hp1 n ⟨χ,hχ⟩) ∧
        Function.Bijective
          (sourcePsiSelectedRootJacobian hp hp1 n c R
            (sourcePsiGapRoot hp hp1 n φ) φ.val) ∧
        (∀ᶠ χ in 𝓝 φ.val,
          sourcePsiSelectedEquationSequence hp hp1 n c R (s χ) χ = 0) ∧
        AnalyticAt ℂ
          (fun t : DeletedCoeff p n × CoeffPair p =>
            sourcePsiSelectedEquationSequence hp hp1 n c R t.1 t.2)
          (sourcePsiGapRoot hp hp1 n φ,φ.val) ∧
        ∀ h : CoeffPair p,
          (sourcePsiSelectedRootJacobian hp hp1 n c R
            (sourcePsiGapRoot hp hp1 n φ) φ.val)
              ((fderiv ℂ s φ.val) h) =
            - (fderiv ℂ
                (fun t : DeletedCoeff p n × CoeffPair p =>
                  sourcePsiSelectedEquationSequence hp hp1 n c R t.1 t.2)
                (sourcePsiGapRoot hp hp1 n φ,φ.val)) (0,h) := by
  let a := sourcePsiGapRoot hp hp1 n φ
  obtain ⟨hgap,c,R,hcenter,hgeom,hcoord,hzero⟩ :=
    sourcePsiGapRoot_solution hp hp1 n φ
  obtain ⟨b,σ,U,c₀,R₀,hσ,hb,hbgap,hUopen,hbase,
      hcenter₀,hgeom₀,hcoord₀,hC1,hzero₀,hbij,s,V,hVopen,hVbase,
      hs,hsb,hunique,hchartUnique,hbranch⟩ :=
    exists_limit_sourcePsi_gap_solution hp hp1 φ.val φ.property
      (fun _ : ℕ => φ.val) tendsto_const_nhds
      (fun _ => φ.property) n (fun _ => a)
      (fun _ => hgap) (fun _ => c) (fun _ => R)
      (fun _ => hcenter) (fun _ => hgeom)
      (fun _ => hcoord) (fun _ => hzero)
  have hba : b = a := by
    have hb' : Tendsto (fun _ : ℕ => a) atTop (𝓝 b) := by
      simpa only [Function.comp_def] using hb
    exact tendsto_nhds_unique hb' tendsto_const_nhds
  have hsroot : s φ.val = sourcePsiGapRoot hp hp1 n φ := by
    exact hsb.trans hba
  let F : DeletedCoeff p n × CoeffPair p → DeletedCoeff p n :=
    fun t => sourcePsiSelectedEquationSequence hp hp1 n c₀ R₀ t.1 t.2
  have hF : DifferentiableAt ℂ F (b,φ.val) :=
    (hC1.contDiffAt (hUopen.mem_nhds hbase)).differentiableAt (by norm_num)
  have hzeros : ∀ᶠ χ in 𝓝 φ.val, F (s χ,χ) = 0 :=
    hbranch.mono (fun χ hχ => hχ.2.1)
  have hFanalyticB : AnalyticAt ℂ F (b,φ.val) := by
    obtain ⟨Vana,_,hbaseAna,_,hFana⟩ :=
      exists_analytic_sourcePsi_deletedEquation_on_contourChart
        hp hp1 φ.val φ.property n b c₀ R₀ hUopen hbase
        (fun t ht m => ⟨(hgeom₀ t ht m).1,(hgeom₀ t ht m).2.2.2⟩)
        hcoord₀ (hC1.differentiableOn (by norm_num))
    exact hFana (b,φ.val) hbaseAna
  have hpartial := sourcePsiSelectedEquation_partial_fderiv_eq_rootJacobian
    hp hp1 n c₀ R₀ b φ.val hF
  have hderiv (h : CoeffPair p) :
      (sourcePsiSelectedRootJacobian hp hp1 n c₀ R₀ b φ.val)
        ((fderiv ℂ s φ.val) h) = - (fderiv ℂ F (b,φ.val)) (0,h) := by
    have hbal := NLS.ComplexAnalysis.implicitBanachRoot_fderiv_balance
      F s φ.val (by simpa only [hsb] using hF)
        (hs.differentiableAt (by norm_num)) hzeros h
    have hsplit : ((fderiv ℂ s φ.val) h,h) =
        ((fderiv ℂ s φ.val) h,(0 : CoeffPair p)) +
          ((0 : DeletedCoeff p n),h) := by
      ext <;> simp
    rw [hsb,hsplit,map_add] at hbal
    have hQ : (fderiv ℂ F (b,φ.val))
        ((fderiv ℂ s φ.val) h,0) =
        (sourcePsiSelectedRootJacobian hp hp1 n c₀ R₀ b φ.val)
          ((fderiv ℂ s φ.val) h) := by
      have heq := congrArg
        (fun L : DeletedCoeff p n →L[ℂ] DeletedCoeff p n =>
          L ((fderiv ℂ s φ.val) h)) hpartial
      simpa only [ContinuousLinearMap.comp_apply,ContinuousLinearMap.inl_apply]
        using heq
    rw [hQ] at hbal
    exact eq_neg_of_add_eq_zero_left hbal
  have hrootEvent : ∀ᶠ χ in 𝓝 φ.val,
      ∀ hχ : IsRealType (CoeffPair.toMax p χ),
        s χ = sourcePsiGapRoot hp hp1 n ⟨χ,hχ⟩ := by
    filter_upwards [hbranch] with χ hχ hreal
    have hsol : SourcePsiGapSolution hp hp1 n χ (s χ) :=
      ⟨(hχ.2.2 hreal).2,c₀,R₀,hcenter₀,
        (fun m => let h := hgeom₀ (s χ,χ) hχ.1 m;
          ⟨h.1,h.2.1,h.2.2.1⟩),
        (hcoord₀ (s χ,χ) hχ.1),hχ.2.1⟩
    exact hsol.eq_sourcePsiGapRoot hp hp1 n ⟨χ,hreal⟩ (s χ)
  refine ⟨c₀,R₀,s,hs,hsroot,hrootEvent,?_⟩
  have hbro : b = sourcePsiGapRoot hp hp1 n φ := hba
  rw [← hbro]
  exact ⟨hbij,by simpa only [F] using hzeros,hFanalyticB,
    fun h => by simpa only [F] using hderiv h⟩

end NLS.ZakharovShabat
