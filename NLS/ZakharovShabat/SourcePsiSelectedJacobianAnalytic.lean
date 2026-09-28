import NLS.ZakharovShabat.SourcePsiLocalJacobianBijectivity
import NLS.ZakharovShabat.SourcePsiGlobalEquationTaylorTruncation

/-!
# Analytic selected equation on the invertible-Jacobian chart

The contour family used for the selected-root Jacobian has a
Fréchet-differentiable sequence equation and valid scalar contour
coordinates. The coordinatewise criterion upgrades this *same*
equation to Banach analyticity near its real-type base point.
-/

noncomputable section
open Set Metric Complex
open scoped ENNReal
namespace NLS.ZakharovShabat

/-- Around any real-type source and deleted-root input, one selected
contour family has an analytic equation and a bijective root Jacobian
at all real, isolated root data on that chart. -/
theorem exists_local_sourcePsi_selectedJacobian_bijective_analytic
    {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (φ : CoeffPair p) (hφ : IsRealType (CoeffPair.toMax p φ))
    (n : ℤ) (a₀ : DeletedCoeff p n) :
    ∃ c : ℤ → ℂ, ∃ R : ℤ → ℝ,
      ∃ Niso : ℕ, ∃ εiso : ℝ,
      ∃ V : Set (DeletedCoeff p n × CoeffPair p),
        IsOpen V ∧ (a₀,φ) ∈ V ∧
        AnalyticOnNhd ℂ
          (fun t : DeletedCoeff p n × CoeffPair p =>
            sourcePsiSelectedEquationSequence hp hp1 n c R t.1 t.2) V ∧
        ∀ a : DeletedCoeff p n, ∀ ψ : CoeffPair p,
          (a,ψ) ∈ V →
          IsRealType (CoeffPair.toMax p ψ) →
          (∀ j : ℤ, (displacedRoots (a : Coeff p) j).im = 0) →
          (∀ j : ℤ, j ≠ n → displacedRoots (a : Coeff p) j ∈
            sourceIsolatingDisc hp hp1 φ Niso εiso j) →
          Function.Bijective
            (sourcePsiSelectedRootJacobian hp hp1 n c R a ψ) := by
  obtain ⟨U,hUopen,hbase,c,R,Niso,εiso,
      _,_,_,hgeom,hcoord,hC1,hbij⟩ :=
    exists_local_sourcePsi_selectedJacobian_bijective
      hp hp1 φ hφ n a₀
  obtain ⟨V,hVopen,hbaseV,hVU,hanalytic⟩ :=
    exists_analytic_sourcePsi_deletedEquation_on_contourChart
      hp hp1 φ hφ n a₀ c R hUopen hbase
      (fun t ht m => ⟨(hgeom t ht m).1,(hgeom t ht m).2.2.2⟩)
      hcoord (hC1.differentiableOn (by norm_num))
  refine ⟨c,R,Niso,εiso,V,hVopen,hbaseV,hanalytic,?_⟩
  intro a ψ hpair hreal hroots hloc
  exact hbij a ψ (hVU hpair) hreal hroots hloc

end NLS.ZakharovShabat
