import NLS.ZakharovShabat.SourcePsiJacobianContourIndependence
import NLS.ZakharovShabat.SourcePsiLocalJacobianBijectivity

/-!
# Continuous invertible finite Jacobians on the full gap product

At a fixed real-type potential, contour independence transports each
local bounded holomorphic chart to any valid real-centered family.
The root derivative is therefore continuous in operator norm. Real
gap placement supplies the isolating-root hypotheses for its actual
pointwise bijectivity at every deleted index.
-/

noncomputable section
open Set Filter Topology Metric Complex
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

theorem continuous_sourcePsiSelectedRootJacobian_on_realCentered_family
    (hp : p ≠ ⊤) (hp1 : 1 < p) (φ : CoeffPair p)
    (hφ : IsRealType (CoeffPair.toMax p φ))
    (c : ℤ → ℂ) (R : ℤ → ℝ)
    (hfamily : sourcePsiRealCenteredContourFamily hp hp1 φ c R) (n : ℤ) :
    Continuous (fun a : DeletedCoeff p n => sourcePsiSelectedRootJacobian hp hp1 n c R a φ) := by
  rw [continuous_iff_continuousAt]
  intro a
  obtain ⟨U,hUopen,hbase,K,c',R',hcenter,hfree,hgeom,hiso,C,hC,hcoord,hbound,hreal,hdiff⟩ :=
    exists_local_sourcePsi_globalEquation_formula_analytic hp hp1 φ hφ n a
  let V : Set (DeletedCoeff p n) := {b | (b,φ) ∈ U}
  have hVopen : IsOpen V := hUopen.preimage (by fun_prop)
  have haV : a ∈ V := hbase
  let f : DeletedCoeff p n → DeletedCoeff p n :=
    fun b => sourcePsiSelectedEquationSequence hp hp1 n c' R' b φ
  have hf : DifferentiableOn ℂ f V := by
    intro b hb
    have hpair : DifferentiableAt ℂ (fun b : DeletedCoeff p n => (b,φ)) b := by fun_prop
    exact (((hdiff (b,φ) hb).differentiableAt (hUopen.mem_nhds hb)).comp b hpair).differentiableWithinAt
  have hder : ContinuousOn (fderiv ℂ f) V :=
    (NLS.ComplexAnalysis.contDiffOn_one_of_differentiableOn f hVopen hf).continuousOn_fderiv_of_isOpen
      hVopen (by norm_num)
  have hcont := (hder a haV).continuousAt (hVopen.mem_nhds haV)
  have hfamily' : sourcePsiRealCenteredContourFamily hp hp1 φ c' R' :=
    ⟨hcenter,fun m => hgeom (a,φ) hbase m⟩
  have heq : (fun b : DeletedCoeff p n => sourcePsiSelectedRootJacobian hp hp1 n c R b φ) =
      (fun b : DeletedCoeff p n => sourcePsiSelectedRootJacobian hp hp1 n c' R' b φ) := by
    funext b
    exact sourcePsiSelectedRootJacobian_eq_of_realCentered_families hp hp1 φ hφ
      c c' R R' hfamily hfamily' n b
  rw [heq]
  exact hcont

theorem continuous_sourcePsiFullRootJacobian_on_realCentered_family
    (hp : p ≠ ⊤) (hp1 : 1 < p) (φ : CoeffPair p)
    (hφ : IsRealType (CoeffPair.toMax p φ))
    (c : ℤ → ℂ) (R : ℤ → ℝ)
    (hfamily : sourcePsiRealCenteredContourFamily hp hp1 φ c R) (n : ℤ) :
    Continuous (fun a : Coeff p =>
      sourcePsiFullRootJacobian hp hp1 n c R (Coeff.deleteCoordinateTo n a) φ) := by
  have hQ := (continuous_sourcePsiSelectedRootJacobian_on_realCentered_family hp hp1 φ hφ c R hfamily n).comp
    (Coeff.deleteCoordinateTo (p := p) n).continuous
  unfold sourcePsiFullRootJacobian Coeff.deletedJacobianExtension Coeff.deletedOperatorExtension
  exact (continuous_const.clm_comp (hQ.clm_comp continuous_const)).add continuous_const

/-- Every actual full gap-root Jacobian is bijective, for every
deleted index and every valid real-centered contour family. -/
theorem sourcePsiFullRootJacobian_bijective_on_gapProduct
    (hp : p ≠ ⊤) (hp1 : 1 < p) (φ : CoeffPair p)
    (hφ : IsRealType (CoeffPair.toMax p φ))
    (c : ℤ → ℂ) (R : ℤ → ℝ)
    (hfamily : sourcePsiRealCenteredContourFamily hp hp1 φ c R)
    (n : ℤ) (a : sourcePeriodicGapRootSet hp hp1 φ) :
    Function.Bijective (sourcePsiFullRootJacobian hp hp1 n c R (Coeff.deleteCoordinateTo n a.val) φ) := by
  let b := Coeff.deleteCoordinateTo n a.val
  obtain ⟨U,hUopen,hbase,c',R',Niso,εiso,hdisjoint,hfilled,hcenter,hgeom,hcoord,hC1,hbij⟩ :=
    exists_local_sourcePsi_selectedJacobian_bijective hp hp1 φ hφ n b
  have hfamily' : sourcePsiRealCenteredContourFamily hp hp1 φ c' R' :=
    ⟨hcenter,fun m => hgeom (b,φ) hbase m⟩
  have hroot (j : ℤ) (hjn : j ≠ n) : displacedRoots (b : Coeff p) j = displacedRoots a.val j := by
    change displacedRoots (Coeff.deleteCoordinate n a.val) j = displacedRoots a.val j
    simp only [displacedRoots,Coeff.deleteCoordinate_apply_other n j hjn]
  have hroots (j : ℤ) : (displacedRoots (b : Coeff p) j).im = 0 := by
    by_cases hjn : j = n
    · subst j
      simp [b,displacedRoots,Coeff.deleteCoordinateTo]
    · rw [hroot j hjn]
      exact sourcePeriodicSegment_im_eq_zero_of_realType hp hp1 φ hφ j _ (a.property j)
  have hloc (j : ℤ) (hjn : j ≠ n) : displacedRoots (b : Coeff p) j ∈
      sourceIsolatingDisc hp hp1 φ Niso εiso j := by
    rw [hroot j hjn]
    exact hfilled j (ball_subset_closedBall ((hgeom (b,φ) hbase j).2.1 (a.property j)))
  rw [sourcePsiFullRootJacobian_eq_of_realCentered_families hp hp1 φ hφ
    c c' R R' hfamily hfamily' n b]
  exact (sourcePsiFullRootJacobian_bijective_iff hp hp1 n c' R' b φ).2
    (hbij b φ hbase hφ hroots hloc)

end NLS.ZakharovShabat
