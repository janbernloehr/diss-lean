import NLS.SequenceSpaces.RealPairComplexification
import NLS.SequenceSpaces.RealGermScalarActionDescent
import NLS.SequenceSpaces.RealActionLifting
import NLS.SequenceSpaces.RealActionBallGluing

/-! A real analytic scalar action invariant has a single holomorphic
extension near the entire nonnegative action cone. Zero actions, infinite
tails and the actual half-exponent Banach action norm are all retained. -/
noncomputable section
open Set Metric Filter Topology
open scoped ENNReal
namespace NLS.Coeff
variable {p q : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ q)] [p.HolderTriple p q]

theorem real_pairAction_eq_of_quadraticActions_eq
    (x y : RealCoeff p × RealCoeff p)
    (h : quadraticActionsExponent (q := q)
        (((RealCoeff.complexCLM p).prodMap (RealCoeff.complexCLM p)) x) =
      quadraticActionsExponent (q := q)
        (((RealCoeff.complexCLM p).prodMap (RealCoeff.complexCLM p)) y)) :
    ∀ k, RealCoeff.pairAction x k = RealCoeff.pairAction y k := by
  intro k
  have hk := congrArg (fun a : Coeff q => a k) h
  simp only [quadraticActionsExponent_apply] at hk
  change ((x.1 k:ℂ)^2+(x.2 k:ℂ)^2)/2 = ((y.1 k:ℂ)^2+(y.2 k:ℂ)^2)/2 at hk
  dsimp only [RealCoeff.pairAction]
  exact_mod_cast hk

/-- A complete real analytic invariant descends analytically to a
neighborhood of ALL nonnegative action data, including the boundary. -/
theorem exists_analytic_scalar_action_factor_of_real_analytic
    (hp : p ≠ ⊤) (f : (RealCoeff p × RealCoeff p) → ℂ)
    (hf : ∀ x, AnalyticAt ℝ f x)
    (hinv : ∀ x y, (∀ k, RealCoeff.pairAction y k = RealCoeff.pairAction x k) → f y = f x) :
    ∃ U : Set (Coeff q), ∃ G : Coeff q → ℂ,
      IsOpen U ∧ nonnegativeLocus q ⊆ U ∧ AnalyticOnNhd ℂ G U ∧
      ∀ x : RealCoeff p × RealCoeff p,
        G (quadraticActionsExponent (((RealCoeff.complexCLM p).prodMap (RealCoeff.complexCLM p)) x)) = f x := by
  let J := (RealCoeff.complexCLM p).prodMap (RealCoeff.complexCLM p)
  let a : (RealCoeff p × RealCoeff p) → Coeff q := fun x => quadraticActionsExponent (J x)
  have hJ (x : RealCoeff p × RealCoeff p) : J x ∈ realPairLocus p := by
    exact (mem_realPairLocus_iff _).mpr ⟨x,rfl⟩
  have ha (x : RealCoeff p × RealCoeff p) : a x ∈ nonnegativeLocus q :=
    quadraticActions_mem_nonnegativeLocus (J x) (hJ x)
  have hsurj (b : Coeff q) (hb : b ∈ nonnegativeLocus q) : ∃ x, a x = b := by
    obtain ⟨z,hz,he,_⟩ := exists_real_quadraticActions_lift hp b hb
    obtain ⟨x,rfl⟩ := (mem_realPairLocus_iff z).mp hz
    exact ⟨x,he⟩
  have hlocal (x : RealCoeff p × RealCoeff p) :
      ∃ r : ℝ, 0 < r ∧ ∃ g : Coeff q → ℂ,
        AnalyticOnNhd ℂ g (ball (a x) r) ∧ ∀ y, a y ∈ ball (a x) r → g (a y) = f y := by
    obtain ⟨F,hF,he⟩ := (realPairContractiveComplexification p).exists_complex_extension_of_analyticAt (hf x)
    obtain ⟨Z,T,g,hZ,hx,hT,himage,hg,hrec,hreal⟩ :=
      exists_local_scalar_action_factor_of_real_germ (q := q) hp f hinv x F hF he
    have hax : a x ∈ T := by rw [← himage]; exact ⟨J x,hx,rfl⟩
    obtain ⟨r,hr,hrT⟩ := Metric.isOpen_iff.mp hT (a x) hax
    obtain ⟨s,hs,hsZ⟩ := exists_ball_real_quadraticActions_lifts (q := q) hp (J x) (hJ x) Z hZ hx
    refine ⟨min r s,lt_min hr hs,g,hg.mono (ball_subset_ball (min_le_left _ _) |>.trans hrT),?_⟩
    intro y hy
    have hyS : a y ∈ ball (a x) s := ball_subset_ball (min_le_right _ _) hy
    obtain ⟨z,⟨hzZ,hzr⟩,hza⟩ := hsZ ⟨hyS,ha y⟩
    obtain ⟨v,rfl⟩ := (mem_realPairLocus_iff z).mp hzr
    have hev : f y = f v := hinv v y (real_pairAction_eq_of_quadraticActions_eq y v hza.symm)
    exact hza ▸ (hreal v hzZ).trans hev.symm
  choose r hr g hg hrec using hlocal
  obtain ⟨G,hG,hval⟩ := exists_analytic_gluing_of_real_action_ball_recovery hp a r f ha hr
    (fun _ b _ hb => hsurj b hb) (fun x => ⟨g x,hg x,hrec x⟩)
  refine ⟨⋃ x, ball (a x) (r x),G,isOpen_iUnion (fun _ => isOpen_ball),?_,hG,hval⟩
  intro b hb
  obtain ⟨x,rfl⟩ := hsurj b hb
  exact mem_iUnion.mpr ⟨x,mem_ball_self (hr x)⟩

end NLS.Coeff
