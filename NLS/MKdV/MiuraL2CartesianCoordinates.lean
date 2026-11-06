import NLS.ZakharovShabat.SourceDiagonalActionRoot
import NLS.MKdV.MiuraActionFlowSobolev
import NLS.ZakharovShabat.SourceBirkhoffMapReal

/-! # Actual physical action radii in analytic Cartesian coordinates

The positive square root of the regularized Laurent ratio rescales the
original NLS rectangular coordinates. Each selected pair is analytic in
the original complex L² space through a closed selected action, is real
on physical profiles, and has squared radius exactly twice the physical
mKdV action. This does not assert infinite-dimensional invertibility or
canonicity of the resulting coordinate family.
-/
noncomputable section
open Set Metric Complex Filter Topology NLS.ZakharovShabat
open scoped ENNReal ComplexConjugate
namespace NLS.MKdV

def miuraL2CartesianCoordinates (n : ℕ) (a : Coeff 2) : ℂ × ℂ :=
  let ψ := scalarL2Diagonal a
  let r := sourceDiagonalActionRoot (by simp) (by norm_num) n ψ
  let z := sourceBirkhoffMap (by simp) (by norm_num) miuraActionFlowFamily.psi ψ
  (r*z.1 n,-(r*z.2 n))

theorem scalarL2Diagonal_realDiagonal (a : Coeff 2) (ha : ∀ j, a j = conj (a (-j))) :
    scalarL2Diagonal a ∈ realDiagonalSourceLocus 2 := by
  constructor
  · intro j
    change (scalarL2Diagonal a).snd j = conj ((scalarL2Diagonal a).fst (-j))
    rw [scalarL2Diagonal_fst,scalarL2Diagonal_snd]
    exact ha j
  · rw [scalarL2Diagonal_fst,scalarL2Diagonal_snd]

/-- Selected physical Cartesian coordinates are complex analytic and have
the exact physical radius on an original L² neighborhood, with no gap condition. -/
theorem exists_local_miuraL2CartesianCoordinates_analytic_radius
    (a : Coeff 2) (ha : ∀ j, a j = conj (a (-j))) (n : ℕ) (hn : 1 ≤ n) :
    ∃ U : Set (Coeff 2), IsOpen U ∧ a ∈ U ∧
      AnalyticOnNhd ℂ (miuraL2CartesianCoordinates n) U ∧
      ∀ b ∈ U, ((miuraL2CartesianCoordinates n b).1)^2 +
        ((miuraL2CartesianCoordinates n b).2)^2 = 2*miuraL2Action n b := by
  let D := miuraActionFlowFamily.data
  let φ : realDiagonalSourceLocus 2 := ⟨scalarL2Diagonal a,scalarL2Diagonal_realDiagonal a ha⟩
  obtain ⟨V,hV,hφV,_,hr,hfactor⟩ := exists_local_sourceDiagonalActionRoot_analytic_factor
    (by simp) (by norm_num) φ n (by omega)
  let U := scalarL2Diagonal ⁻¹' (V ∩ miuraActionFlowFamily.domain)
  have hU : IsOpen U := (hV.inter D.source_open).preimage scalarL2Diagonal.continuous
  have haU : a ∈ U := ⟨hφV,D.real_subset φ.property.1⟩
  let ex := (lp.evalCLM ℂ (fun _ : ℤ => ℂ) 2 (n : ℤ)).comp
    (ContinuousLinearMap.fst ℂ (Coeff 2) (Coeff 2))
  let ey := (lp.evalCLM ℂ (fun _ : ℤ => ℂ) 2 (n : ℤ)).comp
    (ContinuousLinearMap.snd ℂ (Coeff 2) (Coeff 2))
  refine ⟨U,hU,haU,?_,?_⟩
  · intro b hb
    have hmap := (D.analytic (scalarL2Diagonal b) hb.2).comp (scalarL2Diagonal.analyticAt b)
    have hroot := (hr (scalarL2Diagonal b) hb.1).comp (scalarL2Diagonal.analyticAt b)
    exact (hroot.mul ((ex.analyticAt _).comp hmap)).prod
      ((hroot.mul ((ey.analyticAt _).comp hmap)).neg)
  · intro b hb
    have hrad := D.action_radius (scalarL2Diagonal b) hb.2 n
    have hf := hfactor (scalarL2Diagonal b) hb.1
    change _ = 2*((1/2 : ℂ)*sourceDiagonalLaurentAction (by simp) (by norm_num) n 0 (scalarL2Diagonal b))
    rw [hf]
    dsimp only [miuraL2CartesianCoordinates]
    linear_combination (sourceDiagonalActionRoot (by simp) (by norm_num) n (scalarL2Diagonal b))^2*hrad

theorem analyticAt_miuraL2CartesianCoordinates
    (a : Coeff 2) (ha : ∀ j, a j = conj (a (-j))) (n : ℕ) (hn : 1 ≤ n) :
    AnalyticAt ℂ (miuraL2CartesianCoordinates n) a := by
  obtain ⟨U,_,haU,hA,_⟩ := exists_local_miuraL2CartesianCoordinates_analytic_radius a ha n hn
  exact hA a haU

theorem miuraL2CartesianCoordinates_radius
    (a : Coeff 2) (ha : ∀ j, a j = conj (a (-j))) (n : ℕ) (hn : 1 ≤ n) :
    ((miuraL2CartesianCoordinates n a).1)^2 + ((miuraL2CartesianCoordinates n a).2)^2 = 2*miuraL2Action n a := by
  obtain ⟨U,_,haU,_,hrad⟩ := exists_local_miuraL2CartesianCoordinates_analytic_radius a ha n hn
  exact hrad a haU

/-- The selected Cartesian pair is real at every physical L² profile. -/
theorem miuraL2CartesianCoordinates_real
    (a : Coeff 2) (ha : ∀ j, a j = conj (a (-j))) (n : ℕ) (hn : 1 ≤ n) :
    ((miuraL2CartesianCoordinates n a).1).im = 0 ∧ ((miuraL2CartesianCoordinates n a).2).im = 0 := by
  let φ : realDiagonalSourceLocus 2 := ⟨scalarL2Diagonal a,scalarL2Diagonal_realDiagonal a ha⟩
  have hr := (sourceDiagonalActionRoot_real_positive (by simp) (by norm_num) φ n (by omega)).1
  obtain ⟨hx,hy⟩ := miuraActionFlowFamily.data.coordinates_im_eq_zero_of_realType φ.val φ.property.1 n
  dsimp only [φ] at hr hx hy
  dsimp only [miuraL2CartesianCoordinates]
  simp only [mul_im,neg_im,hr,hx,hy,mul_zero,zero_mul,add_zero,neg_zero,and_self]

/-- The original independent physical H¹ action is exactly the Cartesian radius. -/
theorem miuraL2CartesianCoordinates_physical_H1_radius
    (a : ScalarDomain 2) (ha : ∀ j, a.val j = conj (a.val (-j))) (n : ℕ) (hn : 1 ≤ n) :
    ((miuraL2CartesianCoordinates n (scalarInclusion a)).1)^2 +
      ((miuraL2CartesianCoordinates n (scalarInclusion a)).2)^2 = 2*miuraMKdVAction a ha n := by
  have har : ∀ j, scalarInclusion a j = conj (scalarInclusion a (-j)) := by
    intro j
    simpa only [scalarInclusion_apply] using ha j
  rw [miuraL2CartesianCoordinates_radius _ har n hn,miuraL2Action_eq_physical a ha n hn]

/-- A zero actual action collapses exactly its Cartesian pair. -/
theorem miuraL2CartesianCoordinates_eq_zero_iff_action_zero
    (a : Coeff 2) (ha : ∀ j, a j = conj (a (-j))) (n : ℕ) (hn : 1 ≤ n) :
    miuraL2CartesianCoordinates n a = 0 ↔ miuraL2Action n a = 0 := by
  have hrad := miuraL2CartesianCoordinates_radius a ha n hn
  obtain ⟨hx,hy⟩ := miuraL2CartesianCoordinates_real a ha n hn
  constructor
  · intro h
    rw [h] at hrad
    norm_num at hrad
    exact hrad
  · intro h
    rw [h,mul_zero] at hrad
    have hr := congrArg Complex.re hrad
    simp only [pow_two,add_re,mul_re,hx,hy,mul_zero,sub_zero,zero_re] at hr
    apply Prod.ext
    · exact Complex.ext (by change _ = 0; nlinarith [sq_nonneg ((miuraL2CartesianCoordinates n a).2).re]) hx
    · exact Complex.ext (by change _ = 0; nlinarith [sq_nonneg ((miuraL2CartesianCoordinates n a).1).re]) hy

end NLS.MKdV
