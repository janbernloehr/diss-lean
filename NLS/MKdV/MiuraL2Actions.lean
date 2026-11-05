import NLS.MKdV.MiuraActionLevelExtension
import NLS.Poisson.L2Gardner

/-! # The actual mKdV actions extended to a complex L2 neighborhood

The independent physical H1 contour actions have a common ambient L2
extension by Lemma 7. Its full scalar gradient is obtained from its actual
Frechet derivative, with no externally prescribed coefficients.
-/
noncomputable section
open Set Complex NLS.ZakharovShabat NLS.Poisson
open scoped ENNReal ComplexConjugate
namespace NLS.MKdV

def scalarL2Diagonal : Coeff 2 →L[ℂ] CoeffPair 2 := CoeffPair.inlCLM+CoeffPair.inrCLM

@[simp] theorem scalarL2Diagonal_fst (a : Coeff 2) : (scalarL2Diagonal a).fst = a := by
  change a+0 = a
  simp

@[simp] theorem scalarL2Diagonal_snd (a : Coeff 2) : (scalarL2Diagonal a).snd = a := by
  change 0+a = a
  simp

theorem scalarL2Diagonal_scalarInclusion (a : ScalarDomain 2) :
    scalarL2Diagonal (scalarInclusion a) = sobolevSourceInclusion (a,a) := by
  apply (CoeffPair.toMax 2).injective
  exact Prod.ext (scalarL2Diagonal_fst _) (scalarL2Diagonal_snd _)

def miuraL2ActionDomain : Set (Coeff 2) :=
  scalarL2Diagonal ⁻¹' sourceDiagonalLaurentDomain (by simp) (by norm_num)

def miuraL2Action (n : ℕ) (a : Coeff 2) : ℂ :=
  (1/2 : ℂ)*sourceDiagonalLaurentAction (by simp) (by norm_num) n 0 (scalarL2Diagonal a)

theorem isOpen_miuraL2ActionDomain : IsOpen miuraL2ActionDomain :=
  (isOpen_sourceDiagonalLaurentDomain _ _).preimage scalarL2Diagonal.continuous

theorem real_mem_miuraL2ActionDomain (a : Coeff 2)
    (ha : ∀ j, a j = conj (a (-j))) : a ∈ miuraL2ActionDomain := by
  apply realDiagonal_subset_sourceDiagonalLaurentDomain
  constructor
  · intro j
    change (scalarL2Diagonal a).snd j = conj ((scalarL2Diagonal a).fst (-j))
    rw [scalarL2Diagonal_fst,scalarL2Diagonal_snd]
    exact ha j
  · rw [scalarL2Diagonal_fst,scalarL2Diagonal_snd]

theorem analyticOnNhd_miuraL2Action (n : ℕ) (hn : 1 ≤ n) :
    AnalyticOnNhd ℂ (miuraL2Action n) miuraL2ActionDomain := by
  intro a ha
  exact analyticAt_const.mul
    ((analyticOnNhd_sourceDiagonalLaurentAction _ _ n 0 (by omega) _ ha).comp (scalarL2Diagonal.analyticAt a))

theorem miuraL2Action_eq_physical (a : ScalarDomain 2)
    (ha : ∀ j, a.val j = conj (a.val (-j))) (n : ℕ) (hn : 1 ≤ n) :
    miuraL2Action n (scalarInclusion a) = miuraMKdVAction a ha n := by
  have h := sourceDiagonalLaurentAction_eq_two_miuraActionLevel a ha n hn 1
  simp only [mul_one,sub_self,miuraMKdVActionLevel_one] at h
  rw [miuraL2Action,scalarL2Diagonal_scalarInclusion,h]
  ring

theorem l2ScalarGradient_miuraL2Action (n : ℕ) (hn : 1 ≤ n) (a : Coeff 2)
    (ha : a ∈ miuraL2ActionDomain) (m : ℤ) :
    l2ScalarGradient (miuraL2Action n) a m = (1/2 : ℂ)*
      ((CoeffPair.cotangentCoefficients le_rfl (fderiv ℂ (sourceDiagonalLaurentAction (by simp) (by norm_num) n 0)
        (scalarL2Diagonal a))).1 (-m)+
       (CoeffPair.cotangentCoefficients le_rfl (fderiv ℂ (sourceDiagonalLaurentAction (by simp) (by norm_num) n 0)
        (scalarL2Diagonal a))).2 (-m)) := by
  rw [l2ScalarGradient_apply]
  have hd := ((analyticOnNhd_sourceDiagonalLaurentAction _ _ n 0 (by omega) _ ha).differentiableAt.hasFDerivAt.comp
    a scalarL2Diagonal.hasFDerivAt).const_mul (1/2 : ℂ)
  change HasFDerivAt (miuraL2Action n) _ a at hd
  have hs : scalarL2Diagonal (lp.single 2 (-m) 1) =
      CoeffPair.inlCLM (lp.single 2 (-m) 1)+CoeffPair.inrCLM (lp.single 2 (-m) 1) := rfl
  rw [hd.fderiv,smul_apply,smul_eq_mul,ContinuousLinearMap.comp_apply,hs,
    map_add,CoeffPair.cotangentCoefficients_fst,CoeffPair.cotangentCoefficients_snd]

end NLS.MKdV
