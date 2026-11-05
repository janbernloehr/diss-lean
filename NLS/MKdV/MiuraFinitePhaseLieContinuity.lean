import NLS.MKdV.MiuraNativeAnalyticLieDerivative
import NLS.MKdV.MiuraOppositeAbelianPhase

/-! # Actual finite Abelian phase Lie derivatives are continuous through terminals

The finite phase's independent local complex extension is pulled back to
native Sobolev sources. Its actual action Lie derivative consequently has
its own local holomorphic extension, with no interior-sheet assumption.
-/
noncomputable section
open Set Complex Filter Topology NLS.KdV NLS.ZakharovShabat
open scoped ComplexConjugate
namespace NLS.MKdV

def miuraNativeFiniteAbelianPhase (s : ℕ) (hs : 1 ≤ s) (n : ℕ) (hn : 1 ≤ n)
    (F : Finset ℕ) (a : MiuraRealSobolevSource s) : ℂ :=
  miuraFiniteAbelianPhase (hierarchySobolevToScalarDomain s hs a.val) (miuraNativeH1Profile_real s hs a) n hn F

theorem exists_miuraNativeFiniteAbelianPhase_analytic_extension
    (s : ℕ) (hs : 1 ≤ s) (n : ℕ) (hn : 1 ≤ n) (F : Finset ℕ)
    (a : MiuraRealSobolevSource s) (ha : miuraNativeNLSAngularCoordinate s n a ≠ 0) :
    ∃ P : ScalarSobolev s → ℂ,AnalyticAt ℂ P a.val ∧
      ∀ᶠ b : MiuraRealSobolevSource s in 𝓝 a,P b.val = miuraNativeFiniteAbelianPhase s hs n hn F b := by
  let H := hierarchySobolevToScalarDomain s hs
  have hJ : miuraMKdVAction (H a.val) (miuraNativeH1Profile_real s hs a) n ≠ 0 :=
    fun h => ha ((miuraNativeH1_action_zero_iff_angular_zero s hs n hn a).mp h)
  obtain ⟨P,hP,_,hm⟩ := exists_miuraFiniteAbelianPhase_analytic_extension_along_real_family
    (H a.val) (miuraNativeH1Profile_real s hs a) n hn hJ F
    (fun b : MiuraRealSobolevSource s => H b.val) (H.continuous.comp continuous_subtype_val)
    (fun b => miuraNativeH1Profile_real s hs b) a rfl
  exact ⟨fun b => P (H b),hP.comp (H.analyticAt a.val),hm⟩

theorem exists_miuraNativeFiniteAbelianPhase_Lie_analytic_extension
    (s : ℕ) (hs : 1 ≤ s) (j : ℕ) (hj : 1 ≤ j)
    (n : ℕ) (hn : 1 ≤ n) (F : Finset ℕ)
    (a : MiuraRealSobolevSource s) (ha : miuraNativeNLSAngularCoordinate s n a ≠ 0) :
    ∃ L : ScalarSobolev s → ℂ,AnalyticAt ℂ L a.val ∧
      ∀ᶠ b : MiuraRealSobolevSource s in 𝓝 a,L b.val =
        miuraNativeActionLieDerivative s j (miuraNativeFiniteAbelianPhase s hs n hn F) b := by
  obtain ⟨P,hP,hm⟩ := exists_miuraNativeFiniteAbelianPhase_analytic_extension s hs n hn F a ha
  exact exists_miuraNativeActionLieDerivative_analytic_extension s hs j hj _ a P hP hm

theorem continuousOn_miuraNativeFiniteAbelianPhase_Lie
    (s : ℕ) (hs : 1 ≤ s) (j : ℕ) (hj : 1 ≤ j) (n : ℕ) (hn : 1 ≤ n) (F : Finset ℕ) :
    ContinuousOn (miuraNativeActionLieDerivative s j (miuraNativeFiniteAbelianPhase s hs n hn F))
      {a | miuraNativeNLSAngularCoordinate s n a ≠ 0} := by
  intro a ha
  obtain ⟨P,hP,hm⟩ := exists_miuraNativeFiniteAbelianPhase_analytic_extension s hs n hn F a ha
  exact (continuousAt_miuraNativeActionLieDerivative_of_analytic_extension s hs j hj _ a P hP hm).continuousWithinAt

end NLS.MKdV
