import NLS.MKdV.MiuraNativeSpatialTranslation
import NLS.MKdV.QuasiHillTerminalTranslation
import NLS.KdV.HillOpenEndpointTraceDerivative

/-! # Terminal-continuation ingredients for the independent full phase

Actual full-phase action Lie derivatives are continuous on each fixed
finite-gap stratum, which actual spatial translation preserves. The
independent quasi-Hill IVP gives terminal release under its explicitly
stated nontrivial parabolic hypothesis; each actual open Hill endpoint
has nonzero energy trace derivative. Establishing the remaining endpoint
monodromy and translation identifications, then full rotation, is separate.
-/
noncomputable section
open Set Metric Complex Matrix Filter Topology NLS.LinearVolterra NLS.KdV NLS.MKdV NLS.ZakharovShabat
open scoped ENNReal ComplexConjugate
namespace NLS.Articles.MKdVNLSHierarchies

theorem independent_full_phase_finite_gap_Lie_continuity
    (s : ℕ) (hs : 1 ≤ s) (j : ℕ) (hj : 1 ≤ j) (n : ℕ) (hn : 1 ≤ n) (F : Finset ℕ) :
    ContinuousOn (miuraNativeActionLieDerivative s j (miuraNativeOppositeAbelianPhase s hs n hn))
      (miuraNativeClosedComplement s hs F ∩ {a | miuraNativeNLSAngularCoordinate s n a ≠ 0}) :=
  continuousOn_miuraNativeOppositeAbelianPhase_Lie_finiteGap s hs j hj n hn F

theorem independent_finite_gap_stratum_spatial_translation (s : ℕ) (hs : 1 ≤ s)
    (F : Finset ℕ) (a : MiuraRealSobolevSource s) (ha : a ∈ miuraNativeClosedComplement s hs F) (t : ℝ) :
    miuraNativeSpatialTranslation s t a ∈ miuraNativeClosedComplement s hs F :=
  miuraNativeClosedComplement_spatialTranslation s hs F a ha t

theorem independent_quasi_Hill_terminal_release
    (U : C(ℝ,ℂ)) (hp : Function.Periodic U 1) (z : ℂ) (hz : z ≠ 0) (ε c : ℂ) (hc : c ≠ 0)
    (hpar : quasiHillFundamentalMatrix (periodicScalarProfileUnitCurve U) (z^2) 1 = !![ε,0;c,ε]) :
    ∀ᶠ τ in 𝓝[>] (0:ℝ),
      quasiHillDirichletCharacteristic (periodicScalarProfileUnitCurve (periodicScalarProfileTranslate U τ)) (z^2) ≠ 0 :=
  quasiHillDirichletCharacteristic_translate_parabolic_eventually_ne_zero U hp z hz ε c hc hpar

theorem independent_Hill_open_endpoint_trace_derivative
    (q : WeightedCoeff SpectralWeight.one.toWeight 2)
    (hq : SpectralWeight.one.toCoeff q ∈ Coeff.paritySubspace 0)
    (hr : IsRealHillPotential (SpectralWeight.one.toCoeff q)) (k : ℕ) (hk : 1 ≤ k)
    (hgap : hillRealGapHalfLength q hq hr k ≠ 0) (E : ℂ)
    (hE : E = (hillRealLabels q hq hr (2*k-1) : ℂ) ∨ E = (hillRealLabels q hq hr (2*k) : ℂ)) :
    deriv (hillL2Discriminant (SpectralWeight.one.toCoeff q)) E ≠ 0 :=
  deriv_hillL2Discriminant_ne_zero_open_gap_endpoint q hq hr k hk hgap E hE

end NLS.Articles.MKdVNLSHierarchies
