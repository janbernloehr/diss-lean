import NLS.SequenceSpaces.LocalScalarActionDescent
import NLS.SequenceSpaces.ComplexSignInvariance
import NLS.SequenceSpaces.ComplexActionStationarity
import NLS.SequenceSpaces.NonzeroFiniteCenter

/-! # Analytic scalar action factors from actual real-compatible complex germs

The given holomorphic germ agrees with a real action invariant on a complete
real neighborhood. A real projection supplies a complex neighborhood with
pointwise real agreement. The verified scalar action descent then handles
all zero tail actions without choosing a square-root branch there.
-/
noncomputable section
set_option autoImplicit false
open Set Metric Filter Topology
open scoped ENNReal
namespace NLS.Coeff
variable {p q : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ q)] [p.HolderTriple p q]

/-- Every real-compatible holomorphic scalar germ of an action invariant
has a local analytic factor on the half-exponent complex action space. -/
theorem exists_local_scalar_action_factor_of_real_germ
    (hp : p ≠ ⊤) (f : (RealCoeff p × RealCoeff p) → ℂ)
    (hinv : ∀ x y, (∀ n, RealCoeff.pairAction y n = RealCoeff.pairAction x n) → f y = f x)
    (x : RealCoeff p × RealCoeff p) (F : (Coeff p × Coeff p) → ℂ)
    (hF : AnalyticAt ℂ F (((RealCoeff.complexCLM p).prodMap (RealCoeff.complexCLM p)) x))
    (he : (fun y => F (((RealCoeff.complexCLM p).prodMap (RealCoeff.complexCLM p)) y)) =ᶠ[𝓝 x] f) :
    ∃ Z : Set (Coeff p × Coeff p), ∃ T : Set (Coeff q), ∃ g : Coeff q → ℂ,
      IsOpen Z ∧ ((RealCoeff.complexCLM p).prodMap (RealCoeff.complexCLM p)) x ∈ Z ∧
      IsOpen T ∧ quadraticActionsExponent (q := q) '' Z = T ∧ AnalyticOnNhd ℂ g T ∧
      (∀ z ∈ Z, g (quadraticActionsExponent z) = F z) ∧
      ∀ y : RealCoeff p × RealCoeff p,
        ((RealCoeff.complexCLM p).prodMap (RealCoeff.complexCLM p)) y ∈ Z →
        g (quadraticActionsExponent (((RealCoeff.complexCLM p).prodMap (RealCoeff.complexCLM p)) y)) = f y := by
  let J := (RealCoeff.complexCLM p).prodMap (RealCoeff.complexCLM p)
  let P := (Coeff.reCLM p).prodMap (Coeff.reCLM p)
  have hPJ (y : RealCoeff p × RealCoeff p) : P (J y) = y := by
    apply Prod.ext <;> exact RealCoeff.reCLM_complexCLM p _
  have ht : Tendsto P (𝓝 (J x)) (𝓝 x) := by
    simpa only [hPJ] using P.continuous.tendsto (J x)
  have heP : ∀ᶠ z in 𝓝 (J x), F (J (P z)) = f (P z) := ht.eventually he
  obtain ⟨ε,hε,hεball⟩ := Metric.mem_nhds_iff.mp (hF.eventually_analyticAt.and heP)
  let U := ball (J x) ε
  have hFU : AnalyticOnNhd ℂ F U := fun z hz => (hεball hz).1
  have hreal (y : RealCoeff p × RealCoeff p) (hy : J y ∈ U) : F (J y) = f y := by
    simpa only [hPJ] using (hεball hy).2
  obtain ⟨S,r,hr,hbase,hball,hhead⟩ := exists_nonzeroFiniteCenter_ball hp U isOpen_ball (J x) (mem_ball_self hε)
  let c := truncatePair S (J x)
  have hcr : c ∈ realPairLocus p := truncatePair_mem_realPairLocus S (J x)
    ((mem_realPairLocus_iff _).mpr ⟨x,rfl⟩)
  have hFB : AnalyticOnNhd ℂ F (ball c r) := hFU.mono hball
  have hinvB : ∀ z ∈ ball c r, ∀ w ∈ ball c r,
      z ∈ realPairLocus p → w ∈ realPairLocus p →
      (∀ n, w.1 n^2+w.2 n^2 = z.1 n^2+z.2 n^2) → F w = F z := by
    intro z hz w hw hzr hwr heq
    obtain ⟨u,rfl⟩ := (mem_realPairLocus_iff z).mp hzr
    obtain ⟨v,rfl⟩ := (mem_realPairLocus_iff w).mp hwr
    rw [hreal u (hball hz),hreal v (hball hw)]
    apply hinv u v
    intro n
    have hn := heq n
    change (v.1 n:ℂ)^2+(v.2 n:ℂ)^2 = (u.1 n:ℂ)^2+(u.2 n:ℂ)^2 at hn
    have hn' : v.1 n^2+v.2 n^2 = u.1 n^2+u.2 n^2 := by exact_mod_cast hn
    dsimp only [RealCoeff.pairAction]
    rw [hn']
  have hsign : ∀ e d : ℤ → Bool, (∀ n ∈ S, e n = false) → (∀ n ∈ S, d n = false) →
      ∀ z ∈ ball c r, F (pairSignChange e d z) = F z := by
    intro e d heS hdS z hz
    exact eqOn_pairSignChange_of_real_action_invariance F c r hr hcr hFB hinvB e d
      (pairSignChange_truncatePair S (J x) e d heS hdS) hz
  have hrot : ∀ z ∈ ball c r, ∀ k, fderiv ℂ F z (actionRotationVectorCLM p k z) = 0 := by
    intro z hz k
    exact fderiv_actionRotationVector_eq_zero_of_real_action_invariance F (ball c r) isOpen_ball
      (convex_ball c r) c (mem_ball_self hr) hcr hFB hinvB z hz k
  obtain ⟨Z,T,g,hZ,hx,hZB,hT,himage,hg,hrec⟩ := exists_local_scalar_action_factor
    (q := q) hp S F (ball c r) isOpen_ball hFB hsign hrot (J x) hbase hhead
  exact ⟨Z,T,g,hZ,hx,hT,himage,hg,hrec,
    fun y hy => (hrec (J y) hy).trans (hreal y (hball (hZB hy)))⟩

end NLS.Coeff
