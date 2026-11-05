import NLS.KdV.HillPeriodOneRestriction
import NLS.KdV.HillGeneralKernelCorrections

noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology MeasureTheory
open NLS.ComplexAnalysis NLS.ZakharovShabat
open scoped ENNReal ComplexConjugate Classical

namespace NLS.KdV



def hillEvenCoefficientMap : WeightedCoeff SpectralWeight.one.toWeight 2 →L[ℂ] Coeff 2 :=
  (Coeff.parityProjection 0).comp SpectralWeight.one.toCoeff

theorem hillEvenCoefficientMap_even (p : RealPeriodOneHillPotential) :
    hillEvenCoefficientMap p.val=SpectralWeight.one.toCoeff p.val :=
  (Coeff.parityProjection_eq_self_iff 0 _).mpr p.property.1

private theorem linear_norm_domain_open
    {E F : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [NormedAddCommGroup F] [NormedSpace ℂ F]
    (T : E →L[ℂ] F) (U : Set F) (hU : IsOpen U) (L : ℝ) :
    IsOpen {x : E | T x∈U ∧ ‖x‖<L} :=
  (hU.preimage T.continuous).inter (isOpen_lt continuous_norm continuous_const)

private theorem analytic_linear_norm_pullback
    {E F : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [NormedAddCommGroup F] [NormedSpace ℂ F]
    (T : E →L[ℂ] F) (f : F → ℂ) (U : Set F) (hf : AnalyticOnNhd ℂ f U) (L : ℝ) :
    AnalyticOnNhd ℂ (fun x : E => f (T x)) {x : E | T x∈U ∧ ‖x‖<L} := by
  intro x hx
  exact (hf _ hx.1).comp (T.analyticAt x)

def hillProjectedSourceDomain (p0 : Coeff 2) (δ L : ℝ) : Set (WeightedCoeff SpectralWeight.one.toWeight 2) :=
  {p | hillEvenCoefficientMap p∈ball p0 δ ∧ ‖p‖<L}

theorem isOpen_hillProjectedSourceDomain (p0 : Coeff 2) (δ L : ℝ) :
    IsOpen (hillProjectedSourceDomain p0 δ L) :=
  linear_norm_domain_open hillEvenCoefficientMap (ball p0 δ) isOpen_ball L

theorem mem_hillProjectedSourceDomain_base (q : WeightedCoeff SpectralWeight.one.toWeight 2)
    (hq : SpectralWeight.one.toCoeff q∈Coeff.paritySubspace 0) (δ L : ℝ) (hδ : 0<δ) (hL : ‖q‖<L) :
    q∈hillProjectedSourceDomain (SpectralWeight.one.toCoeff q) δ L := by
  refine ⟨?_,hL⟩
  change Coeff.parityProjection 0 (SpectralWeight.one.toCoeff q)∈ball (SpectralWeight.one.toCoeff q) δ
  rw [(Coeff.parityProjection_eq_self_iff 0 _).mpr hq]
  exact mem_ball_self hδ

theorem analyticOnNhd_hillProjectedSource_pullback (f : Coeff 2 → ℂ) (p0 : Coeff 2) (δ L : ℝ)
    (hf : AnalyticOnNhd ℂ f (ball p0 δ)) :
    AnalyticOnNhd ℂ (fun p : WeightedCoeff SpectralWeight.one.toWeight 2 => f (hillEvenCoefficientMap p))
      (hillProjectedSourceDomain p0 δ L) :=
  analytic_linear_norm_pullback hillEvenCoefficientMap f (ball p0 δ) hf L

private theorem projected_kernel_bound
    (γ : ℕ → Coeff 2 → ℂ) (p0 : Coeff 2) (δ L M : ℝ) (n : ℕ)
    (hb : ∀ r : WeightedCoeff SpectralWeight.one.doubleIndex.toWeight 2, ‖r‖≤L →
      hillPeriodOneCoefficientMap SpectralWeight.one r∈ball p0 δ →
      ∀ k : ℕ, ‖γ k (hillPeriodOneCoefficientMap SpectralWeight.one r)‖≤M*hillOffDiagonalPeriodKernel n (k : ℤ))
    (p : WeightedCoeff SpectralWeight.one.toWeight 2)
    (hp : hillEvenCoefficientMap p∈ball p0 δ ∧ ‖p‖<L) (j : ℕ) :
    ‖γ (j+1) (hillEvenCoefficientMap p)‖≤M*hillOffDiagonalPeriodKernel n ((j+1 : ℕ) : ℤ) := by
  have hmap : hillPeriodOneCoefficientMap SpectralWeight.one (hillPeriodOneRestriction SpectralWeight.one p)=hillEvenCoefficientMap p :=
    hillPeriodOneCoefficientMap_restriction SpectralWeight.one p
  have hh := hb (hillPeriodOneRestriction SpectralWeight.one p)
    ((norm_hillPeriodOneRestriction_le _ p).trans hp.2.le) (by rw [hmap];exact hp.1) (j+1)
  rw [hmap] at hh
  exact hh

private theorem projected_charts_from_native
    (q : WeightedCoeff SpectralWeight.one.toWeight 2)
    (hq : SpectralWeight.one.toCoeff q∈Coeff.paritySubspace 0)
    (hr : IsRealHillPotential (SpectralWeight.one.toCoeff q))
    (n N : ℕ) (hn : 1≤n) (hN : 1≤N) (L δ M : ℝ) (hδ : 0<δ) (_hM : 0<M) (hqL : ‖q‖<L)
    (W : Set RealPeriodOneHillPotential) (hW : IsOpen W) (hqW : (⟨q,hq,hr⟩ : RealPeriodOneHillPotential)∈W)
    (γ : ℕ → Coeff 2 → ℂ)
    (hγa : ∀ k : ℕ, AnalyticOnNhd ℂ (γ k) (ball (SpectralWeight.one.toCoeff q) δ))
    (hγzero : ∀ k : ℕ, ¬(N≤k ∧ k≠n) → γ k=0)
    (hγb : ∀ r : WeightedCoeff SpectralWeight.one.doubleIndex.toWeight 2, ‖r‖≤L →
      hillPeriodOneCoefficientMap SpectralWeight.one r∈ball (SpectralWeight.one.toCoeff q) δ →
      ∀ k : ℕ, ‖γ k (hillPeriodOneCoefficientMap SpectralWeight.one r)‖≤M*hillOffDiagonalPeriodKernel n (k : ℤ))
    (hγreal : ∀ p∈W, ∀ k : ℕ, ∀ hk : N≤k, k≠n → γ k (SpectralWeight.one.toCoeff p.val)=
      hillRegularAbelianCorrection p.val p.property.1 p.property.2 n hn k (hN.trans hk)) :
    ∃ U : Set (WeightedCoeff SpectralWeight.one.toWeight 2), ∃ V : Set RealPeriodOneHillPotential,
      IsOpen U ∧ q∈U ∧ IsOpen V ∧ (⟨q,hq,hr⟩ : RealPeriodOneHillPotential)∈V ∧
      (∀ p∈V, p.val∈U) ∧ ∃ β : ℕ → WeightedCoeff SpectralWeight.one.toWeight 2 → ℂ,
        (∀ j : ℕ, AnalyticOnNhd ℂ (β j) U) ∧
        (∀ j : ℕ, ¬(N≤j+1 ∧ j+1≠n) → β j=0) ∧
        (∀ j : ℕ, ∀ p∈U, ‖β j p‖≤M*hillOffDiagonalPeriodKernel n ((j+1 : ℕ) : ℤ)) ∧
        ∀ p∈V, ∀ j : ℕ, ∀ _hj : N≤j+1, j+1≠n → β j p.val=
          hillRegularAbelianCorrection p.val p.property.1 p.property.2 n hn (j+1) (by omega) := by
  let U := hillProjectedSourceDomain (SpectralWeight.one.toCoeff q) δ L
  have hU : IsOpen U := isOpen_hillProjectedSourceDomain _ δ L
  have hqU : q∈U := mem_hillProjectedSourceDomain_base q hq δ L hδ hqL
  let V := W ∩ (Subtype.val : RealPeriodOneHillPotential → WeightedCoeff SpectralWeight.one.toWeight 2) ⁻¹' U
  let β : ℕ → WeightedCoeff SpectralWeight.one.toWeight 2 → ℂ := fun j p => γ (j+1) (hillEvenCoefficientMap p)
  refine ⟨U,V,hU,hqU,hW.inter (hU.preimage continuous_subtype_val),⟨hqW,hqU⟩,
    (fun p hp => hp.2),β,?_,?_,?_,?_⟩
  · intro j p hp
    exact analyticOnNhd_hillProjectedSource_pullback (γ (j+1)) _ δ L (hγa (j+1)) p hp
  · intro j hj
    funext p
    exact congrFun (hγzero (j+1) hj) _
  · intro j p hp
    exact projected_kernel_bound γ (SpectralWeight.one.toCoeff q) δ L M n hγb p hp j
  · intro p hp j hj hjn
    change γ (j+1) (hillEvenCoefficientMap p.val)=_
    rw [hillEvenCoefficientMap_even p]
    exact hγreal p hp.1 (j+1) hj hjn

variable (q : WeightedCoeff SpectralWeight.one.toWeight 2)
    (hq : SpectralWeight.one.toCoeff q∈Coeff.paritySubspace 0)
    (hr : IsRealHillPotential (SpectralWeight.one.toCoeff q))
    (h0q : SpectralWeight.one.toCoeff (0 : WeightedCoeff SpectralWeight.one.toWeight 2)∈Coeff.paritySubspace 0)
    (h0r : IsRealHillPotential (SpectralWeight.one.toCoeff (0 : WeightedCoeff SpectralWeight.one.toWeight 2)))
include h0q h0r

/-- On a common open source domain, the actual high off-diagonal
corrections form a normally bounded analytic series in the original
weighted Hill space, without an inverse native-coordinate hypothesis. -/
theorem exists_hillHighRegularCorrection_weightOne_normal_charts (n : ℕ) (hn : 1≤n) :
    ∃ U : Set (WeightedCoeff SpectralWeight.one.toWeight 2), ∃ V : Set RealPeriodOneHillPotential,
      ∃ N : ℕ, ∃ M : ℝ, IsOpen U ∧ q∈U ∧ IsOpen V ∧ (⟨q,hq,hr⟩ : RealPeriodOneHillPotential)∈V ∧
      1≤N ∧ 0<M ∧ (∀ p∈V, p.val∈U) ∧ ∃ β : ℕ → WeightedCoeff SpectralWeight.one.toWeight 2 → ℂ,
        (∀ j : ℕ, AnalyticOnNhd ℂ (β j) U) ∧
        (∀ j : ℕ, ¬(N≤j+1 ∧ j+1≠n) → β j=0) ∧
        (∀ j : ℕ, ∀ p∈U, ‖β j p‖≤M*hillOffDiagonalPeriodKernel n ((j+1 : ℕ) : ℤ)) ∧
        ∀ p∈V, ∀ j : ℕ, ∀ _hj : N≤j+1, j+1≠n → β j p.val=
          hillRegularAbelianCorrection p.val p.property.1 p.property.2 n hn (j+1) (by omega) := by
  let L := ‖q‖+1
  obtain ⟨δ,M,N,W,hδ,hM,hN,hW,hqW,_,hcharts⟩ :=
    exists_hillRegularAbelianCorrection_general_native_kernel_charts q hq hr h0q h0r L (by dsimp only [L];positivity)
  obtain ⟨γ,hγa,hγzero,hγb,hγreal⟩ := hcharts n hn
  obtain ⟨U,V,hU,hqU,hV,hqV,hsource,β,hβ,hzero,hbound,hreal⟩ :=
    projected_charts_from_native q hq hr n N hn hN L δ M hδ hM (by dsimp only [L];linarith)
      W hW hqW γ hγa hγzero (hγb SpectralWeight.one) hγreal
  exact ⟨U,V,N,M,hU,hqU,hV,hqV,hN,hM,hsource,β,hβ,hzero,hbound,hreal⟩

end NLS.KdV
