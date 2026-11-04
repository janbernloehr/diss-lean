import NLS.MKdV.MiuraNativeInteriorTranslation

/-! # The independent negative action generator through every finite-gap terminal

Actual norm-continuous spatial translations give simultaneous interior
divisors for the finite open-gap support. Continuity of the actual full
phase Lie derivative extends its checked interior Kronecker value to
every terminal configuration, with closed contributing gaps permitted.
-/
noncomputable section
open Set Complex Filter Topology NLS.LinearVolterra NLS.ZakharovShabat NLS.KdV
namespace NLS.MKdV

@[simp] theorem miuraNativeRealActionFlow_zero (s : ℕ) (a : MiuraRealSobolevSource s) (j : ℕ) :
    miuraNativeRealActionFlow s a j 0 = a := by
  apply Subtype.ext
  exact miuraActionFlow_zero s a.val (fun k => a.property k) j

@[simp] theorem miuraNativeHillActionCurve_zero (s : ℕ) (hs : 1 ≤ s)
    (a : MiuraRealSobolevSource s) (j : ℕ) :
    miuraNativeHillActionCurve s hs a j 0 = miuraNativeHillPotential s hs a := by
  change miuraNativeHillPotential s hs (miuraNativeRealActionFlow s a j 0) = _
  exact congrArg (miuraNativeHillPotential s hs) (miuraNativeRealActionFlow_zero s a j)

theorem miuraNativeHill_halfLength_zero_iff_angular_zero
    (s : ℕ) (hs : 1 ≤ s) (a : MiuraRealSobolevSource s) (n : ℕ) (hn : 1 ≤ n) :
    hillRealGapHalfLength (miuraNativeHillPotential s hs a).val
      (miuraNativeHillPotential s hs a).property.1 (miuraNativeHillPotential s hs a).property.2 n = 0 ↔
      miuraNativeNLSAngularCoordinate s n a = 0 :=
  (realSobolevMiuraHill_halfLength_zero_iff_action_zero _ (miuraNativeH1Profile_real s hs a) n hn).trans
    (miuraNativeH1_action_zero_iff_angular_zero s hs n hn a)

theorem miuraNativeHill_halfLength_spatialTranslation
    (s : ℕ) (hs : 1 ≤ s) (a : MiuraRealSobolevSource s) (τ : ℝ) (n : ℕ) :
    hillRealGapHalfLength (miuraNativeHillPotential s hs (miuraNativeSpatialTranslation s τ a)).val
      (miuraNativeHillPotential s hs (miuraNativeSpatialTranslation s τ a)).property.1
      (miuraNativeHillPotential s hs (miuraNativeSpatialTranslation s τ a)).property.2 n =
    hillRealGapHalfLength (miuraNativeHillPotential s hs a).val
      (miuraNativeHillPotential s hs a).property.1 (miuraNativeHillPotential s hs a).property.2 n :=
  congrFun (hillRealGapHalfLength_eq_of_labels (miuraNativeHillPotential s hs (miuraNativeSpatialTranslation s τ a))
    (miuraNativeHillPotential s hs a) (miuraNativeHillLabels_spatialTranslation s hs τ a)) n

theorem miuraNativeNLSAngularCoordinate_spatialTranslation_ne_zero
    (s : ℕ) (hs : 1 ≤ s) (a : MiuraRealSobolevSource s) (n : ℕ) (hn : 1 ≤ n)
    (ha : miuraNativeNLSAngularCoordinate s n a ≠ 0) (τ : ℝ) :
    miuraNativeNLSAngularCoordinate s n (miuraNativeSpatialTranslation s τ a) ≠ 0 := by
  intro hz
  apply ha
  apply (miuraNativeHill_halfLength_zero_iff_angular_zero s hs a n hn).mp
  rw [← miuraNativeHill_halfLength_spatialTranslation s hs a τ n]
  exact (miuraNativeHill_halfLength_zero_iff_angular_zero s hs _ n hn).mpr hz

theorem miuraNativeOppositeAbelianPhase_Lie_finiteGap
    (s : ℕ) (hs : 1 ≤ s) (a : MiuraRealSobolevSource s) (j : ℕ) (hj : 1 ≤ j)
    (n : ℕ) (hn : 1 ≤ n) (F : Finset ℕ) (hclosed : a ∈ miuraNativeClosedComplement s hs F)
    (hangle : miuraNativeNLSAngularCoordinate s n a ≠ 0) :
    miuraNativeActionLieDerivative s j (miuraNativeOppositeAbelianPhase s hs n hn) a =
      -I*(if j = n then 1 else 0)*miuraNativeOppositeAbelianPhase s hs n hn a := by
  classical
  let G := F.filter (fun k => hillRealGapHalfLength (miuraNativeHillPotential s hs a).val
    (miuraNativeHillPotential s hs a).property.1 (miuraNativeHillPotential s hs a).property.2 (k+1) ≠ 0)
  have hnopen : hillRealGapHalfLength (miuraNativeHillPotential s hs a).val
      (miuraNativeHillPotential s hs a).property.1 (miuraNativeHillPotential s hs a).property.2 n ≠ 0 :=
    fun hz => hangle ((miuraNativeHill_halfLength_zero_iff_angular_zero s hs a n hn).mp hz)
  have hnF : n-1 ∈ F := by
    by_contra hnot
    exact hnopen (by simpa only [Nat.sub_add_cancel hn,miuraNativeHillPotential] using hclosed (n-1) hnot)
  have hnG : n-1 ∈ G := Finset.mem_filter.mpr ⟨hnF,by
    simpa only [Nat.sub_add_cancel hn] using hnopen⟩
  have hG : a ∈ miuraNativeClosedComplement s hs G := by
    intro k hk
    by_cases hkF : k ∈ F
    · by_contra hz
      exact hk (Finset.mem_filter.mpr ⟨hkF,hz⟩)
    · exact hclosed k hkF
  have hgapG : ∀ k ∈ G,hillRealGapHalfLength (miuraNativeHillPotential s hs a).val
      (miuraNativeHillPotential s hs a).property.1 (miuraNativeHillPotential s hs a).property.2 (k+1) ≠ 0 :=
    fun _ hk => (Finset.mem_filter.mp hk).2
  have hR := miuraNativeFiniteDirichletSheets_spatialTranslation_eventually_ne_zero s hs a G hgapG
  have he : ∀ᶠ τ in 𝓝[>] (0:ℝ),
      miuraNativeActionLieDerivative s j (miuraNativeOppositeAbelianPhase s hs n hn) (miuraNativeSpatialTranslation s τ a) =
        -I*(if j = n then 1 else 0)*miuraNativeOppositeAbelianPhase s hs n hn (miuraNativeSpatialTranslation s τ a) := by
    filter_upwards [hR] with τ hτ
    have hc := miuraNativeClosedComplement_spatialTranslation s hs G a hG τ
    have hd := hasDerivAt_miuraNativeOppositeAbelianPhase_actionFlow_finiteGap_generator
      s hs (miuraNativeSpatialTranslation s τ a) j hj n hn G hnG 0
      (fun k hk => by simpa only [miuraNativeHillActionCurve_zero,miuraNativeHillPotential] using hc k hk)
      (by simpa only [miuraNativeHillActionCurve_zero] using hτ)
    simpa only [miuraNativeActionLieDerivative,miuraNativeRealActionFlow_zero] using hd.deriv
  have hmem (τ : ℝ) : miuraNativeSpatialTranslation s τ a ∈
      miuraNativeClosedComplement s hs F ∩ {b | miuraNativeNLSAngularCoordinate s n b ≠ 0} :=
    ⟨miuraNativeClosedComplement_spatialTranslation s hs F a hclosed τ,
      miuraNativeNLSAngularCoordinate_spatialTranslation_ne_zero s hs a n hn hangle τ⟩
  have hL : Continuous (fun τ => miuraNativeActionLieDerivative s j (miuraNativeOppositeAbelianPhase s hs n hn)
      (miuraNativeSpatialTranslation s τ a)) :=
    (continuousOn_miuraNativeOppositeAbelianPhase_Lie_finiteGap s hs j hj n hn F).comp_continuous
      (continuous_miuraNativeSpatialTranslation s a) hmem
  have hQ : Continuous (fun τ => miuraNativeOppositeAbelianPhase s hs n hn (miuraNativeSpatialTranslation s τ a)) :=
    (continuousOn_miuraNativeOppositeAbelianPhase s hs n hn).comp_continuous
      (continuous_miuraNativeSpatialTranslation s a) (fun τ => (hmem τ).2)
  have hRcont : Continuous (fun τ => -I*(if j = n then 1 else 0)*
      miuraNativeOppositeAbelianPhase s hs n hn (miuraNativeSpatialTranslation s τ a)) := continuous_const.mul hQ
  have hlimL := (hL.tendsto 0).mono_left (nhdsWithin_le_nhds (s := Ioi (0:ℝ)))
  have hlimR := (hRcont.tendsto 0).mono_left (nhdsWithin_le_nhds (s := Ioi (0:ℝ)))
  rw [miuraNativeSpatialTranslation_zero] at hlimL hlimR
  exact tendsto_nhds_unique hlimL (hlimR.congr' (Filter.EventuallyEq.symm he))

end NLS.MKdV
