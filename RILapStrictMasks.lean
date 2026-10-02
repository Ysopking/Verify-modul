import YangMills.RG.NeumannRectangleDirectionalMasks

namespace YangMills.RG

noncomputable section

/-- Under strict rectangle fit, the outgoing Neumann bond mask has no torus-wrap branch. -/
theorem neumannRectangle_outgoingBond_iff_strict_reconstruct
    {N : ℕ} [NeZero N] {m : Fin 4 → ℤ}
    (hm : ∀ mu, 0 < m mu)
    (hfit : ∀ mu, m mu < (N : ℤ))
    (x : ActiveGaugeRegion.Site
      (cmp89SourceNeumannRectangleActiveRegion (N := N) m))
    (i : Fin 4) :
    (x.1, i) ∈ (cmp89SourceNeumannRectangleActiveRegion (N := N) m).bonds ↔
      (x.1 i).val + 1 < Int.toNat (m i) := by
  have hfitLe : ∀ mu, m mu ≤ (N : ℤ) := fun mu => (hfit mu).le
  rw [neumannRectangle_outgoingBond_iff hm hfitLe x i]
  have hm0 : 0 ≤ m i := (hm i).le
  have hnat : Int.toNat (m i) < N := by
    exact_mod_cast (show (Int.toNat (m i) : ℤ) < (N : ℤ) by
      rw [Int.toNat_of_nonneg hm0]
      exact hfit i)
  have hne : Int.toNat (m i) ≠ N := ne_of_lt hnat
  simp [hne]

/-- Under strict rectangle fit, the incoming Neumann bond mask has no torus-wrap branch. -/
theorem neumannRectangle_incomingBond_iff_strict_reconstruct
    {N : ℕ} [NeZero N] {m : Fin 4 → ℤ}
    (hm : ∀ mu, 0 < m mu)
    (hfit : ∀ mu, m mu < (N : ℤ))
    (x : ActiveGaugeRegion.Site
      (cmp89SourceNeumannRectangleActiveRegion (N := N) m))
    (i : Fin 4) :
    (x.1.shiftBack i, i) ∈
        (cmp89SourceNeumannRectangleActiveRegion (N := N) m).bonds ↔
      0 < (x.1 i).val := by
  have hfitLe : ∀ mu, m mu ≤ (N : ℤ) := fun mu => (hfit mu).le
  rw [neumannRectangle_incomingBond_iff hm hfitLe x i]
  have hm0 : 0 ≤ m i := (hm i).le
  have hnat : Int.toNat (m i) < N := by
    exact_mod_cast (show (Int.toNat (m i) : ℤ) < (N : ℤ) by
      rw [Int.toNat_of_nonneg hm0]
      exact hfit i)
  have hne : Int.toNat (m i) ≠ N := ne_of_lt hnat
  simp [hne]

end

end YangMills.RG
