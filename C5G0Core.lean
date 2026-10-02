import YangMills.RG.NeumannImageRectangleCoverage

namespace YangMills.RG

open scoped BigOperators

noncomputable section

def cmp89CountingDeltaCore {d : ℕ}
    (target source : Fin d → ℤ) : ℝ :=
  if target = source then 1 else 0

@[simp] theorem neumannReflectionImage_identity_core
    {d : ℕ} (m : Fin d → ℤ)
    (n : CMP89SourceNeumannIntegerRectanglePoint m) :
    cmp89NeumannReflectionImage m n.1 (0 : Fin d → ℤ)
        (fun _ => false) =
      n.1 := by
  funext mu
  simp [cmp89NeumannReflectionImage, cmp89NeumannReflectionOrbit]

theorem neumannReflectionImage_eq_rectanglePoint_iff_identity_core
    {d : ℕ}
    (m : Fin d → ℤ)
    (hm : ∀ mu, 0 < m mu)
    (x n : CMP89SourceNeumannIntegerRectanglePoint m)
    (k : Fin d → ℤ)
    (b : CMP89NeumannReflectionBranch d) :
    cmp89NeumannReflectionImage m n.1 k b = x.1 ↔
      k = 0 ∧ b = (fun _ => false) ∧ n = x := by
  constructor
  · intro h
    have hfull :
        ((k, b, n) :
          (Fin d → ℤ) × CMP89NeumannReflectionBranch d ×
            CMP89SourceNeumannIntegerRectanglePoint m) =
        (0, (fun _ => false), x) := by
      apply (neumannImageRectangleFamily_bijective m hm).1
      change cmp89NeumannReflectionImage m n.1 k b =
        cmp89NeumannReflectionImage m x.1 0 (fun _ => false)
      rw [neumannReflectionImage_identity_core]
      exact h
    exact ⟨congrArg (fun p => p.1) hfull,
      congrArg (fun p => p.2.1) hfull,
      congrArg (fun p => p.2.2) hfull⟩
  · rintro ⟨rfl, rfl, rfl⟩
    simp only [neumannReflectionImage_identity_core]

theorem cmp89NeumannReflectionSeries_countingDelta_core
    {d : ℕ}
    (m : Fin d → ℤ)
    (hm : ∀ mu, 0 < m mu)
    (x n : CMP89SourceNeumannIntegerRectanglePoint m) :
    cmp89NeumannReflectionSeries cmp89CountingDeltaCore m x.1 n.1 =
      if x = n then 1 else 0 := by
  classical
  unfold cmp89NeumannReflectionSeries
  by_cases hxn : x = n
  · subst n
    rw [if_pos rfl]
    rw [tsum_eq_single (0 : Fin d → ℤ)]
    · rw [Finset.sum_eq_single (fun _ => false)]
      · simp [cmp89CountingDeltaCore, neumannReflectionImage_identity_core]
      · intro b _ hne
        have himage :
            cmp89NeumannReflectionImage m x.1 0 b ≠ x.1 := by
          intro h
          have hiff :=
            (neumannReflectionImage_eq_rectanglePoint_iff_identity_core
              m hm x x 0 b).1 h
          exact hne hiff.2.1
        have hximage :
            x.1 ≠ cmp89NeumannReflectionImage m x.1 0 b :=
          fun h => himage h.symm
        simp [cmp89CountingDeltaCore, hximage]
      · simp
    · intro k hk
      apply Finset.sum_eq_zero
      intro b _
      have himage :
          cmp89NeumannReflectionImage m x.1 k b ≠ x.1 := by
        intro h
        have hiff :=
          (neumannReflectionImage_eq_rectanglePoint_iff_identity_core
            m hm x x k b).1 h
        exact hk hiff.1
      have hximage :
          x.1 ≠ cmp89NeumannReflectionImage m x.1 k b :=
        fun h => himage h.symm
      simp [cmp89CountingDeltaCore, hximage]
  · rw [if_neg hxn]
    have hzero :
        (fun k : Fin d → ℤ =>
          ∑ b : CMP89NeumannReflectionBranch d,
            cmp89CountingDeltaCore x.1
              (cmp89NeumannReflectionImage m n.1 k b)) = 0 := by
      funext k
      apply Finset.sum_eq_zero
      intro b _
      have himage :
          x.1 ≠ cmp89NeumannReflectionImage m n.1 k b := by
        intro h
        have hiff :=
          (neumannReflectionImage_eq_rectanglePoint_iff_identity_core
            m hm x n k b).1 h.symm
        exact hxn hiff.2.2.symm
      simp [cmp89CountingDeltaCore, himage]
    rw [hzero]
    exact tsum_zero

end

end YangMills.RG
