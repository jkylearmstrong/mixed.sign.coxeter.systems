/-
Copyright (c) 2026 Johnathon Kyle Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import MixedSignCoxeter.EvenCycleSingleDefect

/-!
# Bipartite Sign-Flip Duality

For any reflection system `(W, S, B)` on `Fin n` and any sign assignment
`ε : Fin n → ℝ` with `ε i ^ 2 = 1`:

1. **General conjugation (`principalElement_bipartiteSignFlip`)**:
   Replacing `B` by `bipartiteSignFlip B ε := -(diagonal ε * B * diagonal ε)`
   conjugates the principal element `w = s_0 s_1 ... s_{n-1}` by `D = diagonal ε`:
   `principalElement (bipartiteSignFlipSystem S ε hε) = D * principalElement S * D`.
2. **Bipartite sign-flip duality (`bipartiteSignFlip_preserves_offdiag`)**:
   When `ε` is a proper 2-coloring of the support graph of `B`
   (`i ≠ j → B i j ≠ 0 → ε i * ε j = -1`), `bipartiteSignFlip B ε` has the exact
   same off-diagonal entries as `B` and negated diagonal entries (`-B i i`).
   Hence on any bipartite graph, flipping all vertex signs preserves the
   characteristic polynomial `det (μ • 1 - w)`, all eigenvalues, and the spectral radius.
3. **Application to `C_{2m}(-, +, ..., +)` (`evenCycleSingleMinus_has_eigenvalue_lt_neg_one`)**:
   Since `C_{2m}` (`m ≥ 2`) is bipartite, `C_{2m}(-, +, ..., +)` is sign-flip dual to
   `C_{2m}(+, -, ..., -)` (`EvenCycleSingleDefect.lean`), so it likewise has a real
   eigenvalue `μ ∈ (-5, -1)` and spectral radius `ρ(w) > 1`.
-/

open Matrix BigOperators

namespace ReflectionSystem

section BipartiteDuality

variable {n : ℕ}

/-- Sign-flipped bilinear form `-(D * B * D)` where `D = diagonal ε`. -/
noncomputable def bipartiteSignFlip (B : Matrix (Fin n) (Fin n) ℝ) (ε : Fin n → ℝ) :
    Matrix (Fin n) (Fin n) ℝ :=
  -(diagonal ε * B * diagonal ε)

lemma bipartiteSignFlip_apply (B : Matrix (Fin n) (Fin n) ℝ) (ε : Fin n → ℝ) (i j : Fin n) :
    bipartiteSignFlip B ε i j = -(ε i * B i j * ε j) := by
  simp [bipartiteSignFlip, Matrix.mul_assoc]; ring

lemma bipartiteSignFlip_diag (B : Matrix (Fin n) (Fin n) ℝ) (ε : Fin n → ℝ)
    (hε : ∀ i, ε i ^ 2 = 1) (i : Fin n) :
    bipartiteSignFlip B ε i i = -(B i i) := by
  rw [bipartiteSignFlip_apply]
  have hi : ε i * ε i = 1 := by simpa [sq] using hε i
  calc -(ε i * B i i * ε i) = -((ε i * ε i) * B i i) := by ring
    _ = -(B i i) := by rw [hi, one_mul]

/-- When `ε` is a proper 2-coloring of the off-diagonal support of `B`,
`bipartiteSignFlip B ε` preserves all off-diagonal entries of `B`. -/
lemma bipartiteSignFlip_offdiag (B : Matrix (Fin n) (Fin n) ℝ) (ε : Fin n → ℝ)
    (hbip : ∀ i j : Fin n, i ≠ j → B i j ≠ 0 → ε i * ε j = -1)
    {i j : Fin n} (hij : i ≠ j) :
    bipartiteSignFlip B ε i j = B i j := by
  rw [bipartiteSignFlip_apply]
  by_cases h0 : B i j = 0
  · simp [h0]
  · have hε : ε i * ε j = -1 := hbip i j hij h0
    calc -(ε i * B i j * ε j) = -((ε i * ε j) * B i j) := by ring
      _ = B i j := by rw [hε]; ring

/-- The sign-flipped reflection system `-(D * S.B * D)`. -/
noncomputable def bipartiteSignFlipSystem (S : ReflectionSystem n) (ε : Fin n → ℝ)
    (hε : ∀ i, ε i ^ 2 = 1) : ReflectionSystem n where
  B := bipartiteSignFlip S.B ε
  B_symm := by
    ext i j
    simp only [transpose_apply, bipartiteSignFlip_apply]
    rw [S.B_symm.apply i j]
    ring
  B_diag_ne_zero := by
    intro i
    rw [bipartiteSignFlip_diag S.B ε hε i]
    exact neg_ne_zero.mpr (S.B_diag_ne_zero i)

lemma diagonal_sq_eq_one (ε : Fin n → ℝ) (hε : ∀ i, ε i ^ 2 = 1) :
    diagonal ε * diagonal ε = 1 := by
  ext i j
  by_cases hij : i = j
  · subst hij
    simpa [sq] using hε i
  · simp [hij]

lemma reflectionMatrix_bipartiteSignFlip (S : ReflectionSystem n) (ε : Fin n → ℝ)
    (hε : ∀ i, ε i ^ 2 = 1) (i : Fin n) :
    reflectionMatrix (bipartiteSignFlip S.B ε) i =
      diagonal ε * reflectionMatrix S.B i * diagonal ε := by
  unfold bipartiteSignFlip
  rw [reflectionMatrix_neg]
  have hB : S.B i i ≠ 0 := S.B_diag_ne_zero i
  have hεi : ε i * ε i = 1 := by simpa [sq] using hε i
  have hεi_ne : ε i ≠ 0 := fun h => by simp [h] at hεi
  ext r c
  simp only [reflectionMatrix_apply, Matrix.mul_apply, diagonal_apply]
  simp only [ite_mul, zero_mul, mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ,
    ↓reduceIte, Finset.sum_ite_eq]
  by_cases hrc : r = c <;> by_cases hri : r = i
  · subst hrc hri
    simp only [↓reduceIte]
    field_simp [hB, hεi_ne]
    exact (hε r).symm
  · subst hrc
    have hr : ε r * ε r = 1 := by simpa [sq] using hε r
    simp [hri, hr]
  · subst hri
    simp only [↓reduceIte, hrc]
    field_simp [hB, hεi_ne]
    rw [hε r]
    ring
  · simp [hrc, hri]

lemma prefixProd_bipartiteSignFlip (S : ReflectionSystem n) (ε : Fin n → ℝ)
    (hε : ∀ i, ε i ^ 2 = 1) (k : ℕ) :
    prefixProd (bipartiteSignFlip S.B ε) k = diagonal ε * prefixProd S.B k * diagonal ε := by
  have hD : diagonal ε * diagonal ε = 1 := diagonal_sq_eq_one ε hε
  induction k with
  | zero =>
    simp [prefixProd, hD]
  | succ k ih =>
    by_cases hk : k < n
    · simp only [prefixProd, hk, ↓reduceDIte]
      rw [ih, reflectionMatrix_bipartiteSignFlip S ε hε ⟨k, hk⟩]
      calc (diagonal ε * prefixProd S.B k * diagonal ε) *
            (diagonal ε * reflectionMatrix S.B ⟨k, hk⟩ * diagonal ε)
          = diagonal ε * prefixProd S.B k * (diagonal ε * diagonal ε) *
              reflectionMatrix S.B ⟨k, hk⟩ * diagonal ε := by simp only [Matrix.mul_assoc]
        _ = diagonal ε * (prefixProd S.B k * reflectionMatrix S.B ⟨k, hk⟩) * diagonal ε := by
            rw [hD, Matrix.mul_one]
            simp only [Matrix.mul_assoc]
    · simp only [prefixProd, hk, ↓reduceDIte]
      exact ih

/-- **Bipartite Sign-Flip Conjugation**:
The principal element of `bipartiteSignFlipSystem S ε hε` is conjugate to
`principalElement S` via the involution `D = diagonal ε`. -/
theorem principalElement_bipartiteSignFlip (S : ReflectionSystem n) (ε : Fin n → ℝ)
    (hε : ∀ i, ε i ^ 2 = 1) :
    principalElement (bipartiteSignFlipSystem S ε hε) =
      diagonal ε * principalElement S * diagonal ε :=
  prefixProd_bipartiteSignFlip S ε hε n

/-- **Bipartite Sign-Flip Characteristic Polynomial Invariance**:
For every `μ : ℝ`, `det (μ • 1 - w') = det (μ • 1 - w)`. -/
theorem charpoly_eval_bipartiteSignFlip (S : ReflectionSystem n) (ε : Fin n → ℝ)
    (hε : ∀ i, ε i ^ 2 = 1) (μ : ℝ) :
    (μ • (1 : Matrix (Fin n) (Fin n) ℝ) -
      principalElement (bipartiteSignFlipSystem S ε hε)).det =
      (μ • (1 : Matrix (Fin n) (Fin n) ℝ) - principalElement S).det := by
  have hD : diagonal ε * diagonal ε = 1 := diagonal_sq_eq_one ε hε
  rw [principalElement_bipartiteSignFlip S ε hε]
  have hconj :
      μ • (1 : Matrix (Fin n) (Fin n) ℝ) - diagonal ε * principalElement S * diagonal ε =
        diagonal ε * (μ • 1 - principalElement S) * diagonal ε := by
    simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one, hD]
  rw [hconj, Matrix.det_mul, Matrix.det_mul]
  have hdetD : (diagonal ε).det * (diagonal ε).det = 1 := by
    rw [← Matrix.det_mul, hD, Matrix.det_one]
  calc ((diagonal ε).det * (μ • 1 - principalElement S).det) * (diagonal ε).det
      = ((diagonal ε).det * (diagonal ε).det) * (μ • 1 - principalElement S).det := by ring
    _ = (μ • 1 - principalElement S).det := by rw [hdetD, one_mul]

end BipartiteDuality

section EvenCycleSingleMinus

open MixedSignCoxeter

/-- Bilinear form for `C_{2m}(-, +, ..., +)`: vertex `0` is negative (`-2`),
vertices `1 .. 2m-1` are positive (`+2`), and cyclic neighbors have `-1`. -/
noncomputable def B_evenCycleSingleMinus (m : ℕ) : Matrix (Fin (2 * m)) (Fin (2 * m)) ℝ :=
  Matrix.of fun i j =>
    if i = j then (if i.val = 0 then -2 else 2)
    else if (i.val + 1 = j.val ∨ j.val + 1 = i.val) ∨
        (i.val = 0 ∧ j.val = 2 * m - 1) ∨ (j.val = 0 ∧ i.val = 2 * m - 1) then -1
    else 0

/-- Reflection system `C_{2m}(-, +, ..., +)` for `m ≥ 2`. -/
noncomputable def evenCycleSingleMinusSystem (m : ℕ) (_hm : 2 ≤ m) :
    ReflectionSystem (2 * m) where
  B := B_evenCycleSingleMinus m
  B_symm := by
    ext i j
    simp only [transpose_apply, B_evenCycleSingleMinus, of_apply]
    by_cases hij : i = j
    · subst hij; simp
    · have hji : j ≠ i := Ne.symm hij
      simp only [hij, hji, ↓reduceIte]
      have hcond :
          ((j.val + 1 = i.val ∨ i.val + 1 = j.val) ∨
            (j.val = 0 ∧ i.val = 2 * m - 1) ∨ (i.val = 0 ∧ j.val = 2 * m - 1)) ↔
          ((i.val + 1 = j.val ∨ j.val + 1 = i.val) ∨
            (i.val = 0 ∧ j.val = 2 * m - 1) ∨ (j.val = 0 ∧ i.val = 2 * m - 1)) := by tauto
      simp only [hcond]
  B_diag_ne_zero := by
    intro i
    simp only [B_evenCycleSingleMinus, of_apply, ↓reduceIte]
    split_ifs <;> norm_num

private def evenCycleBipSign (m : ℕ) (i : Fin (2 * m)) : ℝ :=
  if i.val % 2 = 0 then 1 else -1

private lemma evenCycleBipSign_sq (m : ℕ) (i : Fin (2 * m)) :
    evenCycleBipSign m i ^ 2 = 1 := by
  unfold evenCycleBipSign
  split_ifs <;> norm_num

private lemma B_evenCycleSingleMinus_eq_signFlip (m : ℕ) (hm : 2 ≤ m) :
    B_evenCycleSingleMinus m =
      bipartiteSignFlip (B_evenCycleSinglePlus m) (evenCycleBipSign m) := by
  ext i j
  by_cases hij : i = j
  · subst hij
    rw [bipartiteSignFlip_diag (B_evenCycleSinglePlus m) (evenCycleBipSign m)
      (evenCycleBipSign_sq m) i]
    simp only [B_evenCycleSingleMinus, B_evenCycleSinglePlus, of_apply, ↓reduceIte]
    split_ifs <;> norm_num
  · rw [bipartiteSignFlip_offdiag (B_evenCycleSinglePlus m) (evenCycleBipSign m)]
    · simp only [B_evenCycleSingleMinus, B_evenCycleSinglePlus, of_apply, hij, ↓reduceIte]
      have hiff : ((i.val + 1 = j.val ∨ j.val + 1 = i.val) ∨
          (i.val = 0 ∧ j.val = 2 * m - 1) ∨ (j.val = 0 ∧ i.val = 2 * m - 1)) ↔
          (i.val + 1 = j.val ∨ j.val + 1 = i.val ∨
          (i.val = 0 ∧ j.val = 2 * m - 1) ∨ (j.val = 0 ∧ i.val = 2 * m - 1)) := by tauto
      simp only [hiff]
    · intro a b hab hB
      simp only [B_evenCycleSinglePlus, of_apply, hab, ↓reduceIte] at hB
      split_ifs at hB with hadj
      · unfold evenCycleBipSign
        rcases hadj with h1 | h2 | ⟨h0, hlast⟩ | ⟨h0, hlast⟩
        · by_cases ha : a.val % 2 = 0
          · have hb : b.val % 2 = 1 := by omega
            simp [ha, hb]
          · have hb : b.val % 2 = 0 := by omega
            simp [ha, hb]
        · by_cases ha : a.val % 2 = 0
          · have hb : b.val % 2 = 1 := by omega
            simp [ha, hb]
          · have hb : b.val % 2 = 0 := by omega
            simp [ha, hb]
        · have hmod_a : a.val % 2 = 0 := by omega
          have hmod_b : b.val % 2 = 1 := by omega
          simp [hmod_a, hmod_b]
        · have hmod_a : a.val % 2 = 1 := by omega
          have hmod_b : b.val % 2 = 0 := by omega
          simp [hmod_a, hmod_b]
      · exact absurd rfl hB
    · exact hij

/-- **Dual Single-Defect Even Cycle Spectral Radius `> 1`**:
For every `m ≥ 2`, `C_{2m}(-, +, ..., +)` has a real eigenvalue `μ < -1`,
matching `C_{2m}(+, -, ..., -)` by bipartite sign-flip duality. -/
theorem evenCycleSingleMinus_has_eigenvalue_lt_neg_one (m : ℕ) (hm : 2 ≤ m) :
    ∃ μ : ℝ, μ < -1 ∧ ∃ v : Fin (2 * m) → ℝ, v ≠ 0 ∧
      principalElement (evenCycleSingleMinusSystem m hm) *ᵥ v = μ • v := by
  have hB_eq : (evenCycleSingleMinusSystem m hm).B =
      (bipartiteSignFlipSystem (evenCycleSinglePlusSystem m hm) (evenCycleBipSign m)
        (evenCycleBipSign_sq m)).B :=
    B_evenCycleSingleMinus_eq_signFlip m hm
  have hw_eq : principalElement (evenCycleSingleMinusSystem m hm) =
      diagonal (evenCycleBipSign m) *
        principalElement (evenCycleSinglePlusSystem m hm) *
        diagonal (evenCycleBipSign m) := by
    rw [principalElement, hB_eq]
    exact prefixProd_bipartiteSignFlip (evenCycleSinglePlusSystem m hm)
      (evenCycleBipSign m) (evenCycleBipSign_sq m) (2 * m)
  rcases evenCycleSinglePlus_has_eigenvalue_lt_neg_one m hm with ⟨μ, hμ, v, hv_ne, hv_eig⟩
  refine ⟨μ, hμ, diagonal (evenCycleBipSign m) *ᵥ v, ?_, ?_⟩
  · intro hzero
    apply hv_ne
    have hD := diagonal_sq_eq_one (evenCycleBipSign m) (evenCycleBipSign_sq m)
    calc v = (1 : Matrix (Fin (2 * m)) (Fin (2 * m)) ℝ) *ᵥ v := (one_mulVec v).symm
      _ = (diagonal (evenCycleBipSign m) * diagonal (evenCycleBipSign m)) *ᵥ v := by rw [hD]
      _ = diagonal (evenCycleBipSign m) *ᵥ (diagonal (evenCycleBipSign m) *ᵥ v) :=
          (mulVec_mulVec _ _ _).symm
      _ = diagonal (evenCycleBipSign m) *ᵥ 0 := by rw [hzero]
      _ = 0 := mulVec_zero _
  · have hD := diagonal_sq_eq_one (evenCycleBipSign m) (evenCycleBipSign_sq m)
    rw [hw_eq, mulVec_mulVec, Matrix.mul_assoc, Matrix.mul_assoc, hD, Matrix.mul_one,
      ← mulVec_mulVec]
    have hv_eig' : principalElement (evenCycleSinglePlusSystem m hm) *ᵥ v = μ • v := hv_eig
    rw [hv_eig', mulVec_smul]

end EvenCycleSingleMinus

end ReflectionSystem
