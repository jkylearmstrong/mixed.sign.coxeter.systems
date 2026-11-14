/-
Copyright (c) 2026 Johnathon Kyle Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.GroupTheory.Coxeter.Basic
import MixedSignCoxeter.CyclesAndDeletion

/-!
# Classical Coxeter Quotients, Deletion Property, and Corollary 1.3

Formalization of:
- **Proposition 3.19**: Every reflection system (and mixed-sign Coxeter group) `W(S)`
  is a quotient of the universal Coxeter group `W(K_n[∞])`.
- **Deletion Property & Theorem 3.9** framing (`SatisfiesDeletionProperty`) and its
  invariance under `𝒪`-conjugacy (`SignedPerm`).
- **Corollary 1.3**: For every `k : ℕ`, `(tildeAminus2Extended k).toReflectionSystem`
  is not `𝒪`-conjugate to any reflection system satisfying the Deletion Property
  (and hence, by Theorem 3.9, not conjugate to any classical Coxeter system).
-/

namespace MixedSignCoxeter

open Matrix ReflectionSystem

/-! ### Proposition 3.19: Universal Coxeter Quotient -/

/-- The universal rank-`n` Coxeter matrix `K_n[∞]` with `M i i = 1` and `M i j = 0` (`∞`)
for `i ≠ j`. -/
def freeCoxeterMatrix (n : ℕ) : CoxeterMatrix (Fin n) where
  M i j := if i = j then 1 else 0
  isSymm := by
    ext i j
    dsimp [Matrix.transpose]
    by_cases h : i = j <;> simp [h, eq_comm]
  diagonal := by
    intro i; simp
  off_diagonal := by
    intro i j hij; simp [hij]

/-- **Proposition 3.19**: For any `S : ReflectionSystem n`, the generating reflections
`S.reflectionMatrix` lift to a monoid homomorphism from the universal Coxeter group
`(freeCoxeterMatrix n).Group` to `Matrix (Fin n) (Fin n) ℝ`, realizing `W(S)` as a
quotient of `W(K_n[∞])`. -/
theorem reflectionSystem_isLiftable_freeCoxeter {n : ℕ} (S : ReflectionSystem n) :
    (freeCoxeterMatrix n).IsLiftable (reflectionMatrix S.B) := by
  intro i j
  by_cases h : i = j
  · subst h
    simp [freeCoxeterMatrix, reflectionMatrix_mul_self S i]
  · simp [freeCoxeterMatrix, h]

noncomputable def freeCoxeterQuotient {n : ℕ} (S : ReflectionSystem n) :
    (freeCoxeterMatrix n).Group →* Matrix (Fin n) (Fin n) ℝ :=
  (freeCoxeterMatrix n).toCoxeterSystem.lift ⟨reflectionMatrix S.B, reflectionSystem_isLiftable_freeCoxeter S⟩

theorem freeCoxeterQuotient_simple {n : ℕ} (S : ReflectionSystem n) (i : Fin n) :
    freeCoxeterQuotient S ((freeCoxeterMatrix n).toCoxeterSystem.simple i) =
      reflectionMatrix S.B i :=
  (freeCoxeterMatrix n).toCoxeterSystem.lift_apply_simple
    (reflectionSystem_isLiftable_freeCoxeter S) i

/-! ### Deletion Property and Corollary 1.3 -/

/-- A `ReflectionSystem n` satisfies the **Deletion Property** if every non-reduced word
`w` (one equal in `W(S)` to a strictly shorter word `u`) admits two indices `i < j < w.length`
whose deletion preserves `S.wordProd w`. -/
def SatisfiesDeletionProperty {n : ℕ} (S : ReflectionSystem n) : Prop :=
  ∀ w : List (Fin n), (∃ u : List (Fin n), u.length < w.length ∧ S.wordProd w = S.wordProd u) →
    ∃ i j : ℕ, i < j ∧ j < w.length ∧ S.wordProd (deleteTwo w i j) = S.wordProd w

/-- For every `k : ℕ`, the rank `3 + k` system `tildeAminus2Extended k` fails the
Deletion Property (Theorem 1.2). -/
theorem tildeAminus2Extended_not_deletion (k : ℕ) :
    ¬ SatisfiesDeletionProperty (tildeAminus2Extended k).toReflectionSystem := by
  intro hdel
  obtain ⟨heq, hno⟩ := theorem_1_2_infinite_family k
  let w : List (Fin (3 + k)) := [0, 1, 0, 2, 0].map (Fin.castAdd k)
  let u : List (Fin (3 + k)) := [2, 0, 1].map (Fin.castAdd k)
  have hu : u.length < w.length := by simp [u, w]
  obtain ⟨i, j, hij, hj, hdel_eq⟩ := hdel w ⟨u, hu, heq⟩
  have hlen : w.length = 5 := by simp [w]
  rw [hlen] at hj
  have hi5 : i < 5 := lt_trans hij hj
  exact hno ⟨i, hi5⟩ ⟨j, hj⟩ hij hdel_eq

private lemma deleteTwo_map {α β : Type*} (f : α → β) (w : List α) (i j : ℕ) :
    deleteTwo (w.map f) i j =
      (deleteTwo w i j).map f := by
  simp [deleteTwo, List.zipIdx_map, List.filter_map, Function.comp_def]

private lemma wordProd_O_conjugate {n : ℕ} {B₁ B₂ : Matrix (Fin n) (Fin n) ℝ}
    (P : SignedPerm n) (hB : B₂ = P.toMatrixᵀ * B₁ * P.toMatrix) (w : List (Fin n)) :
    P.toMatrixᵀ * (w.map (reflectionMatrix B₁ ∘ P.perm)).prod * P.toMatrix =
      (w.map (reflectionMatrix B₂)).prod := by
  induction w with
  | nil =>
    simp [P.toMatrix_transpose_mul_self]
  | cons a t ih =>
    simp only [List.map_cons, List.prod_cons, Function.comp_apply]
    have ha : P.toMatrixᵀ * reflectionMatrix B₁ (P.perm a) * P.toMatrix = reflectionMatrix B₂ a :=
      conjugate_reflections_of_form B₁ B₂ P hB a
    have hPP : P.toMatrix * P.toMatrixᵀ = 1 := by
      ext r c
      simp only [Matrix.mul_apply, Matrix.transpose_apply, SignedPerm.toMatrix_apply, Matrix.one_apply]
      have hterm : ∀ k : Fin n,
          (if r = P.perm k then P.signReal k else 0) *
            (if c = P.perm k then P.signReal k else 0) =
          if k = P.perm.symm r then (if r = c then 1 else 0) else 0 := by
        intro k
        by_cases hk : k = P.perm.symm r
        · subst hk
          have hpk : P.perm (P.perm.symm r) = r := P.perm.apply_symm_apply r
          by_cases hrc : r = c
          · subst hrc; simp [hpk, P.signReal_mul_self]
          · simp [hpk, hrc, Ne.symm hrc]
        · have hne : r ≠ P.perm k := fun h => hk (P.perm.eq_symm_apply.mpr h.symm)
          simp [hk, hne]
      rw [Finset.sum_congr rfl fun k _ => hterm k]
      simp
    calc P.toMatrixᵀ * (reflectionMatrix B₁ (P.perm a) *
          (t.map (reflectionMatrix B₁ ∘ P.perm)).prod) * P.toMatrix
        = (P.toMatrixᵀ * reflectionMatrix B₁ (P.perm a) * P.toMatrix) *
            (P.toMatrixᵀ * (t.map (reflectionMatrix B₁ ∘ P.perm)).prod * P.toMatrix) := by
          calc P.toMatrixᵀ * (reflectionMatrix B₁ (P.perm a) *
                (t.map (reflectionMatrix B₁ ∘ P.perm)).prod) * P.toMatrix
              = P.toMatrixᵀ * reflectionMatrix B₁ (P.perm a) * 1 *
                  (t.map (reflectionMatrix B₁ ∘ P.perm)).prod * P.toMatrix := by
                simp only [mul_one, mul_assoc]
            _ = P.toMatrixᵀ * reflectionMatrix B₁ (P.perm a) * (P.toMatrix * P.toMatrixᵀ) *
                  (t.map (reflectionMatrix B₁ ∘ P.perm)).prod * P.toMatrix := by rw [hPP]
            _ = (P.toMatrixᵀ * reflectionMatrix B₁ (P.perm a) * P.toMatrix) *
                  (P.toMatrixᵀ * (t.map (reflectionMatrix B₁ ∘ P.perm)).prod * P.toMatrix) := by
                simp only [mul_assoc]
      _ = reflectionMatrix B₂ a * (t.map (reflectionMatrix B₂)).prod := by rw [ha, ih]

/-- The Deletion Property is invariant under `𝒪`-conjugacy (`SignedPerm`). -/
theorem deletion_invariant_of_O_conjugate {n : ℕ} (S₁ S₂ : ReflectionSystem n)
    (P : SignedPerm n) (hB : S₂.B = P.toMatrixᵀ * S₁.B * P.toMatrix)
    (h1 : SatisfiesDeletionProperty S₁) :
    SatisfiesDeletionProperty S₂ := by
  intro w ⟨u, hu, heq⟩
  have hconj : ∀ v : List (Fin n),
      P.toMatrixᵀ * S₁.wordProd (v.map P.perm) * P.toMatrix = S₂.wordProd v := by
    intro v
    simpa [wordProd, List.map_map] using wordProd_O_conjugate P hB v
  have hS1eq : S₁.wordProd (w.map P.perm) = S₁.wordProd (u.map P.perm) := by
    have hw := hconj w
    have hu_conj := hconj u
    rw [heq, ← hu_conj] at hw
    have h1' := congr_arg (fun M => P.toMatrix * M * P.toMatrixᵀ) hw
    have hPP : P.toMatrix * P.toMatrixᵀ = 1 := by
      ext r c
      simp only [Matrix.mul_apply, Matrix.transpose_apply, SignedPerm.toMatrix_apply, Matrix.one_apply]
      have hterm : ∀ k : Fin n,
          (if r = P.perm k then P.signReal k else 0) *
            (if c = P.perm k then P.signReal k else 0) =
          if k = P.perm.symm r then (if r = c then 1 else 0) else 0 := by
        intro k
        by_cases hk : k = P.perm.symm r
        · subst hk
          have hpk : P.perm (P.perm.symm r) = r := P.perm.apply_symm_apply r
          by_cases hrc : r = c
          · subst hrc; simp [hpk, P.signReal_mul_self]
          · simp [hpk, hrc, Ne.symm hrc]
        · have hne : r ≠ P.perm k := fun h => hk (P.perm.eq_symm_apply.mpr h.symm)
          simp [hk, hne]
      rw [Finset.sum_congr rfl fun k _ => hterm k]
      simp
    have h1'' : (P.toMatrix * P.toMatrixᵀ) * S₁.wordProd (w.map P.perm) *
        (P.toMatrix * P.toMatrixᵀ) =
        (P.toMatrix * P.toMatrixᵀ) * S₁.wordProd (u.map P.perm) *
          (P.toMatrix * P.toMatrixᵀ) := by
      simpa only [mul_assoc] using h1'
    simpa [hPP] using h1''
  obtain ⟨i, j, hij, hj, hdel⟩ := h1 (w.map P.perm) ⟨u.map P.perm, by simpa using hu, hS1eq⟩
  refine ⟨i, j, hij, by simpa using hj, ?_⟩
  rw [← hconj (deleteTwo w i j), ← hconj w,
    ← deleteTwo_map P.perm w i j, hdel]

/-- **Corollary 1.3**: For every `k : ℕ`, `(tildeAminus2Extended k).toReflectionSystem`
is not `𝒪`-conjugate to any reflection system `S₁` satisfying the Deletion Property
(and hence, by Theorem 3.9, not conjugate to any classical Coxeter system). -/
theorem corollary_1_3_not_conjugate_to_deletion (k : ℕ)
    (S₁ : ReflectionSystem (3 + k)) (hdel : SatisfiesDeletionProperty S₁) :
    ¬ ∃ P : SignedPerm (3 + k),
      (tildeAminus2Extended k).toBilinearForm =
        P.toMatrixᵀ * S₁.B * P.toMatrix := by
  rintro ⟨P, hB⟩
  have h2 := deletion_invariant_of_O_conjugate S₁
    (tildeAminus2Extended k).toReflectionSystem P hB hdel
  exact tildeAminus2Extended_not_deletion k h2

end MixedSignCoxeter
