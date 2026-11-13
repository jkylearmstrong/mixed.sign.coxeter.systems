/-
Copyright (c) 2026 Johnathon Kyle Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import MixedSignCoxeter.Basic

/-!
# Disconnected Components (Section 2.5) and Tree Principal Elements (Section 2.6)

Formalization of Proposition 2.45 and Theorem 2.58 of:
Johnathon Kyle Armstrong, *Principal Elements of Mixed-Sign Coxeter Systems* (FSU, 2012).

## Main results
* `wordProd_split_components` (Proposition 2.45): If `Γ` decomposes into two disconnected
  components `N₁` and `N₂`, then every word `w ∈ W(Γ)` factors as `(word in S₁) * (word in S₂)`.
* `component_fixes_other` (Proposition 2.45): `W(Γ₁)` pointwise fixes `V₂` (i.e. acts as
  the identity on basis vectors `e_j` with `j ∈ N₂`).
* `leaf_insert_conj` (Theorem 2.58): If node `t` is a leaf (connected to at most one node `i`),
  inserting `s_t` anywhere in a word `w₀` yields an element conjugate to `w₀ * s_t`.
-/

open Matrix BigOperators

namespace ReflectionSystem

variable {n : ℕ}

section Components

/-- If `part : Fin n → Bool` separates `Γ` into two disconnected components
(`part i ≠ part j → B i j = 0`), then generators in different components commute. -/
lemma comm_of_diff_component (S : ReflectionSystem n) (part : Fin n → Bool)
    (hsep : ∀ i j : Fin n, part i ≠ part j → S.B i j = 0)
    {i j : Fin n} (hij : part i ≠ part j) :
    reflectionMatrix S.B i * reflectionMatrix S.B j =
      reflectionMatrix S.B j * reflectionMatrix S.B i :=
  reflectionMatrix_comm_of_orthogonal S (hsep i j hij)

lemma comm_wordProd_of_diff_component (S : ReflectionSystem n) (part : Fin n → Bool)
    (hsep : ∀ i j : Fin n, part i ≠ part j → S.B i j = 0)
    {a : Fin n} (ha : part a = false) (w : List (Fin n)) (hw : ∀ b ∈ w, part b = true) :
    reflectionMatrix S.B a * wordProd S w = wordProd S w * reflectionMatrix S.B a := by
  induction w with
  | nil => simp [wordProd]
  | cons b t ih =>
    simp only [wordProd, List.map_cons, List.prod_cons]
    have hb : part b = true := hw b (List.mem_cons_self)
    have ht : ∀ x ∈ t, part x = true := fun x hx => hw x (List.mem_cons_of_mem b hx)
    have hcomm : reflectionMatrix S.B a * reflectionMatrix S.B b =
        reflectionMatrix S.B b * reflectionMatrix S.B a := by
      apply comm_of_diff_component S part hsep
      rw [ha, hb]
      decide
    have ih' := ih ht
    simp only [wordProd] at ih'
    rw [← Matrix.mul_assoc, hcomm, Matrix.mul_assoc, ih', ← Matrix.mul_assoc]

/-- **Proposition 2.45 (word decomposition)**: Any word `w` in `S` factors as
`(letters in S₁) * (letters in S₂)`. -/
theorem wordProd_split_components (S : ReflectionSystem n) (part : Fin n → Bool)
    (hsep : ∀ i j : Fin n, part i ≠ part j → S.B i j = 0) (w : List (Fin n)) :
    wordProd S w =
      wordProd S (w.filter fun i => part i) * wordProd S (w.filter fun i => !part i) := by
  induction w with
  | nil => simp [wordProd]
  | cons a t ih =>
    simp only [wordProd] at ih
    cases ha : part a
    · -- part a = false, so a goes to the second component
      simp only [wordProd, List.map_cons, List.prod_cons, List.filter_cons, ha,
        Bool.false_eq_true, ↓reduceIte, Bool.not_false]
      rw [ih]
      have hcomm := comm_wordProd_of_diff_component S part hsep ha (t.filter fun i => part i)
        (fun b hb => (List.mem_filter.mp hb).2)
      simp only [wordProd] at hcomm
      rw [← Matrix.mul_assoc, hcomm, Matrix.mul_assoc]
    · -- part a = true, so a goes to the first component
      simp only [wordProd, List.map_cons, List.prod_cons, List.filter_cons, ha, ↓reduceIte,
        Bool.not_true, Bool.false_eq_true]
      rw [ih, ← Matrix.mul_assoc]

/-- **Proposition 2.45 (pointwise action)**: `W(Γ₁)` fixes `e_j` for every `j ∈ N₂`. -/
theorem component_fixes_other (S : ReflectionSystem n) (part : Fin n → Bool)
    (hsep : ∀ i j : Fin n, part i ≠ part j → S.B i j = 0)
    (w : List (Fin n)) (hw : ∀ a ∈ w, part a = true)
    {j : Fin n} (hj : part j = false) (r : Fin n) :
    wordProd S w r j = if r = j then 1 else 0 := by
  induction w generalizing r with
  | nil => simp [wordProd, Matrix.one_apply]
  | cons a t ih =>
    have ha : part a = true := hw a List.mem_cons_self
    have ht : ∀ x ∈ t, part x = true := fun x hx => hw x (List.mem_cons_of_mem a hx)
    simp only [wordProd, List.map_cons, List.prod_cons, Matrix.mul_apply]
    have hcol : ∀ k : Fin n, (List.map (reflectionMatrix S.B) t).prod k j = if k = j then 1 else 0 :=
      fun k => ih ht k
    simp_rw [hcol]
    have hterm : ∀ k : Fin n,
        reflectionMatrix S.B a r k * (if k = j then (1 : ℝ) else 0) =
        if k = j then reflectionMatrix S.B a r k else 0 := by
      intro k; split_ifs <;> ring
    rw [Finset.sum_congr rfl (fun k _ => hterm k)]
    simp only [Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte, reflectionMatrix_apply]
    have hne : a ≠ j := by
      intro h; rw [h, hj] at ha; exact absurd ha (by decide)
    have h0 : S.B a j = 0 := by
      apply hsep
      rw [ha, hj]
      decide
    by_cases hra : r = a
    · subst hra
      simp [hne, h0]
    · simp [hra]

end Components

section Trees

/-- **Theorem 2.58 (leaf-insertion conjugacy)**: If node `t` is a leaf connected to at most
one node `i` (`∀ j ≠ i, B t j = 0`), then inserting `s_t` anywhere in a word `u ++ v`
yields an element conjugate (by `1` or `s_t`) to `(u ++ v) * s_t`. -/
theorem leaf_insert_conj (S : ReflectionSystem n) (t i : Fin n)
    (hleaf : ∀ j : Fin n, j ≠ i → j ≠ t → S.B t j = 0)
    (u v : List (Fin n)) (hu : t ∉ u) (hv : t ∉ v) (huv : i ∉ u ∨ i ∉ v) :
    ∃ g : Matrix (Fin n) (Fin n) ℝ,
      g * g = 1 ∧
      g * wordProd S (u ++ [t] ++ v) * g = wordProd S (u ++ v ++ [t]) := by
  have hcomm_of_not_mem : ∀ w : List (Fin n), i ∉ w → t ∉ w →
      reflectionMatrix S.B t * wordProd S w = wordProd S w * reflectionMatrix S.B t := by
    intro w hiw htw
    induction w with
    | nil => simp [wordProd]
    | cons a rest ih =>
      simp only [wordProd, List.map_cons, List.prod_cons]
      have hai : a ≠ i := fun h => hiw (h ▸ List.mem_cons_self)
      have hat : a ≠ t := fun h => htw (h ▸ List.mem_cons_self)
      have hcomm : reflectionMatrix S.B t * reflectionMatrix S.B a =
          reflectionMatrix S.B a * reflectionMatrix S.B t :=
        reflectionMatrix_comm_of_orthogonal S (hleaf a hai hat)
      have ih' := ih (fun h => hiw (List.mem_cons_of_mem a h))
        (fun h => htw (List.mem_cons_of_mem a h))
      simp only [wordProd] at ih'
      rw [← Matrix.mul_assoc, hcomm, Matrix.mul_assoc, ih', ← Matrix.mul_assoc]
  rcases huv with hiu | hiv
  · -- Case 1: `i ∉ u`, so `s_t` commutes past `u` to the front, then conjugate by `s_t`!
    refine ⟨reflectionMatrix S.B t, reflectionMatrix_mul_self S t, ?_⟩
    have hcomm_u := hcomm_of_not_mem u hiu hu
    have hst : reflectionMatrix S.B t * reflectionMatrix S.B t = 1 :=
      reflectionMatrix_mul_self S t
    simp only [wordProd, List.append_assoc, List.map_append, List.prod_append,
      List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, Matrix.mul_one] at hcomm_u ⊢
    rw [← Matrix.mul_assoc (reflectionMatrix S.B t) (List.map (reflectionMatrix S.B) u).prod, hcomm_u]
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc (reflectionMatrix S.B t) (reflectionMatrix S.B t), hst, Matrix.one_mul]
  · -- Case 2: `i ∉ v`, so `s_t` commutes past `v` to the end (`g = 1`).
    refine ⟨1, Matrix.one_mul 1, ?_⟩
    have hcomm_v := hcomm_of_not_mem v hiv hv
    simp only [Matrix.one_mul, Matrix.mul_one]
    simp only [wordProd, List.append_assoc, List.map_append, List.prod_append,
      List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, Matrix.mul_one] at hcomm_v ⊢
    rw [hcomm_v]

end Trees

end ReflectionSystem
