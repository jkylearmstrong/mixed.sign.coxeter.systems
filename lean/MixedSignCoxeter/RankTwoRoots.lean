/-
Copyright (c) 2026 Johnathon Kyle Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import MixedSignCoxeter.Basic

/-!
# Positivity of `(s_i s_j)^k e_i` for infinite dihedral pairs (Proposition 3.11, general)

Formalization of Proposition 3.11 (and the proof's sequence `g_k`) of:
Johnathon Kyle Armstrong, *Principal Elements of Mixed-Sign Coxeter Systems* (FSU, 2012).

`RankTwo.lean` checks the rank-two example `A₂(∞)`. Here we prove the statement for an
arbitrary pair of nodes `i ≠ j` of an arbitrary reflection system of any rank `n`, whenever
the pair generates an infinite dihedral group in the classical way:
`B(e_i, e_i) = B(e_j, e_j)` and `c := -2 B(e_i, e_j) / B(e_i, e_i) ≥ 2`
(for a classical Coxeter graph this is exactly the edge weight `m(i, j) = ∞`, where `c = 2`;
for a general classical Coxeter matrix with `B(e_i, e_j) ≤ -1`, `c ≥ 2` as well).

Writing `t₀ = 0`, `t₁ = 1`, `t_{k+2} = c t_{k+1} - t_k` (a Chebyshev-type sequence), we show

* `alternating_word_root` : the alternating words `g₀ = 1, g₁ = s_j, g₂ = s_i s_j,
  g₃ = s_j s_i s_j, …` of the dissertation's proof send `e_i` to
  `t_{2k+1} e_i + t_{2k} e_j` (for `g_{2k}`) and `t_{2k+1} e_i + t_{2k+2} e_j` (for `g_{2k+1}`);
* `chebSeq_ge` : `t_k ≥ k`, so all these coefficients are nonnegative;
* `prop_3_11_general` (**Proposition 3.11**): `w_k e_i ∈ Φ⁺` for `w_k = (s_i s_j)^k`, i.e.
  `w_k e_i` has nonnegative coordinates, explicitly `t_{2k+1} e_i + t_{2k} e_j`;
* `prop_3_11_infinite_order`: `(s_i s_j)^k ≠ 1` for every `k ≥ 1`.
-/

open Matrix

namespace ReflectionSystem

variable {n : ℕ}

/-- The sequence `t₀ = 0`, `t₁ = 1`, `t_{k+2} = c t_{k+1} - t_k`. -/
noncomputable def chebSeq (c : ℝ) : ℕ → ℝ
  | 0 => 0
  | 1 => 1
  | k + 2 => c * chebSeq c (k + 1) - chebSeq c k

@[simp] lemma chebSeq_zero (c : ℝ) : chebSeq c 0 = 0 := rfl
@[simp] lemma chebSeq_one (c : ℝ) : chebSeq c 1 = 1 := rfl
lemma chebSeq_succ_succ (c : ℝ) (k : ℕ) :
    chebSeq c (k + 2) = c * chebSeq c (k + 1) - chebSeq c k := rfl

/-- For `c ≥ 2` the sequence increases by at least `1` at each step. -/
lemma chebSeq_step (c : ℝ) (hc : 2 ≤ c) : ∀ k : ℕ,
    1 ≤ chebSeq c (k + 1) - chebSeq c k ∧ 0 ≤ chebSeq c k
  | 0 => by simp
  | k + 1 => by
    obtain ⟨h1, h2⟩ := chebSeq_step c hc k
    have h3 : 0 ≤ chebSeq c (k + 1) := by linarith
    refine ⟨?_, h3⟩
    rw [chebSeq_succ_succ]
    nlinarith

/-- For `c ≥ 2`, `t_k ≥ k`. -/
lemma chebSeq_ge (c : ℝ) (hc : 2 ≤ c) : ∀ k : ℕ, (k : ℝ) ≤ chebSeq c k
  | 0 => by simp
  | k + 1 => by
    have := chebSeq_ge c hc k
    have := (chebSeq_step c hc k).1
    push_cast
    linarith

/-- The vector `α e_i + β e_j`. -/
def pairVec (i j : Fin n) (α β : ℝ) : Fin n → ℝ :=
  fun r => (if r = i then α else 0) + (if r = j then β else 0)

private lemma sum_mul_pairVec (i j : Fin n) (α β : ℝ) (g : Fin n → ℝ) :
    (∑ c : Fin n, g c * pairVec i j α β c) = g i * α + g j * β := by
  simp only [pairVec, mul_add, mul_ite, mul_zero, Finset.sum_add_distrib,
    Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]

variable (S : ReflectionSystem n) {i j : Fin n}

/-- `s_i (α e_i + β e_j) = (c β - α) e_i + β e_j`. -/
lemma reflection_i_pairVec (hij : i ≠ j) (α β : ℝ) :
    (reflectionMatrix S.B i).mulVec (pairVec i j α β) =
      pairVec i j (-2 * S.B i j / S.B i i * β - α) β := by
  have hB := S.B_diag_ne_zero i
  funext r
  simp only [mulVec, dotProduct, reflectionMatrix_apply, sub_mul, ite_mul, one_mul, zero_mul,
    Finset.sum_sub_distrib, Finset.sum_ite_eq, Finset.mem_univ, ↓reduceIte]
  have hsum : (∑ x : Fin n, (if r = i then 2 * S.B i x / S.B i i else 0) * pairVec i j α β x) =
      if r = i then 2 * S.B i i / S.B i i * α + 2 * S.B i j / S.B i i * β else 0 := by
    by_cases hr : r = i
    · simp only [hr, ↓reduceIte]
      exact sum_mul_pairVec i j α β (fun x => 2 * S.B i x / S.B i i)
    · simp [hr]
  rw [hsum]
  by_cases hr : r = i
  · subst hr
    simp only [pairVec, ↓reduceIte, hij, add_zero]
    field_simp
    ring
  · simp [pairVec, hr]

/-- `s_j (α e_i + β e_j) = α e_i + (c' α - β) e_j`, `c' = -2 B(e_j, e_i) / B(e_j, e_j)`. -/
lemma reflection_j_pairVec (hij : i ≠ j) (α β : ℝ) :
    (reflectionMatrix S.B j).mulVec (pairVec i j α β) =
      pairVec i j α (-2 * S.B j i / S.B j j * α - β) := by
  have hB := S.B_diag_ne_zero j
  have hji : j ≠ i := hij.symm
  funext r
  simp only [mulVec, dotProduct, reflectionMatrix_apply, sub_mul, ite_mul, one_mul, zero_mul,
    Finset.sum_sub_distrib, Finset.sum_ite_eq, Finset.mem_univ, ↓reduceIte]
  have hsum : (∑ x : Fin n, (if r = j then 2 * S.B j x / S.B j j else 0) * pairVec i j α β x) =
      if r = j then 2 * S.B j i / S.B j j * α + 2 * S.B j j / S.B j j * β else 0 := by
    by_cases hr : r = j
    · simp only [hr, ↓reduceIte]
      exact sum_mul_pairVec i j α β (fun x => 2 * S.B j x / S.B j j)
    · simp [hr]
  rw [hsum]
  by_cases hr : r = j
  · subst hr
    simp only [pairVec, ↓reduceIte, hji, zero_add]
    field_simp
    ring
  · by_cases hri : r = i
    · subst hri; simp [pairVec, hr]
    · simp [pairVec, hr, hri]

/-- The basis vector `e_i` is `pairVec i j 1 0`. -/
lemma pairVec_single (hij : i ≠ j) : pairVec i j 1 0 = Pi.single i 1 := by
  funext r
  by_cases hr : r = i
  · subst hr; simp [pairVec, Pi.single_apply]
  · simp [pairVec, Pi.single_apply, hr]

/-- The alternating words `g_k` of the proof of Proposition 3.11:
`g₀ = 1`, `g_{2k+1} = s_j g_{2k}`, `g_{2k+2} = s_i g_{2k+1}`. -/
noncomputable def altWord (i j : Fin n) : ℕ → Matrix (Fin n) (Fin n) ℝ
  | 0 => 1
  | k + 1 => (if k % 2 = 0 then reflectionMatrix S.B j else reflectionMatrix S.B i) * altWord i j k

/-- The coefficients of `g_k e_i`. -/
lemma alternating_word_root (hij : i ≠ j) (hdiag : S.B i i = S.B j j) (k : ℕ) :
    let c := -2 * S.B i j / S.B i i
    (altWord S i j (2 * k)).mulVec (Pi.single i 1) =
        pairVec i j (chebSeq c (2 * k + 1)) (chebSeq c (2 * k)) ∧
      (altWord S i j (2 * k + 1)).mulVec (Pi.single i 1) =
        pairVec i j (chebSeq c (2 * k + 1)) (chebSeq c (2 * k + 2)) := by
  intro c
  have hcj : -2 * S.B j i / S.B j j = c := by
    simp only [c]; rw [← hdiag, S.B_symm.apply i j]
  induction k with
  | zero =>
    have h0 : (altWord S i j 0).mulVec (Pi.single i 1) = pairVec i j 1 0 := by
      simp [altWord, pairVec_single S hij]
    refine ⟨by simpa using h0, ?_⟩
    simp only [altWord, Nat.zero_mod, ↓reduceIte]
    rw [← Matrix.mulVec_mulVec]
    have := h0
    simp only [altWord] at this
    rw [this, reflection_j_pairVec S hij, hcj]
    simp [chebSeq_succ_succ]
  | succ k ih =>
    obtain ⟨_, h₂⟩ := ih
    have hodd : (2 * k + 1) % 2 = 1 := by omega
    have heven : (2 * (k + 1)) % 2 = 0 := by omega
    have hA : (altWord S i j (2 * (k + 1))).mulVec (Pi.single i 1) =
        pairVec i j (chebSeq c (2 * (k + 1) + 1)) (chebSeq c (2 * (k + 1))) := by
      have e : 2 * (k + 1) = (2 * k + 1) + 1 := by ring
      rw [e]
      simp only [altWord, hodd, one_ne_zero, ↓reduceIte]
      rw [← Matrix.mulVec_mulVec]
      have h₂' := h₂
      simp only [altWord] at h₂'
      rw [h₂', reflection_i_pairVec S hij]
      have e2 : 2 * k + 1 + 1 + 1 = (2 * k + 1) + 2 := by ring
      rw [e2, chebSeq_succ_succ, show 2 * k + 1 + 1 = 2 * k + 2 by ring]
      simp only [c]
      ring_nf
    refine ⟨hA, ?_⟩
    simp only [altWord, heven, ↓reduceIte]
    rw [← Matrix.mulVec_mulVec]
    have hA' := hA
    simp only [altWord] at hA'
    rw [hA', reflection_j_pairVec S hij, hcj]
    have e3 : 2 * (k + 1) + 2 = (2 * (k + 1)) + 2 := rfl
    rw [e3, chebSeq_succ_succ]
    ring_nf

/-- `g_{2k} = (s_i s_j)^k`. -/
lemma altWord_even (k : ℕ) :
    altWord S i j (2 * k) = (reflectionMatrix S.B i * reflectionMatrix S.B j) ^ k := by
  induction k with
  | zero => simp [altWord]
  | succ k ih =>
    have e : 2 * (k + 1) = (2 * k + 1) + 1 := by ring
    have hodd : (2 * k + 1) % 2 = 1 := by omega
    have heven : (2 * k) % 2 = 0 := by omega
    rw [e]
    simp only [altWord, hodd, one_ne_zero, ↓reduceIte, heven]
    rw [ih, pow_succ', Matrix.mul_assoc]

/-- **Proposition 3.11 (general)**: If `i ≠ j`, `B(e_i, e_i) = B(e_j, e_j)` and
`c = -2 B(e_i, e_j) / B(e_i, e_i) ≥ 2` (so `s_i s_j` has infinite order, e.g. `m(i, j) = ∞`
in a classical Coxeter graph), then `w_k = (s_i s_j)^k` satisfies
`w_k e_i = t_{2k+1} e_i + t_{2k} e_j` with `t_{2k+1} ≥ 2k+1` and `t_{2k} ≥ 2k`; in particular
every coordinate of `w_k e_i` is nonnegative, i.e. `w_k e_i ∈ Φ⁺`. The same holds for all the
alternating words `g_k` of the dissertation's proof. -/
theorem prop_3_11_general (hij : i ≠ j) (hdiag : S.B i i = S.B j j)
    (hc : 2 ≤ -2 * S.B i j / S.B i i) (k : ℕ) :
    let c := -2 * S.B i j / S.B i i
    ((reflectionMatrix S.B i * reflectionMatrix S.B j) ^ k).mulVec (Pi.single i 1) =
        pairVec i j (chebSeq c (2 * k + 1)) (chebSeq c (2 * k)) ∧
      ((2 * k + 1 : ℕ) : ℝ) ≤ chebSeq c (2 * k + 1) ∧ ((2 * k : ℕ) : ℝ) ≤ chebSeq c (2 * k) ∧
      (∀ r, 0 ≤ ((reflectionMatrix S.B i * reflectionMatrix S.B j) ^ k).mulVec
        (Pi.single i 1) r) ∧
      (∀ m r, 0 ≤ (altWord S i j m).mulVec (Pi.single i 1) r) := by
  intro c
  have hroot := alternating_word_root S hij hdiag
  have hge := chebSeq_ge c hc
  have hnn : ∀ m, 0 ≤ chebSeq c m := fun m => le_trans (Nat.cast_nonneg m) (hge m)
  have hpair : ∀ α β, 0 ≤ α → 0 ≤ β → ∀ r, 0 ≤ pairVec i j α β r := by
    intro α β hα hβ r
    unfold pairVec
    split_ifs <;> linarith
  have hk := (hroot k).1
  rw [altWord_even] at hk
  refine ⟨hk, hge _, hge _, ?_, ?_⟩
  · rw [hk]; exact hpair _ _ (hnn _) (hnn _)
  · intro m r
    obtain ⟨q, rfl | rfl⟩ := Nat.even_or_odd' m
    · rw [(hroot q).1]; exact hpair _ _ (hnn _) (hnn _) r
    · rw [(hroot q).2]; exact hpair _ _ (hnn _) (hnn _) r

/-- Under the hypotheses of Proposition 3.11, `s_i s_j` has infinite order. -/
theorem prop_3_11_infinite_order (hij : i ≠ j) (hdiag : S.B i i = S.B j j)
    (hc : 2 ≤ -2 * S.B i j / S.B i i) (k : ℕ) (hk : 1 ≤ k) :
    (reflectionMatrix S.B i * reflectionMatrix S.B j) ^ k ≠ 1 := by
  intro h1
  obtain ⟨hv, h2, _⟩ := prop_3_11_general S hij hdiag hc k
  rw [h1, Matrix.one_mulVec] at hv
  have := congr_fun hv i
  simp only [Pi.single_eq_same, pairVec, ↓reduceIte, hij, add_zero] at this
  have : ((2 * k + 1 : ℕ) : ℝ) ≤ 1 := by linarith
  have : (2 * k + 1 : ℕ) ≤ 1 := by exact_mod_cast this
  omega

end ReflectionSystem
