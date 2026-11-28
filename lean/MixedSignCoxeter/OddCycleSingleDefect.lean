/-
Copyright (c) 2026 Johnathon Kyle Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import MixedSignCoxeter.ReflectionSystem

/-!
# Odd Cycles with a Single Positive Vertex $C_{2m+1}(-, \dots, -, +)$

Proves a general infinite-family theorem for single mixed-sign cycles of odd length
$k = 2m + 1$ ($m \ge 1$) with signs $(-, \dots, -, +)$:
* `oddCycleSinglePlus_minimal_poly`: the cyclic principal element
  $w = s_0 s_1 \cdots s_{2m}$ satisfies $(w + 1)^2 (w^{2m} - 1) = 0$ for every $m \ge 1$.
  Consequently, every complex eigenvalue of $w$ is either $-1$ or a $(2m)$-th root of unity
  (spectral radius $1$).
* `oddCycleSinglePlus_w_ne_neg_one`: $(w + 1)(w^{2m} - 1) \ne 0$ for every $m \ge 1$,
  showing $w$ has a non-trivial Jordan block at $-1$ and hence infinite order despite having
  spectral radius $1$.
-/

open Matrix

namespace MixedSignCoxeter

section OddCycleSingleDefect

/-- Bilinear form of the odd cycle $C_{2m+1}(-, \dots, -, +)$: vertices $0, \dots, 2m-1$
have diagonal $-2$, vertex $2m$ has diagonal $+2$, and adjacent vertices mod $2m+1$ have
off-diagonal $-1$. -/
def B_oddCycleSinglePlus (m : ℕ) : Matrix (Fin (2 * m + 1)) (Fin (2 * m + 1)) ℝ :=
  Matrix.of fun i j =>
    if i = j then (if i.val = 2 * m then 2 else -2)
    else if (i.val + 1 = j.val ∨ j.val + 1 = i.val ∨
        (i.val = 0 ∧ j.val = 2 * m) ∨ (j.val = 0 ∧ i.val = 2 * m)) then -1
    else 0

/-- `B_oddCycleSinglePlus m` defines a valid `ReflectionSystem (2 * m + 1)`. -/
def oddCycleSinglePlusSystem (m : ℕ) (hm : 1 ≤ m) : ReflectionSystem (2 * m + 1) where
  B := B_oddCycleSinglePlus m
  B_symm := by
    ext i j
    simp only [transpose_apply, B_oddCycleSinglePlus, of_apply]
    by_cases hij : i = j
    · subst hij; simp
    · have hji : j ≠ i := Ne.symm hij
      simp only [hij, hji, ↓reduceIte]
      by_cases hadj : i.val + 1 = j.val ∨ j.val + 1 = i.val ∨
          (i.val = 0 ∧ j.val = 2 * m) ∨ (j.val = 0 ∧ i.val = 2 * m)
      · split_ifs <;> first | rfl | (exfalso; simp only [Fin.ext_iff, Fin.val_zero] at *; tauto)
      · split_ifs <;> first | rfl | (exfalso; simp only [Fin.ext_iff, Fin.val_zero] at *; tauto)
  B_diag_ne_zero := by
    intro i
    simp only [B_oddCycleSinglePlus, of_apply, ↓reduceIte]
    split_ifs <;> norm_num

/-- The cyclic principal element `w = s₀ s₁ ... s_{2m}` of `C_{2m+1}(-, ..., -, +)`. -/
noncomputable def w_oddCycleSinglePlus (m : ℕ) (hm : 1 ≤ m) :
    Matrix (Fin (2 * m + 1)) (Fin (2 * m + 1)) ℝ :=
  (oddCycleSinglePlusSystem m hm).wordProd (List.finRange (2 * m + 1))

private lemma reflectionMatrix_mulVec_apply {n : ℕ} (B : Matrix (Fin n) (Fin n) ℝ)
    (i r : Fin n) (x : Fin n → ℝ) :
    (ReflectionSystem.reflectionMatrix B i).mulVec x r =
      x r - if r = i then (∑ j : Fin n, 2 * B i j * x j) / B i i else 0 := by
  simp only [Matrix.mulVec, dotProduct, ReflectionSystem.reflectionMatrix_apply, sub_mul,
    Finset.sum_sub_distrib]
  have h1 : ∑ j : Fin n, (if r = j then (1 : ℝ) else 0) * x j = x r := by
    simp [Finset.sum_ite_eq]
  rw [h1]
  by_cases hri : r = i
  · subst hri
    simp only [↓reduceIte, Finset.sum_div]
    congr 1
    exact Finset.sum_congr rfl fun j _ => by ring
  · simp [hri]

private lemma reflectionMatrix_oddCycle_mulVec (m : ℕ) (hm : 1 ≤ m)
    (i : Fin (2 * m + 1)) (x : Fin (2 * m + 1) → ℝ) (r : Fin (2 * m + 1)) :
    (ReflectionSystem.reflectionMatrix (B_oddCycleSinglePlus m) i).mulVec x r =
      if r = i then
        if h2m : i.val = 2 * m then -x i + x ⟨0, by omega⟩ + x ⟨2 * m - 1, by omega⟩
        else if h0 : i.val = 0 then -x i - x ⟨1, by omega⟩ - x ⟨2 * m, by omega⟩
        else -x i - x ⟨i.val - 1, by omega⟩ - x ⟨i.val + 1, by omega⟩
      else x r := by
  by_cases hri : r = i
  · subst hri
    rw [reflectionMatrix_mulVec_apply]
    simp only [↓reduceIte]
    by_cases h2m : r.val = 2 * m
    · rw [dif_pos h2m]
      have hdiag : B_oddCycleSinglePlus m r r = 2 := by
        simp [B_oddCycleSinglePlus, h2m]
      rw [hdiag]
      have hsum : (∑ j : Fin (2 * m + 1), 2 * B_oddCycleSinglePlus m r j * x j) =
          4 * x r - 2 * x ⟨0, by omega⟩ - 2 * x ⟨2 * m - 1, by omega⟩ := by
        have hterm : ∀ j : Fin (2 * m + 1), 2 * B_oddCycleSinglePlus m r j * x j =
            (if j = r then 4 * x j else 0) +
              (if j = ⟨0, by omega⟩ then -2 * x j else 0) +
              (if j = ⟨2 * m - 1, by omega⟩ then -2 * x j else 0) := by
          intro j
          simp only [B_oddCycleSinglePlus, of_apply]
          rcases eq_or_ne j r with rfl | hjr
          · have hne0 : j ≠ ⟨0, by omega⟩ := Fin.ne_of_val_ne (by simp only [Fin.val_mk]; omega)
            have hne1 : j ≠ ⟨2 * m - 1, by omega⟩ := Fin.ne_of_val_ne (by simp only [Fin.val_mk]; omega)
            simp only [↓reduceIte, h2m, hne0, hne1]; ring
          · rcases eq_or_ne j ⟨0, by omega⟩ with rfl | hj0
            · have hne1 : (⟨0, by omega⟩ : Fin (2 * m + 1)) ≠ ⟨2 * m - 1, by omega⟩ :=
                Fin.ne_of_val_ne (by simp only [Fin.val_mk]; omega)
              simp only [hjr, Ne.symm hjr, eq_self_iff_true, ↓reduceIte, hne1, h2m, Fin.val_mk,
                true_and, or_true]; ring
            · rcases eq_or_ne j ⟨2 * m - 1, by omega⟩ with rfl | hj1
              · have hadj : r.val + 1 = (⟨2 * m - 1, by omega⟩ : Fin (2 * m + 1)).val ∨
                    (⟨2 * m - 1, by omega⟩ : Fin (2 * m + 1)).val + 1 = r.val ∨
                    (r.val = 0 ∧ (⟨2 * m - 1, by omega⟩ : Fin (2 * m + 1)).val = 2 * m) ∨
                    ((⟨2 * m - 1, by omega⟩ : Fin (2 * m + 1)).val = 0 ∧ r.val = 2 * m) :=
                  Or.inr (Or.inl (by simp only [Fin.val_mk]; omega))
                simp only [hjr, Ne.symm hjr, eq_self_iff_true, ↓reduceIte, hj0, hadj]; ring
              · have hnot : ¬(r.val + 1 = j.val ∨ j.val + 1 = r.val ∨
                    (r.val = 0 ∧ j.val = 2 * m) ∨ (j.val = 0 ∧ r.val = 2 * m)) := by
                  have := Fin.val_ne_of_ne hjr
                  have := Fin.val_ne_of_ne hj0
                  have := Fin.val_ne_of_ne hj1
                  simp only [Fin.val_mk] at *
                  omega
                simp only [hjr, Ne.symm hjr, ↓reduceIte, hj0, hj1, hnot]; ring
        simp_rw [hterm, Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
        ring
      rw [hsum]
      ring
    · rw [dif_neg h2m]
      have hdiag : B_oddCycleSinglePlus m r r = -2 := by
        simp [B_oddCycleSinglePlus, h2m]
      rw [hdiag]
      by_cases h0 : r.val = 0
      · rw [dif_pos h0]
        have hsum : (∑ j : Fin (2 * m + 1), 2 * B_oddCycleSinglePlus m r j * x j) =
            -4 * x r - 2 * x ⟨1, by omega⟩ - 2 * x ⟨2 * m, by omega⟩ := by
          have hterm : ∀ j : Fin (2 * m + 1), 2 * B_oddCycleSinglePlus m r j * x j =
              (if j = r then -4 * x j else 0) +
                (if j = ⟨1, by omega⟩ then -2 * x j else 0) +
                (if j = ⟨2 * m, by omega⟩ then -2 * x j else 0) := by
            intro j
            simp only [B_oddCycleSinglePlus, of_apply]
            rcases eq_or_ne j r with rfl | hjr
            · have hne1 : j ≠ ⟨1, by omega⟩ := Fin.ne_of_val_ne (by simp only [Fin.val_mk]; omega)
              have hne2 : j ≠ ⟨2 * m, by omega⟩ := Fin.ne_of_val_ne (by simp only [Fin.val_mk]; omega)
              simp only [↓reduceIte, h2m, hne1, hne2]; ring
            · rcases eq_or_ne j ⟨1, by omega⟩ with rfl | hj1
              · have hne2 : (⟨1, by omega⟩ : Fin (2 * m + 1)) ≠ ⟨2 * m, by omega⟩ :=
                  Fin.ne_of_val_ne (by simp only [Fin.val_mk]; omega)
                have hadj : r.val + 1 = (⟨1, by omega⟩ : Fin (2 * m + 1)).val ∨
                    (⟨1, by omega⟩ : Fin (2 * m + 1)).val + 1 = r.val ∨
                    (r.val = 0 ∧ (⟨1, by omega⟩ : Fin (2 * m + 1)).val = 2 * m) ∨
                    ((⟨1, by omega⟩ : Fin (2 * m + 1)).val = 0 ∧ r.val = 2 * m) :=
                  Or.inl (by simp only [Fin.val_mk]; omega)
                simp only [hjr, Ne.symm hjr, eq_self_iff_true, ↓reduceIte, hne2, hadj]; ring
              · rcases eq_or_ne j ⟨2 * m, by omega⟩ with rfl | hj2
                · simp only [hjr, Ne.symm hjr, eq_self_iff_true, ↓reduceIte, hj1, h0, Fin.val_mk,
                    and_self, true_or, or_true]; ring
                · have hnot : ¬(r.val + 1 = j.val ∨ j.val + 1 = r.val ∨
                      (r.val = 0 ∧ j.val = 2 * m) ∨ (j.val = 0 ∧ r.val = 2 * m)) := by
                    have := Fin.val_ne_of_ne hjr
                    have := Fin.val_ne_of_ne hj1
                    have := Fin.val_ne_of_ne hj2
                    simp only [Fin.val_mk] at *
                    omega
                  simp only [hjr, Ne.symm hjr, ↓reduceIte, hj1, hj2, hnot]; ring
          simp_rw [hterm, Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
          ring
        rw [hsum]
        ring
      · rw [dif_neg h0]
        have hsum : (∑ j : Fin (2 * m + 1), 2 * B_oddCycleSinglePlus m r j * x j) =
            -4 * x r - 2 * x ⟨r.val - 1, by omega⟩ - 2 * x ⟨r.val + 1, by omega⟩ := by
          have hterm : ∀ j : Fin (2 * m + 1), 2 * B_oddCycleSinglePlus m r j * x j =
              (if j = r then -4 * x j else 0) +
                (if j = ⟨r.val - 1, by omega⟩ then -2 * x j else 0) +
                (if j = ⟨r.val + 1, by omega⟩ then -2 * x j else 0) := by
            intro j
            simp only [B_oddCycleSinglePlus, of_apply]
            rcases eq_or_ne j r with rfl | hjr
            · have hnep : j ≠ ⟨j.val - 1, by omega⟩ := Fin.ne_of_val_ne (by simp only [Fin.val_mk]; omega)
              have hnen : j ≠ ⟨j.val + 1, by omega⟩ := Fin.ne_of_val_ne (by simp only [Fin.val_mk]; omega)
              simp only [↓reduceIte, h2m, hnep, hnen]; ring
            · rcases eq_or_ne j ⟨r.val - 1, by omega⟩ with rfl | hjp
              · have hnen : (⟨r.val - 1, by omega⟩ : Fin (2 * m + 1)) ≠ ⟨r.val + 1, by omega⟩ :=
                  Fin.ne_of_val_ne (by simp only [Fin.val_mk]; omega)
                have hadj : r.val + 1 = (⟨r.val - 1, by omega⟩ : Fin (2 * m + 1)).val ∨
                    (⟨r.val - 1, by omega⟩ : Fin (2 * m + 1)).val + 1 = r.val ∨
                    (r.val = 0 ∧ (⟨r.val - 1, by omega⟩ : Fin (2 * m + 1)).val = 2 * m) ∨
                    ((⟨r.val - 1, by omega⟩ : Fin (2 * m + 1)).val = 0 ∧ r.val = 2 * m) :=
                  Or.inr (Or.inl (by simp only [Fin.val_mk]; omega))
                simp only [hjr, Ne.symm hjr, eq_self_iff_true, ↓reduceIte, hnen, hadj]; ring
              · rcases eq_or_ne j ⟨r.val + 1, by omega⟩ with hj_eq | hjn
                · rw [hj_eq] at hjr hjp ⊢
                  simp only [hjr, Ne.symm hjr, eq_self_iff_true, ↓reduceIte, hjp, Fin.val_mk,
                    true_or]; ring
                · have hnot : ¬(r.val + 1 = j.val ∨ j.val + 1 = r.val ∨
                      (r.val = 0 ∧ j.val = 2 * m) ∨ (j.val = 0 ∧ r.val = 2 * m)) := by
                    have := Fin.val_ne_of_ne hjr
                    have := Fin.val_ne_of_ne hjp
                    have := Fin.val_ne_of_ne hjn
                    simp only [Fin.val_mk] at *
                    omega
                  simp only [hjr, Ne.symm hjr, ↓reduceIte, hjp, hjn, hnot]; ring
          simp_rw [hterm, Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
          ring
        rw [hsum]
        ring
  · simp only [hri, ↓reduceIte]
    rw [reflectionMatrix_mulVec_apply]
    simp [hri]

private noncomputable def suffixProd (m : ℕ) (t : ℕ) :
    Matrix (Fin (2 * m + 1)) (Fin (2 * m + 1)) ℝ :=
  ((List.finRange (2 * m + 1)).drop t).map
    (ReflectionSystem.reflectionMatrix (B_oddCycleSinglePlus m)) |>.prod

private lemma suffixProd_zero (m : ℕ) (hm : 1 ≤ m) :
    suffixProd m 0 = w_oddCycleSinglePlus m hm := rfl

private lemma suffixProd_ge (m : ℕ) {t : ℕ} (ht : 2 * m + 1 ≤ t) :
    suffixProd m t = 1 := by
  rw [suffixProd, List.drop_eq_nil_of_le (by simpa using ht), List.map_nil, List.prod_nil]

private lemma suffixProd_step (m : ℕ) {t : ℕ} (ht : t < 2 * m + 1) :
    suffixProd m t =
      ReflectionSystem.reflectionMatrix (B_oddCycleSinglePlus m) ⟨t, ht⟩ * suffixProd m (t + 1) := by
  have hdrop : (List.finRange (2 * m + 1)).drop t =
      ⟨t, ht⟩ :: (List.finRange (2 * m + 1)).drop (t + 1) := by
    rw [List.drop_eq_getElem_cons (by simpa using ht)]
    simp
  simp only [suffixProd, hdrop, List.map_cons, List.prod_cons]

/-- Alternating sign vector `u_r = (-1)^r`. -/
private noncomputable def altVec (m : ℕ) : Fin (2 * m + 1) → ℝ :=
  fun r => (-1 : ℝ) ^ r.val

/-- `v_0 = e_0 + e_{2m}` and `v_j = e_j` for `1 ≤ j ≤ 2m - 1`. -/
private noncomputable def basisV (m : ℕ) (hm : 1 ≤ m) (j : Fin (2 * m)) :
    Fin (2 * m + 1) → ℝ :=
  if j.val = 0 then Pi.single ⟨0, by omega⟩ 1 + Pi.single ⟨2 * m, by omega⟩ 1
  else Pi.single ⟨j.val, by omega⟩ 1

private lemma w_mulVec_altVec (m : ℕ) (hm : 1 ≤ m) :
    (w_oddCycleSinglePlus m hm).mulVec (altVec m) = -altVec m := by
  have hstep : ∀ (d : ℕ) (hd : d ≤ 2 * m + 1),
      (suffixProd m (2 * m + 1 - d)).mulVec (altVec m) =
        fun r => if r.val < 2 * m + 1 - d then altVec m r else -altVec m r := by
    intro d
    induction d with
    | zero =>
      intro _
      rw [Nat.sub_zero, suffixProd_ge m (le_refl _), Matrix.one_mulVec]
      ext r
      simp [r.isLt]
    | succ d ih =>
      intro hd
      set t := 2 * m + 1 - (d + 1)
      have hlt : t < 2 * m + 1 := by omega
      have hsucc : t + 1 = 2 * m + 1 - d := by omega
      have ih' := ih (by omega)
      rw [suffixProd_step m hlt, ← Matrix.mulVec_mulVec, hsucc, ih', ← hsucc]
      ext r
      rw [reflectionMatrix_oddCycle_mulVec m hm ⟨t, hlt⟩]
      by_cases hr : r = ⟨t, hlt⟩
      · subst hr
        simp only [↓reduceIte, Fin.val_mk, lt_self_iff_false]
        by_cases h2m : t = 2 * m
        · rw [dif_pos h2m]
          have h0lt : 0 < t + 1 := by omega
          have h1lt : 2 * m - 1 < t + 1 := by omega
          have h2mlt : 2 * m < t + 1 := by omega
          simp only [h0lt, h1lt, h2mlt, ↓reduceIte, altVec, Fin.val_mk, pow_zero]
          have hpow : (-1 : ℝ) ^ (2 * m) = 1 := by simp [pow_mul]
          have hpow1 : (-1 : ℝ) ^ (2 * m - 1) = -1 := by
            have : 2 * m = (2 * m - 1) + 1 := by omega
            have h' : (-1 : ℝ) ^ (2 * m) = (-1 : ℝ) ^ (2 * m - 1) * (-1) := by
              conv_lhs => rw [this, pow_succ]
            linarith [hpow]
          simp [h2m, hpow, hpow1]
        · rw [dif_neg h2m]
          by_cases h0 : t = 0
          · rw [dif_pos h0]
            have h0lt : 0 < t + 1 := by omega
            have h1ge : ¬(1 < t + 1) := by omega
            have h2mge : ¬(2 * m < t + 1) := by omega
            simp only [h0lt, h1ge, h2mge, ↓reduceIte, altVec, Fin.val_mk, pow_zero, pow_one]
            have hpow : (-1 : ℝ) ^ (2 * m) = 1 := by simp [pow_mul]
            simp [h0, hpow]
          · rw [dif_neg h0]
            have hcur : t < t + 1 := by omega
            have hprev : t - 1 < t + 1 := by omega
            have hnext : ¬(t + 1 < t + 1) := by omega
            simp only [hcur, hprev, hnext, ↓reduceIte, altVec, Fin.val_mk]
            have ht1 : t = (t - 1) + 1 := by omega
            have hp1 : (-1 : ℝ) ^ t = -((-1 : ℝ) ^ (t - 1)) := by
              conv_lhs => rw [ht1, pow_succ]; ring
            have hp2 : (-1 : ℝ) ^ (t + 1) = -((-1 : ℝ) ^ t) := by
              rw [pow_succ]; ring
            linarith
      · have hne : r.val ≠ t := fun h => hr (Fin.ext h)
        simp only [hr, ↓reduceIte]
        by_cases hlt' : r.val < t
        · have hlt2 : r.val < t + 1 := by omega
          simp only [hlt', hlt2, ↓reduceIte]
        · have hlt2 : ¬(r.val < t + 1) := by omega
          simp only [hlt', hlt2, ↓reduceIte]
  have h0 := hstep (2 * m + 1) (le_refl _)
  rw [Nat.sub_self, suffixProd_zero m hm] at h0
  rw [h0]
  ext r
  simp

private lemma w_mulVec_basisV_lt (m : ℕ) (hm : 1 ≤ m) (j : Fin (2 * m)) (hj : j.val + 1 < 2 * m) :
    (w_oddCycleSinglePlus m hm).mulVec (basisV m hm j) = -basisV m hm ⟨j.val + 1, hj⟩ := by
  by_cases hj0 : j.val = 0
  · have hstep0 : ∀ (d : ℕ) (hd : d ≤ 2 * m + 1),
        (suffixProd m (2 * m + 1 - d)).mulVec (basisV m hm j) =
          if 2 * m + 1 - d = 2 * m + 1 then basisV m hm j
          else if 2 ≤ 2 * m + 1 - d then Pi.single ⟨0, by omega⟩ (1 : ℝ)
          else if 2 * m + 1 - d = 1 then
            Pi.single ⟨0, by omega⟩ (1 : ℝ) - Pi.single ⟨1, by omega⟩ (1 : ℝ)
          else -Pi.single ⟨1, by omega⟩ (1 : ℝ) := by
      intro d
      induction d with
      | zero =>
        intro _
        rw [Nat.sub_zero, suffixProd_ge m (le_refl _), Matrix.one_mulVec]
        simp
      | succ d ih =>
        intro hd
        set t := 2 * m + 1 - (d + 1)
        have ht_lt : t < 2 * m + 1 := by omega
        have ht_succ : t + 1 = 2 * m + 1 - d := by omega
        rw [suffixProd_step m ht_lt, ← Matrix.mulVec_mulVec, ht_succ, ih (by omega), ← ht_succ]
        ext r
        rw [reflectionMatrix_oddCycle_mulVec m hm]
        by_cases ht2m : t = 2 * m
        · have hm0 : m ≠ 0 := by omega
          have hp_ne0 : 2 * m - 1 ≠ 0 := by omega
          by_cases hrt : r = ⟨t, ht_lt⟩
          · subst hrt
            have h0_ne : (0 : ℕ) ≠ 2 * m := by omega
            have hp_ne : (2 * m - 1 : ℕ) ≠ 2 * m := by omega
            simp [ht2m, hj0, hm, hm0, hp_ne0, basisV, Pi.single_apply, h0_ne, hp_ne]
          · have hrt_val : r.val ≠ 2 * m := fun h => hrt (Fin.ext (h.trans ht2m.symm))
            have hrt2m : r ≠ ⟨2 * m, by omega⟩ := Fin.ne_of_val_ne hrt_val
            simp only [hrt2m, ht2m, hj0, basisV, ↓reduceIte, hm, hm0, Pi.add_apply]
            rw [Pi.single_eq_of_ne hrt2m]
            simp [hm]
        · by_cases ht2 : 2 ≤ t
          · have h2t1 : 2 ≤ t + 1 := by omega
            have hne_end : t ≠ 2 * m + 1 := by omega
            by_cases hrt : r = ⟨t, ht_lt⟩
            · subst hrt
              have ht0 : t ≠ 0 := by omega
              have h_ne0 : t ≠ 0 := by omega
              have h_p_ne0 : t - 1 ≠ 0 := by omega
              have h_n_ne0 : t + 1 ≠ 0 := by omega
              simp [ht2m, ht2, h2t1, ht0, hne_end, h_ne0, h_p_ne0, h_n_ne0, Pi.single_apply,
                Fin.ext_iff, h_ne0.symm]
            · simp [hrt, ht2m, ht2, h2t1, hne_end]
          · by_cases ht1 : t = 1
            · have h2t1 : 2 ≤ t + 1 := by omega
              have hm0 : m ≠ 0 := by omega
              have hne_end : t ≠ 2 * m + 1 := by omega
              have h1_ne_2m : (1 : ℕ) ≠ 2 * m := by omega
              by_cases hrt : r = ⟨t, ht_lt⟩
              · subst hrt
                have h_ne0 : t ≠ 0 := by omega
                have h_p_eq0 : t - 1 = 0 := by omega
                have h_n_ne0 : t + 1 ≠ 0 := by omega
                have h0_ne1 : (0 : ℕ) ≠ 1 := by omega
                simp [hm0, ht2m, ht2, ht1, h2t1, hne_end, h1_ne_2m, h_ne0, h_p_eq0, h_n_ne0,
                  h0_ne1, Pi.single_apply, Fin.ext_iff]
              · have hr_ne1 : r.val ≠ 1 := fun h => hrt (Fin.ext (h.trans ht1.symm))
                have hrt1 : r ≠ ⟨1, by omega⟩ := Fin.ne_of_val_ne hr_ne1
                have hne_end1 : 1 + 1 ≠ 2 * m + 1 := by omega
                have h1_ne_end : (1 : ℕ) ≠ 2 * m + 1 := by omega
                have h2le2 : (2 : ℕ) ≤ 1 + 1 := by omega
                have hnot_le2_1 : ¬((2 : ℕ) ≤ 1) := by omega
                simp only [hrt1, ht2m, ht2, ht1, h2t1, h2le2, hnot_le2_1, hm0, hne_end1, h1_ne_end,
                  ↓reduceIte, Pi.sub_apply]
                simp only [Pi.single_apply, Fin.ext_iff, Fin.val_mk, Fin.val_zero]
                split_ifs <;> first | ring | (exfalso; omega)
            · have ht0 : t = 0 := by omega
              have ht1_eq : t + 1 = 1 := by omega
              have hm0 : m ≠ 0 := by omega
              by_cases hrt : r = ⟨t, ht_lt⟩
              · subst hrt
                have hm_ne0 : 2 * m ≠ 0 := by omega
                have hm_ne1 : 2 * m ≠ 1 := by omega
                simp [ht0, ht1_eq, hm0, Pi.single_apply]
              · have hr_ne0 : r.val ≠ 0 := fun h => hrt (Fin.ext (h.trans ht0.symm))
                have hrt0 : r ≠ ⟨0, by omega⟩ := Fin.ne_of_val_ne hr_ne0
                have h01_ne : 0 + 1 ≠ 2 * m + 1 := by omega
                have h0_ne_end : (0 : ℕ) ≠ 2 * m + 1 := by omega
                have hnot_le2 : ¬((2 : ℕ) ≤ 0 + 1) := by omega
                have hnot_le2_0 : ¬((2 : ℕ) ≤ 0) := by omega
                have h0_ne_1 : (0 : ℕ) ≠ 1 := by omega
                simp only [hrt0, ht0, ht1_eq, h01_ne, h0_ne_end, hnot_le2, hnot_le2_0, h0_ne_1,
                  ↓reduceIte, Pi.sub_apply, Pi.neg_apply, hm0]
                have h0_ne_r : (0 : ℕ) ≠ r.val := hr_ne0.symm
                by_cases hr1 : r.val = 1
                · simp only [Pi.single_apply, Fin.ext_iff, Fin.val_mk, Fin.val_zero, h0_ne_r,
                    hr1, ↓reduceIte]
                  norm_num
                · simp only [Pi.single_apply, Fin.ext_iff, Fin.val_mk, Fin.val_zero, hr_ne0,
                    hr1, ↓reduceIte]
                  ring
    have h0 := hstep0 (2 * m + 1) (le_refl _)
    rw [Nat.sub_self, suffixProd_zero m hm] at h0
    rw [h0]
    ext r
    simp [hj0, basisV, Pi.single_apply, Fin.ext_iff]
  have hstep : ∀ (d : ℕ) (hd : d ≤ 2 * m + 1),
      (suffixProd m (2 * m + 1 - d)).mulVec (basisV m hm j) =
        if 2 * m + 1 - d ≤ j.val then -basisV m hm ⟨j.val + 1, hj⟩
        else if 2 * m + 1 - d = j.val + 1 then
          basisV m hm j - Pi.single ⟨j.val + 1, by omega⟩ (1 : ℝ)
        else basisV m hm j := by
    intro d
    induction d with
    | zero =>
      intro _
      rw [Nat.sub_zero, suffixProd_ge m (le_refl _), Matrix.one_mulVec]
      have h1 : ¬(2 * m + 1 ≤ j.val) := by omega
      have h2 : 2 * m + 1 ≠ j.val + 1 := by omega
      rw [if_neg h1, if_neg h2]
    | succ d ih =>
      intro hd
      set t := 2 * m + 1 - (d + 1)
      have ht_lt : t < 2 * m + 1 := by omega
      have ht_succ : t + 1 = 2 * m + 1 - d := by omega
      rw [suffixProd_step m ht_lt, ← Matrix.mulVec_mulVec, ht_succ, ih (by omega), ← ht_succ]
      by_cases hle : t + 1 ≤ j.val
      · have hle' : t ≤ j.val := by omega
        have hne_eq : t + 1 ≠ j.val + 1 := by omega
        have hle_d : 2 * m + 1 - d ≤ j.val := by omega
        have hne_d : 2 * m + 1 - d ≠ j.val + 1 := by omega
        simp only [hle, hle', hne_eq, hle_d, hne_d, ↓reduceIte, Matrix.mulVec_neg]
        congr 1
        ext r
        rw [reflectionMatrix_oddCycle_mulVec m hm]
        by_cases hrt : r = ⟨t, ht_lt⟩
        · subst hrt
          have hne_end : t ≠ 2 * m := by omega
          by_cases ht0 : t = 0
          · have hm0 : m ≠ 0 := by omega
            have h1_ne : (1 : ℕ) ≠ j.val + 1 := by omega
            have h2m_ne : 2 * m ≠ j.val + 1 := by omega
            have h0_ne : (0 : ℕ) ≠ j.val + 1 := by omega
            simp only [ht0, hne_end, ↓reduceIte, Pi.neg_apply, basisV, Fin.val_mk,
              Nat.add_eq_zero_iff, one_ne_zero, and_false, Pi.single_apply, Fin.ext_iff,
              h1_ne, h2m_ne, h0_ne, hm0, hj0]
            simp [hm0, hj0, h1_ne, h2m_ne, h0_ne]
          · simp only [↓reduceIte, ht0, hne_end, basisV, Fin.val_mk, Nat.add_eq_zero_iff,
              one_ne_zero, and_false, Pi.single_apply, Fin.ext_iff]
            have : t ≠ j.val + 1 := by omega
            have : t - 1 ≠ j.val + 1 := by omega
            have : t + 1 ≠ j.val + 1 := by omega
            simp [*, hne_d]
        · simp [hrt]
      · by_cases heq : t + 1 = j.val + 1
        · have hle' : t ≤ j.val := by omega
          have heq_t : t = j.val := by omega
          simp only [hle, heq, hle', ↓reduceIte]
          ext r
          rw [reflectionMatrix_oddCycle_mulVec m hm]
          by_cases hrt : r = ⟨t, ht_lt⟩
          · subst hrt
            have hne_end : t ≠ 2 * m := by omega
            have ht0 : t ≠ 0 := by omega
            simp only [ht0, hne_end, hj0, basisV, ↓reduceIte, Pi.sub_apply, Pi.single_apply,
              Fin.ext_iff, Fin.val_mk, Nat.add_eq_zero_iff, one_ne_zero, and_false]
            have : t ≠ j.val + 1 := by omega
            have : t - 1 ≠ j.val + 1 := by omega
            have : t + 1 = j.val + 1 := by omega
            have : j.val ≠ j.val - 1 := by omega
            simp [*]
          · have hnot_le_jj : ¬(j.val + 1 ≤ j.val) := by omega
            simp only [hrt, hnot_le_jj, ↓reduceIte, Pi.sub_apply, Pi.neg_apply, basisV, Fin.val_mk,
              Nat.add_eq_zero_iff, one_ne_zero, and_false, hj0, Pi.single_apply, Fin.ext_iff]
            have hr_nej : r.val ≠ j.val := fun h => hrt (Fin.ext (h.trans heq_t.symm))
            by_cases hrj1 : r.val = j.val + 1
            · simp [hr_nej, hrj1]
            · simp [hr_nej, hrj1, Ne.symm hrj1]
        · have hnot_le : ¬(t ≤ j.val) := by omega
          by_cases heq' : t = j.val + 1
          · simp only [hle, heq, hnot_le, heq', ↓reduceIte]
            ext r
            rw [reflectionMatrix_oddCycle_mulVec m hm]
            by_cases hrt : r = ⟨t, ht_lt⟩
            · subst hrt
              have ht0 : t ≠ 0 := by omega
              have hne_end : t ≠ 2 * m := by omega
              simp only [ht0, hj0, hne_end, basisV, ↓reduceIte, Pi.single_apply, Fin.ext_iff, Fin.val_mk]
              have : t ≠ j.val := by omega
              have : t - 1 = j.val := by omega
              have : t + 1 ≠ j.val := by omega
              have hne_m2 : 1 + j.val ≠ m * 2 := by omega
              have hne_2m : j.val + 1 ≠ 2 * m := by omega
              have hj_ne_j2 : j.val ≠ 2 + j.val := by omega
              have hj_ne_j2' : j.val ≠ j.val + 1 + 1 := by omega
              simp [*, hne_m2, hne_2m, hj_ne_j2, hj_ne_j2']
            · have hrt' : r ≠ ⟨j.val + 1, by omega⟩ := fun h => by
                simp only [Fin.ext_iff, Fin.val_mk] at h
                exact hrt (Fin.ext (h.trans heq'.symm))
              simp [hrt, hrt']
          · simp only [hle, heq, hnot_le, heq', ↓reduceIte]
            ext r
            rw [reflectionMatrix_oddCycle_mulVec m hm]
            by_cases hrt : r = ⟨t, ht_lt⟩
            · subst hrt
              have ht0 : t ≠ 0 := by omega
              have hne_dj : 2 * m + 1 - d ≠ j.val := by omega
              by_cases hne_end : t = 2 * m
              · simp only [ht0, hne_end, hj0, basisV, ↓reduceIte, Pi.single_apply, Fin.ext_iff, Fin.val_mk]
                have : 2 * m ≠ j.val := by omega
                have : 0 ≠ j.val := by omega
                have : 2 * m - 1 ≠ j.val := by omega
                simp [*, hne_dj]
              · simp only [ht0, hne_end, hj0, basisV, ↓reduceIte, Pi.single_apply, Fin.ext_iff, Fin.val_mk]
                have : t ≠ j.val := by omega
                have : t - 1 ≠ j.val := by omega
                have : t + 1 ≠ j.val := by omega
                simp [*, hne_dj]
            · simp [hrt]
  have h0 := hstep (2 * m + 1) (le_refl _)
  rw [Nat.sub_self, suffixProd_zero m hm] at h0
  simpa using h0

private lemma w_mulVec_basisV_last (m : ℕ) (hm : 1 ≤ m) :
    (w_oddCycleSinglePlus m hm).mulVec (basisV m hm ⟨2 * m - 1, by omega⟩) =
      -basisV m hm ⟨0, by omega⟩ + (2 : ℝ) • altVec m := by
  have hstep : ∀ (d : ℕ) (hd : d ≤ 2 * m + 1),
      (suffixProd m (2 * m + 1 - d)).mulVec (basisV m hm ⟨2 * m - 1, by omega⟩) =
        fun r =>
          if 2 * m + 1 - d = 0 then
            (-basisV m hm ⟨0, by omega⟩ + (2 : ℝ) • altVec m) r
          else if r.val < 2 * m + 1 - d then
            if r.val = 2 * m - 1 then 1 else 0
          else if r.val = 2 * m then 1
          else (2 : ℝ) * (-1 : ℝ) ^ r.val := by
    intro d
    induction d with
    | zero =>
      intro _
      rw [Nat.sub_zero, suffixProd_ge m (le_refl _), Matrix.one_mulVec]
      ext r
      have hne0 : 2 * m + 1 ≠ 0 := by omega
      have hlt : r.val < 2 * m + 1 := r.isLt
      have hne_j : 2 * m - 1 ≠ 0 := by omega
      simp only [hne0, hlt, ↓reduceIte, basisV, Fin.val_mk, hne_j, Pi.single_apply, Fin.ext_iff]
    | succ d ih =>
      intro hd
      set t := 2 * m + 1 - (d + 1)
      have ht_lt : t < 2 * m + 1 := by omega
      have ht_succ : t + 1 = 2 * m + 1 - d := by omega
      rw [suffixProd_step m ht_lt, ← Matrix.mulVec_mulVec, ht_succ, ih (by omega), ← ht_succ]
      ext r
      rw [reflectionMatrix_oddCycle_mulVec m hm]
      by_cases ht0 : t = 0
      · by_cases hrt : r = ⟨t, ht_lt⟩
        · subst hrt
          simp only [ht0, ↓reduceIte, Fin.val_mk, Nat.add_eq_zero_iff, one_ne_zero, and_false,
            Pi.add_apply, Pi.neg_apply, Pi.smul_apply, smul_eq_mul, altVec, pow_zero, mul_one]
          have h1_lt : ¬(1 < 1) := by omega
          have h2m_lt : ¬(2 * m < 1) := by omega
          have h0_lt : (0 : ℕ) < 1 := by omega
          have h0_ne : (0 : ℕ) ≠ 2 * m - 1 := by omega
          have h1_ne : (1 : ℕ) ≠ 2 * m := by omega
          have hm0 : m ≠ 0 := by omega
          simp only [h1_lt, h2m_lt, h0_lt, h0_ne, h1_ne, ↓reduceIte, pow_one]
          simp [hm0, basisV, Pi.single_apply, Fin.ext_iff]
          ring
        · have hrt_val : r.val ≠ 0 := fun h => hrt (Fin.ext (h.trans ht0.symm))
          have h_r_lt : ¬(r.val < 1) := by omega
          simp only [ht0, hrt, ↓reduceIte, h_r_lt, Pi.add_apply, Pi.neg_apply, Pi.smul_apply,
            smul_eq_mul, altVec]
          by_cases hr2m : r.val = 2 * m
          · have hm0 : m ≠ 0 := by omega
            simp [hr2m, hm0, basisV, Pi.single_apply, Fin.ext_iff]
            have : (-1 : ℝ) ^ (2 * m) = 1 := by
              rw [pow_mul]; norm_num
            linarith
          · simp [hr2m, hrt_val, basisV, Pi.single_apply, Fin.ext_iff]
      · have h_t_ne0 : t ≠ 0 := ht0
        have h_t1_ne0 : t + 1 ≠ 0 := by omega
        by_cases hrt : r = ⟨t, ht_lt⟩
        · subst hrt
          simp only [↓reduceIte, h_t_ne0, h_t1_ne0, Fin.val_mk]
          have h_t_lt : t < t + 1 := by omega
          simp only [h_t_lt, ↓reduceIte]
          by_cases ht2m : t = 2 * m
          · have h1 : (2 * m : ℕ) ≠ 2 * m - 1 := by omega
            have h0_lt : (0 : ℕ) < 2 * m + 1 := by omega
            have h0_ne : (0 : ℕ) ≠ 2 * m - 1 := by omega
            have hp_lt : (2 * m - 1 : ℕ) < 2 * m + 1 := by omega
            simp [ht2m, h1, h0_lt, h0_ne, hp_lt]
          · by_cases ht_last : t = 2 * m - 1
            · have h_ne0 : 2 * m - 1 ≠ 0 := by omega
              have h_ne2m : 2 * m - 1 ≠ 2 * m := by omega
              have h_p_lt : (2 * m - 1 - 1 : ℕ) < 2 * m := by omega
              have h_p_ne : (2 * m - 1 - 1 : ℕ) ≠ 2 * m - 1 := by omega
              have h_n_eq : (2 * m - 1 + 1 : ℕ) = 2 * m := by omega
              simp [ht_last, h_ne0, h_ne2m, h_p_lt, h_p_ne, h_n_eq]
              have hpow : (-1 : ℝ) ^ (2 * m - 1) = -1 := by
                have : 2 * m - 1 = 2 * (m - 1) + 1 := by omega
                rw [this, pow_add, pow_mul]
                norm_num
              linarith
            · have h_p_lt : t - 1 < t + 1 := by omega
              have h_p_ne : t - 1 ≠ 2 * m - 1 := by omega
              have h_n_lt : ¬(t + 1 < t + 1) := by omega
              have h_n_ne : t + 1 ≠ 2 * m := by omega
              simp [ht2m, ht_last, h_p_lt, h_p_ne, h_n_lt, h_n_ne]
              have hpow : (-1 : ℝ) ^ t = -((-1 : ℝ) ^ (t + 1)) := by
                rw [pow_succ]; ring
              linarith
        · have hrt_val : r.val ≠ t := fun h => hrt (Fin.ext h)
          simp only [hrt, ↓reduceIte, h_t_ne0, h_t1_ne0]
          by_cases h_lt : r.val < t
          · have h_lt1 : r.val < t + 1 := by omega
            simp [h_lt, h_lt1]
          · have h_nlt1 : ¬(r.val < t + 1) := by omega
            simp [h_lt, h_nlt1]
  have h0 := hstep (2 * m + 1) (le_refl _)
  rw [Nat.sub_self, suffixProd_zero m hm] at h0
  ext r
  simpa [Pi.add_apply, Pi.neg_apply, Pi.smul_apply, smul_eq_mul] using congrFun h0 r

private lemma w_mulVec_last (m : ℕ) (hm : 1 ≤ m) :
    (w_oddCycleSinglePlus m hm).mulVec (Pi.single ⟨2 * m, by omega⟩ (1 : ℝ)) =
      basisV m hm ⟨0, by omega⟩ - Pi.single ⟨2 * m, by omega⟩ (1 : ℝ) - altVec m := by
  have hstep : ∀ (d : ℕ) (hd : d ≤ 2 * m + 1),
      (suffixProd m (2 * m + 1 - d)).mulVec (Pi.single ⟨2 * m, by omega⟩ (1 : ℝ)) =
        fun r =>
          if 2 * m + 1 - d = 2 * m + 1 then
            if r.val = 2 * m then (1 : ℝ) else 0
          else if r.val < 2 * m + 1 - d then 0
          else if r.val = 2 * m then -1
          else if r.val = 0 then 0
          else (-1 : ℝ) ^ (r.val + 1) := by
    intro d
    induction d with
    | zero =>
      intro _
      rw [Nat.sub_zero, suffixProd_ge m (le_refl _), Matrix.one_mulVec]
      ext r
      simp [Pi.single_apply, Fin.ext_iff]
    | succ d ih =>
      intro hd
      set t := 2 * m + 1 - (d + 1)
      have ht_lt : t < 2 * m + 1 := by omega
      have ht_succ : t + 1 = 2 * m + 1 - d := by omega
      rw [suffixProd_step m ht_lt, ← Matrix.mulVec_mulVec, ht_succ, ih (by omega), ← ht_succ]
      ext r
      rw [reflectionMatrix_oddCycle_mulVec m hm]
      have ht_ne_end : t ≠ 2 * m + 1 := by omega
      by_cases ht_eq : t = 2 * m
      · by_cases hrt : r = ⟨t, ht_lt⟩
        · subst hrt
          have h0_ne : (0 : ℕ) ≠ 2 * m := by omega
          have hp_ne : (2 * m - 1 : ℕ) ≠ 2 * m := by omega
          simp [ht_eq, Pi.single_apply, Fin.ext_iff, h0_ne, hp_ne]
        · have hrt_val : r.val ≠ 2 * m := fun h => hrt (Fin.ext (h.trans ht_eq.symm))
          have hr_lt : r.val < 2 * m := by omega
          simp [hrt, ht_eq, ht_ne_end, hr_lt, Pi.single_apply, Fin.ext_iff, hrt_val]
      · have ht1_ne : t + 1 ≠ 2 * m + 1 := by omega
        by_cases hrt : r = ⟨t, ht_lt⟩
        · subst hrt
          have ht_lt_t1 : t < t + 1 := by omega
          simp only [↓reduceIte, ht_ne_end, ht_eq]
          by_cases ht0 : t = 0
          · have h1_ne : (1 : ℕ) ≠ 2 * m := by omega
            have hm0 : 2 * m ≠ 0 := by omega
            simp [ht0, h1_ne, hm0]
          · have hp_lt : t - 1 < t + 1 := by omega
            by_cases ht_last : t = 2 * m - 1
            · have h_ne0 : 2 * m - 1 ≠ 0 := by omega
              have h_p_lt2 : 2 * m - 1 - 1 < 2 * m := by omega
              have h_n_eq : 2 * m - 1 + 1 = 2 * m := by omega
              have hm_pos : 0 < m := by omega
              simp [ht_last, h_ne0, h_p_lt2, h_n_eq, hm_pos]
            · have hn_ne : t + 1 ≠ 2 * m := by omega
              simp [ht0, ht_eq, hp_lt, hn_ne]
              have hpow : (-1 : ℝ) ^ (t + 2) = -((-1 : ℝ) ^ (t + 1)) := by
                rw [pow_succ]; ring
              linarith
        · have hrt_val : r.val ≠ t := fun h => hrt (Fin.ext h)
          simp only [hrt, ↓reduceIte, ht_ne_end, ht1_ne]
          by_cases hr_lt : r.val < t
          · have hr_lt1 : r.val < t + 1 := by omega
            simp only [hr_lt, hr_lt1, ↓reduceIte]
          · have hr_nlt1 : ¬(r.val < t + 1) := by omega
            simp only [hr_lt, hr_nlt1, ↓reduceIte]
  have h0 := hstep (2 * m + 1) (le_refl _)
  rw [Nat.sub_self, suffixProd_zero m hm] at h0
  rw [h0]
  ext r
  have h0_ne : (0 : ℕ) ≠ 2 * m + 1 := by omega
  have hr_nlt : ¬(r.val < 0) := by omega
  simp only [h0_ne, hr_nlt, ↓reduceIte, Pi.sub_apply, basisV, Fin.val_mk,
    Pi.add_apply, Pi.single_apply, Fin.ext_iff, altVec]
  have hm0 : m ≠ 0 := by omega
  by_cases hr0 : r.val = 0
  · simp [hr0, hm0]
  · by_cases hr2m : r.val = 2 * m
    · simp [hr2m, hm0]
    · simp [hr0, hr2m, pow_succ]

private lemma w_pow_basisV_zero (m : ℕ) (hm : 1 ≤ m) (t : ℕ) (ht : t < 2 * m) :
    ((w_oddCycleSinglePlus m hm) ^ t).mulVec (basisV m hm ⟨0, by omega⟩) =
      (-1 : ℝ) ^ t • basisV m hm ⟨t, ht⟩ := by
  induction t with
  | zero => simp
  | succ t ih =>
    rw [pow_succ', ← Matrix.mulVec_mulVec, ih (by omega), Matrix.mulVec_smul,
      w_mulVec_basisV_lt m hm ⟨t, by omega⟩ ht, pow_succ]
    ext r
    simp [smul_eq_mul]

private lemma w_pow_two_m_basisV_zero (m : ℕ) (hm : 1 ≤ m) :
    ((w_oddCycleSinglePlus m hm) ^ (2 * m)).mulVec (basisV m hm ⟨0, by omega⟩) =
      basisV m hm ⟨0, by omega⟩ - (2 : ℝ) • altVec m := by
  have hpow_split : ∀ (A : Matrix (Fin (2 * m + 1)) (Fin (2 * m + 1)) ℝ) (n : ℕ),
      1 ≤ n → A ^ n = A * A ^ (n - 1) := by
    intro A n hn
    cases n with
    | zero => omega
    | succ n => simp [pow_succ']
  rw [hpow_split _ (2 * m) (by omega), ← Matrix.mulVec_mulVec,
    w_pow_basisV_zero m hm (2 * m - 1) (by omega),
    Matrix.mulVec_smul, w_mulVec_basisV_last m hm]
  have hpow : (-1 : ℝ) ^ (2 * m - 1) = -1 := by
    have : 2 * m - 1 = 2 * (m - 1) + 1 := by omega
    rw [this, pow_add, pow_mul]
    norm_num
  rw [hpow]
  ext r
  simp [smul_eq_mul]
  ring

private lemma w_pow_altVec (m : ℕ) (hm : 1 ≤ m) (t : ℕ) :
    ((w_oddCycleSinglePlus m hm) ^ t).mulVec (altVec m) = (-1 : ℝ) ^ t • altVec m := by
  induction t with
  | zero => simp
  | succ t ih =>
    rw [pow_succ', ← Matrix.mulVec_mulVec, ih, Matrix.mulVec_smul, w_mulVec_altVec m hm, pow_succ]
    ext r
    simp [smul_eq_mul]

private lemma w_pow_two_m_sub_one_basisV (m : ℕ) (hm : 1 ≤ m) (j : Fin (2 * m)) :
    ((w_oddCycleSinglePlus m hm) ^ (2 * m) - 1).mulVec (basisV m hm j) = (-2 : ℝ) • altVec m := by
  have hbasis : basisV m hm j =
      (-1 : ℝ) ^ j.val • ((w_oddCycleSinglePlus m hm) ^ j.val).mulVec (basisV m hm ⟨0, by omega⟩) := by
    rw [w_pow_basisV_zero m hm j.val j.isLt, smul_smul, ← pow_add]
    have hpow : (-1 : ℝ) ^ (j.val + j.val) = 1 := by
      rw [← two_mul, pow_mul]
      norm_num
    rw [hpow, one_smul]
  rw [hbasis, Matrix.mulVec_smul, Matrix.sub_mulVec, Matrix.one_mulVec]
  have hcomm : (w_oddCycleSinglePlus m hm) ^ (2 * m) * (w_oddCycleSinglePlus m hm) ^ j.val =
      (w_oddCycleSinglePlus m hm) ^ j.val * (w_oddCycleSinglePlus m hm) ^ (2 * m) := by
    rw [← pow_add, ← pow_add]
    congr 1
    omega
  rw [Matrix.mulVec_mulVec, hcomm, ← Matrix.mulVec_mulVec, w_pow_two_m_basisV_zero m hm]
  rw [Matrix.mulVec_sub, Matrix.mulVec_smul, w_pow_altVec m hm j.val]
  ext r
  simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  have hpow : (-1 : ℝ) ^ j.val * (-1 : ℝ) ^ j.val = 1 := by
    rw [← pow_add, ← two_mul, pow_mul]
    norm_num
  have hring :
      (-1 : ℝ) ^ j.val * ((((w_oddCycleSinglePlus m hm) ^ j.val).mulVec (basisV m hm ⟨0, by omega⟩)) r -
          2 * ((-1 : ℝ) ^ j.val * altVec m r) -
        (((w_oddCycleSinglePlus m hm) ^ j.val).mulVec (basisV m hm ⟨0, by omega⟩)) r) =
      -2 * (((-1 : ℝ) ^ j.val * (-1 : ℝ) ^ j.val) * altVec m r) := by ring
  rw [hring, hpow, one_mul]

private lemma w_add_one_mulVec_altVec (m : ℕ) (hm : 1 ≤ m) :
    (w_oddCycleSinglePlus m hm + 1).mulVec (altVec m) = 0 := by
  rw [Matrix.add_mulVec, w_mulVec_altVec m hm, Matrix.one_mulVec, neg_add_cancel]

private lemma w_poly_mulVec_basisV (m : ℕ) (hm : 1 ≤ m) (j : Fin (2 * m)) :
    ((w_oddCycleSinglePlus m hm + 1) * ((w_oddCycleSinglePlus m hm) ^ (2 * m) - 1)).mulVec
      (basisV m hm j) = 0 := by
  rw [← Matrix.mulVec_mulVec, w_pow_two_m_sub_one_basisV m hm j, Matrix.mulVec_smul,
    w_add_one_mulVec_altVec m hm, smul_zero]

private lemma w_poly_mulVec_last (m : ℕ) (hm : 1 ≤ m) :
    ((w_oddCycleSinglePlus m hm + 1) * ((w_oddCycleSinglePlus m hm) ^ (2 * m) - 1)).mulVec
      (Pi.single ⟨2 * m, by omega⟩ (1 : ℝ)) = (-2 : ℝ) • altVec m := by
  have hcomm : (w_oddCycleSinglePlus m hm + 1) * ((w_oddCycleSinglePlus m hm) ^ (2 * m) - 1) =
      ((w_oddCycleSinglePlus m hm) ^ (2 * m) - 1) * (w_oddCycleSinglePlus m hm + 1) := by
    have hp : w_oddCycleSinglePlus m hm * (w_oddCycleSinglePlus m hm) ^ (2 * m) =
        (w_oddCycleSinglePlus m hm) ^ (2 * m) * w_oddCycleSinglePlus m hm := by
      rw [← pow_succ, ← pow_succ']
    simp only [mul_sub, sub_mul, add_mul, mul_add, one_mul, mul_one, hp]
    abel
  have hstep1 : (w_oddCycleSinglePlus m hm + 1).mulVec (Pi.single ⟨2 * m, by omega⟩ (1 : ℝ)) =
      basisV m hm ⟨0, by omega⟩ - altVec m := by
    rw [Matrix.add_mulVec, w_mulVec_last m hm, Matrix.one_mulVec]
    ext i; simp; ring
  rw [hcomm, ← Matrix.mulVec_mulVec, hstep1, Matrix.mulVec_sub,
    w_pow_two_m_sub_one_basisV m hm ⟨0, by omega⟩, Matrix.sub_mulVec, Matrix.one_mulVec,
    w_pow_altVec m hm (2 * m)]
  have hpow : (-1 : ℝ) ^ (2 * m) = 1 := by rw [pow_mul]; norm_num
  rw [hpow, one_smul, sub_self, sub_zero]

/-- **Minimal annihilating polynomial for the odd-cycle single-defect Coxeter element**:
`(w + 1)^2 * (w^(2*m) - 1) = 0` for all `m ≥ 1` (`k = 2 * m + 1 ≥ 3`).
Every eigenvalue of `w` is `-1` (with Jordan block of size `2`) or a `(2 * m)`-th root of unity,
so the spectral radius is `1` (quasi-unipotent). -/
theorem oddCycleSinglePlus_minimal_poly (m : ℕ) (hm : 1 ≤ m) :
    (w_oddCycleSinglePlus m hm + 1) ^ 2 * ((w_oddCycleSinglePlus m hm) ^ (2 * m) - 1) = 0 := by
  ext r c
  rw [Matrix.zero_apply]
  set M := (w_oddCycleSinglePlus m hm + 1) ^ 2 * ((w_oddCycleSinglePlus m hm) ^ (2 * m) - 1)
  have hcol : M.mulVec (Pi.single c (1 : ℝ)) = 0 := by
    by_cases hc0 : c.val = 0
    · have hc : c = ⟨0, by omega⟩ := Fin.ext hc0
      have hsing : Pi.single c (1 : ℝ) =
          basisV m hm ⟨0, by omega⟩ - Pi.single ⟨2 * m, by omega⟩ (1 : ℝ) := by
        rw [hc]
        simp [basisV]
      rw [hsing, Matrix.mulVec_sub]
      have h1 : M.mulVec (basisV m hm ⟨0, by omega⟩) = 0 := by
        simp only [M, pow_two, mul_assoc]
        rw [← Matrix.mulVec_mulVec, w_poly_mulVec_basisV m hm ⟨0, by omega⟩, Matrix.mulVec_zero]
      have h2 : M.mulVec (Pi.single ⟨2 * m, by omega⟩ (1 : ℝ)) = 0 := by
        simp only [M, pow_two, mul_assoc]
        rw [← Matrix.mulVec_mulVec, w_poly_mulVec_last m hm, Matrix.mulVec_smul,
          w_add_one_mulVec_altVec m hm, smul_zero]
      rw [h1, h2, sub_zero]
    · by_cases hc2m : c.val = 2 * m
      · have hc : c = ⟨2 * m, by omega⟩ := Fin.ext hc2m
        rw [hc]
        simp only [M, pow_two, mul_assoc]
        rw [← Matrix.mulVec_mulVec, w_poly_mulVec_last m hm, Matrix.mulVec_smul,
          w_add_one_mulVec_altVec m hm, smul_zero]
      · have hsing : Pi.single c (1 : ℝ) = basisV m hm ⟨c.val, by omega⟩ := by
          simp [basisV, hc0]
        rw [hsing]
        simp only [M, pow_two, mul_assoc]
        rw [← Matrix.mulVec_mulVec, w_poly_mulVec_basisV m hm ⟨c.val, by omega⟩, Matrix.mulVec_zero]
  simpa [Matrix.mulVec_single] using congrFun hcol r

/-- The Jordan block at `-1` is genuine (size `2`, not `1`): `(w + 1) * (w^(2*m) - 1) ≠ 0`. -/
theorem oddCycleSinglePlus_ne_neg_one_poly (m : ℕ) (hm : 1 ≤ m) :
    (w_oddCycleSinglePlus m hm + 1) * ((w_oddCycleSinglePlus m hm) ^ (2 * m) - 1) ≠ 0 := by
  intro h
  have hmul : ((w_oddCycleSinglePlus m hm + 1) * ((w_oddCycleSinglePlus m hm) ^ (2 * m) - 1)).mulVec
      (Pi.single ⟨2 * m, by omega⟩ (1 : ℝ)) = 0 := by
    rw [h, Matrix.zero_mulVec]
  rw [w_poly_mulVec_last m hm] at hmul
  have h0 := congrFun hmul ⟨0, by omega⟩
  simp [altVec] at h0

/-- Any real eigenvalue `μ` of `w_oddCycleSinglePlus m hm` satisfies `μ = 1 ∨ μ = -1`
(hence the real spectral radius is `1`). -/
theorem oddCycleSinglePlus_eigenvalue_mem (m : ℕ) (hm : 1 ≤ m)
    (μ : ℝ) (v : Fin (2 * m + 1) → ℝ) (hv : v ≠ 0)
    (heig : (w_oddCycleSinglePlus m hm).mulVec v = μ • v) :
    μ = 1 ∨ μ = -1 := by
  have hpow : ∀ k : ℕ, ((w_oddCycleSinglePlus m hm) ^ k).mulVec v = (μ ^ k) • v := by
    intro k
    induction k with
    | zero => simp [Matrix.one_mulVec]
    | succ k ih =>
      rw [pow_succ', ← Matrix.mulVec_mulVec, ih, Matrix.mulVec_smul, heig, smul_smul, ← pow_succ]
  have hadd : (w_oddCycleSinglePlus m hm + 1).mulVec v = (μ + 1) • v := by
    rw [Matrix.add_mulVec, heig, Matrix.one_mulVec, add_smul, one_smul]
  have hadd2 : ((w_oddCycleSinglePlus m hm + 1) ^ 2).mulVec v = ((μ + 1) ^ 2) • v := by
    rw [pow_two, ← Matrix.mulVec_mulVec, hadd, Matrix.mulVec_smul, hadd, smul_smul, ← pow_two]
  have hsub : ((w_oddCycleSinglePlus m hm) ^ (2 * m) - 1).mulVec v = (μ ^ (2 * m) - 1) • v := by
    rw [Matrix.sub_mulVec, hpow (2 * m), Matrix.one_mulVec, sub_smul, one_smul]
  have hmul : (((w_oddCycleSinglePlus m hm + 1) ^ 2 *
      ((w_oddCycleSinglePlus m hm) ^ (2 * m) - 1)).mulVec v) =
      ((μ + 1) ^ 2 * (μ ^ (2 * m) - 1)) • v := by
    rw [← Matrix.mulVec_mulVec, hsub, Matrix.mulVec_smul, hadd2, smul_smul]
    rw [mul_comm (μ ^ (2 * m) - 1) ((μ + 1) ^ 2)]
  rw [oddCycleSinglePlus_minimal_poly m hm, Matrix.zero_mulVec] at hmul
  have hscalar : (μ + 1) ^ 2 * (μ ^ (2 * m) - 1) = 0 := by
    by_contra hne
    apply hv
    have hzero := congrArg (fun x => ((μ + 1) ^ 2 * (μ ^ (2 * m) - 1))⁻¹ • x) hmul.symm
    rw [smul_smul, inv_mul_cancel₀ hne, one_smul, smul_zero] at hzero
    exact hzero
  rcases mul_eq_zero.mp hscalar with h1 | h2
  · right
    have : μ + 1 = 0 := sq_eq_zero_iff.mp h1
    linarith
  · have hpow_eq : (μ ^ 2) ^ m = (1 : ℝ) ^ m := by
      rw [← pow_mul, one_pow]
      exact sub_eq_zero.mp h2
    have hsq : μ ^ 2 = 1 := by
      have hm0 : m ≠ 0 := by omega
      exact (pow_left_inj₀ (sq_nonneg μ) zero_le_one hm0).mp hpow_eq
    exact sq_eq_one_iff.mp hsq

end OddCycleSingleDefect

end MixedSignCoxeter
