import Aegis.StrongPasswordChecker.Code.Funs

/-!
# Specifications of `Aegis.StrongPasswordChecker.strong_password_checker`

LeetCode problem `strong-password-checker`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

namespace AegisSpec.StrongPasswordChecker

def IsLower (b : Std.U8) : Prop := 97 ≤ b.val ∧ b.val ≤ 122

def IsUpper (b : Std.U8) : Prop := 65 ≤ b.val ∧ b.val ≤ 90

def IsDigit (b : Std.U8) : Prop := 48 ≤ b.val ∧ b.val ≤ 57

def IsAllowed (b : Std.U8) : Prop :=
  IsLower b ∨ IsUpper b ∨ IsDigit b ∨ b.val = 46 ∨ b.val = 33

def ContainsLower (p : List Std.U8) : Prop := ∃ b, b ∈ p ∧ IsLower b

def ContainsUpper (p : List Std.U8) : Prop := ∃ b, b ∈ p ∧ IsUpper b

def ContainsDigit (p : List Std.U8) : Prop := ∃ b, b ∈ p ∧ IsDigit b

def hasLower (p : List Std.U8) : Bool := p.any (fun b => decide (97 ≤ b.val ∧ b.val ≤ 122))

def hasUpper (p : List Std.U8) : Bool := p.any (fun b => decide (65 ≤ b.val ∧ b.val ≤ 90))

def hasDigit (p : List Std.U8) : Bool := p.any (fun b => decide (48 ≤ b.val ∧ b.val ≤ 57))

def MissingCount (p : List Std.U8) : ℕ :=
  (if hasLower p then 0 else 1) + (if hasUpper p then 0 else 1) + (if hasDigit p then 0 else 1)

def NoThreeConsecutive (p : List Std.U8) : Prop :=
  ∀ (i : ℕ) (_hi : i + 3 ≤ p.length),
    p[i]'(by omega) ≠ p[i + 1]'(by omega) ∨ p[i + 1]'(by omega) ≠ p[i + 2]'(by omega)

def Strong (t : List Std.U8) : Prop :=
  6 ≤ t.length ∧ t.length ≤ 20 ∧
    ContainsLower t ∧ ContainsUpper t ∧ ContainsDigit t ∧ NoThreeConsecutive t

def IsMaximalRun (p : List Std.U8) (a b : ℕ) : Prop :=
  ∃ (_hab : a < b) (_hb : b ≤ p.length),
    (∀ (j : ℕ) (haj : a ≤ j) (hjb : j < b), p[j]'(by omega) = p[a]'(by omega)) ∧
    (a = 0 ∨ p[a - 1]'(by omega) ≠ p[a]'(by omega)) ∧
    (b = p.length ∨ ∃ hlt : b < p.length, p[b]'hlt ≠ p[a]'(by omega))

def runLengthsFrom (c : Std.U8) (n : ℕ) : List Std.U8 → List ℕ
  | [] => [n]
  | b :: rest => if b = c then runLengthsFrom c (n + 1) rest else n :: runLengthsFrom b 1 rest

def runLengths : List Std.U8 → List ℕ
  | [] => []
  | c :: rest => runLengthsFrom c 1 rest

def RunScore (p : List Std.U8) : ℕ := ((runLengths p).map (fun L => L / 3)).sum

inductive EditStep : List Std.U8 → List Std.U8 → Prop where
  | insert (pre post : List Std.U8) (c : Std.U8) :
      EditStep (pre ++ post) (pre ++ [c] ++ post)
  | delete (pre post : List Std.U8) (c : Std.U8) :
      EditStep (pre ++ [c] ++ post) (pre ++ post)
  | subst (pre post : List Std.U8) (c d : Std.U8) :
      EditStep (pre ++ [c] ++ post) (pre ++ [d] ++ post)

def EditChain (x : List Std.U8) : List Std.U8 → ℕ → Prop
  | y, 0 => x = y
  | y, k + 1 => ∃ z, EditChain x z k ∧ EditStep z y

noncomputable def Dist (x y : List Std.U8) : ℕ := sInf { k : ℕ | EditChain x y k }

/-- The function returns a result r such that r = min { dist(password, t) | t is a byte array and strong(t) holds }, where: (1) strong(t) means 6 <= len(t) <= 20, t contains at least one ASCII lowercase letter, at least one ASCII uppercase letter, and at least one ASCII digit, and there is no index i with 0 <= i <= len(t)-3 such that t[i] = t[i+1] = t[i+2]; (2) dist(x, y) is the minimum number of single-character insertions, deletions, and substitutions needed to transform x into y.
  Preconditions: password is a byte slice with 1 <= len(password) <= 50, and every byte is one of: an ASCII lowercase letter ('a'..'z'), an ASCII uppercase letter ('A'..'Z'), an ASCII digit ('0'..'9'), the byte '.' (46), or the byte '!' (33). -/
theorem spec_1 (password : Slice Std.U8)
    (hpre_len : 1 ≤ password.val.length) (hpre_len_max : password.val.length ≤ 50)
    (hpre_bytes : ∀ b, b ∈ password.val → IsAllowed b) :
    ∃ r : I64, Aegis.StrongPasswordChecker.strong_password_checker password = ok r ∧
      ∃ d : ℕ, r.val = (d : ℤ) ∧
        (∃ t : List Std.U8, Strong t ∧ Dist password.val t = d) ∧
        (∀ t : List Std.U8, Strong t → d ≤ Dist password.val t) := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (password : Slice Std.U8)
    (hpre_len : 1 ≤ password.val.length) (hpre_len_max : password.val.length ≤ 50)
    (hpre_bytes : ∀ b, b ∈ password.val → IsAllowed b), ∃ r : I64, Aegis.StrongPasswordChecker.strong_password_checker password = ok r ∧
      ∃ d : ℕ, r.val = (d : ℤ) ∧
        (∃ t : List Std.U8, Strong t ∧ Dist password.val t = d) ∧
        (∀ t : List Std.U8, Strong t → d ≤ Dist password.val t)) := by
  sorry

/-- The function returns a result r (it does not fail, panic, or overflow).
  Preconditions: password is a byte slice with 1 <= len(password) <= 50, and every byte is one of: an ASCII lowercase letter ('a'..'z'), an ASCII uppercase letter ('A'..'Z'), an ASCII digit ('0'..'9'), the byte '.' (46), or the byte '!' (33). -/
theorem spec_2 (password : Slice Std.U8)
    (hpre_len : 1 ≤ password.val.length) (hpre_len_max : password.val.length ≤ 50)
    (hpre_bytes : ∀ b, b ∈ password.val → IsAllowed b) :
    ∃ r : I64, Aegis.StrongPasswordChecker.strong_password_checker password = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (password : Slice Std.U8)
    (hpre_len : 1 ≤ password.val.length) (hpre_len_max : password.val.length ≤ 50)
    (hpre_bytes : ∀ b, b ∈ password.val → IsAllowed b), ∃ r : I64, Aegis.StrongPasswordChecker.strong_password_checker password = ok r) := by
  sorry

/-- The function returns a result r with 0 <= r <= 36.
  Preconditions: password is a byte slice with 1 <= len(password) <= 50, and every byte is one of: an ASCII lowercase letter ('a'..'z'), an ASCII uppercase letter ('A'..'Z'), an ASCII digit ('0'..'9'), the byte '.' (46), or the byte '!' (33). -/
theorem spec_3 (password : Slice Std.U8)
    (hpre_len : 1 ≤ password.val.length) (hpre_len_max : password.val.length ≤ 50)
    (hpre_bytes : ∀ b, b ∈ password.val → IsAllowed b) :
    ∃ r : I64, Aegis.StrongPasswordChecker.strong_password_checker password = ok r ∧
      0 ≤ r.val ∧ r.val ≤ 36 := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (password : Slice Std.U8)
    (hpre_len : 1 ≤ password.val.length) (hpre_len_max : password.val.length ≤ 50)
    (hpre_bytes : ∀ b, b ∈ password.val → IsAllowed b), ∃ r : I64, Aegis.StrongPasswordChecker.strong_password_checker password = ok r ∧
      0 ≤ r.val ∧ r.val ≤ 36) := by
  sorry

/-- The function returns a result r with r >= max(0, 6 - len(password)) + max(0, len(password) - 20).
  Preconditions: password is a byte slice with 1 <= len(password) <= 50, and every byte is one of: an ASCII lowercase letter ('a'..'z'), an ASCII uppercase letter ('A'..'Z'), an ASCII digit ('0'..'9'), the byte '.' (46), or the byte '!' (33). -/
theorem spec_4 (password : Slice Std.U8)
    (hpre_len : 1 ≤ password.val.length) (hpre_len_max : password.val.length ≤ 50)
    (hpre_bytes : ∀ b, b ∈ password.val → IsAllowed b) :
    ∃ r : I64, Aegis.StrongPasswordChecker.strong_password_checker password = ok r ∧
      max 0 (6 - (password.val.length : ℤ)) + max 0 ((password.val.length : ℤ) - 20) ≤ r.val := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (password : Slice Std.U8)
    (hpre_len : 1 ≤ password.val.length) (hpre_len_max : password.val.length ≤ 50)
    (hpre_bytes : ∀ b, b ∈ password.val → IsAllowed b), ∃ r : I64, Aegis.StrongPasswordChecker.strong_password_checker password = ok r ∧
      max 0 (6 - (password.val.length : ℤ)) + max 0 ((password.val.length : ℤ) - 20) ≤ r.val) := by
  sorry

/-- Let m be the number of categories among {lowercase letter, uppercase letter, digit} that do not occur in password. The function returns a result r with r >= m.
  Preconditions: password is a byte slice with 1 <= len(password) <= 50, and every byte is one of: an ASCII lowercase letter ('a'..'z'), an ASCII uppercase letter ('A'..'Z'), an ASCII digit ('0'..'9'), the byte '.' (46), or the byte '!' (33). -/
theorem spec_5 (password : Slice Std.U8)
    (hpre_len : 1 ≤ password.val.length) (hpre_len_max : password.val.length ≤ 50)
    (hpre_bytes : ∀ b, b ∈ password.val → IsAllowed b) :
    ∃ r : I64, Aegis.StrongPasswordChecker.strong_password_checker password = ok r ∧
      (MissingCount password.val : ℤ) ≤ r.val := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (password : Slice Std.U8)
    (hpre_len : 1 ≤ password.val.length) (hpre_len_max : password.val.length ≤ 50)
    (hpre_bytes : ∀ b, b ∈ password.val → IsAllowed b), ∃ r : I64, Aegis.StrongPasswordChecker.strong_password_checker password = ok r ∧
      (MissingCount password.val : ℤ) ≤ r.val) := by
  sorry

/-- Let R be the sum over all maximal contiguous runs of identical bytes in password of length L >= 3 of floor(L/3). The function returns a result r with r >= R. (A maximal contiguous run is a non-empty interval [a,b) with 0 <= a < b <= len(password) such that password[j] = password[a] for all a <= j < b, and either a=0 or password[a-1] != password[a], and either b=len(password) or password[b] != password[a].)
  Preconditions: password is a byte slice with 1 <= len(password) <= 50, and every byte is one of: an ASCII lowercase letter ('a'..'z'), an ASCII uppercase letter ('A'..'Z'), an ASCII digit ('0'..'9'), the byte '.' (46), or the byte '!' (33). -/
theorem spec_6 (password : Slice Std.U8)
    (hpre_len : 1 ≤ password.val.length) (hpre_len_max : password.val.length ≤ 50)
    (hpre_bytes : ∀ b, b ∈ password.val → IsAllowed b) :
    ∃ r : I64, Aegis.StrongPasswordChecker.strong_password_checker password = ok r ∧
      (RunScore password.val : ℤ) ≤ r.val := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (password : Slice Std.U8)
    (hpre_len : 1 ≤ password.val.length) (hpre_len_max : password.val.length ≤ 50)
    (hpre_bytes : ∀ b, b ∈ password.val → IsAllowed b), ∃ r : I64, Aegis.StrongPasswordChecker.strong_password_checker password = ok r ∧
      (RunScore password.val : ℤ) ≤ r.val) := by
  sorry

/-- The function returns a result r with r = 0 if and only if password is strong (as defined in spec_1).
  Preconditions: password is a byte slice with 1 <= len(password) <= 50, and every byte is one of: an ASCII lowercase letter ('a'..'z'), an ASCII uppercase letter ('A'..'Z'), an ASCII digit ('0'..'9'), the byte '.' (46), or the byte '!' (33). -/
theorem spec_7 (password : Slice Std.U8)
    (hpre_len : 1 ≤ password.val.length) (hpre_len_max : password.val.length ≤ 50)
    (hpre_bytes : ∀ b, b ∈ password.val → IsAllowed b) :
    ∃ r : I64, Aegis.StrongPasswordChecker.strong_password_checker password = ok r ∧
      (r.val = 0 ↔ Strong password.val) := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (password : Slice Std.U8)
    (hpre_len : 1 ≤ password.val.length) (hpre_len_max : password.val.length ≤ 50)
    (hpre_bytes : ∀ b, b ∈ password.val → IsAllowed b), ∃ r : I64, Aegis.StrongPasswordChecker.strong_password_checker password = ok r ∧
      (r.val = 0 ↔ Strong password.val)) := by
  sorry

/-- Let r be the returned result. There exists a byte array t such that strong(t) holds (as defined in spec_1) and dist(password, t) = r, where dist is defined in spec_1.
  Preconditions: password is a byte slice with 1 <= len(password) <= 50, and every byte is one of: an ASCII lowercase letter ('a'..'z'), an ASCII uppercase letter ('A'..'Z'), an ASCII digit ('0'..'9'), the byte '.' (46), or the byte '!' (33). -/
theorem spec_8 (password : Slice Std.U8)
    (hpre_len : 1 ≤ password.val.length) (hpre_len_max : password.val.length ≤ 50)
    (hpre_bytes : ∀ b, b ∈ password.val → IsAllowed b) :
    ∃ r : I64, Aegis.StrongPasswordChecker.strong_password_checker password = ok r ∧
      ∃ t : List Std.U8, Strong t ∧ r.val = (Dist password.val t : ℤ) := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (password : Slice Std.U8)
    (hpre_len : 1 ≤ password.val.length) (hpre_len_max : password.val.length ≤ 50)
    (hpre_bytes : ∀ b, b ∈ password.val → IsAllowed b), ∃ r : I64, Aegis.StrongPasswordChecker.strong_password_checker password = ok r ∧
      ∃ t : List Std.U8, Strong t ∧ r.val = (Dist password.val t : ℤ)) := by
  sorry

/-- Let r be the returned result. For every byte array t, if strong(t) holds (as defined in spec_1), then r <= dist(password, t), where dist is defined in spec_1.
  Preconditions: password is a byte slice with 1 <= len(password) <= 50, and every byte is one of: an ASCII lowercase letter ('a'..'z'), an ASCII uppercase letter ('A'..'Z'), an ASCII digit ('0'..'9'), the byte '.' (46), or the byte '!' (33). -/
theorem spec_9 (password : Slice Std.U8)
    (hpre_len : 1 ≤ password.val.length) (hpre_len_max : password.val.length ≤ 50)
    (hpre_bytes : ∀ b, b ∈ password.val → IsAllowed b) :
    ∃ r : I64, Aegis.StrongPasswordChecker.strong_password_checker password = ok r ∧
      ∀ t : List Std.U8, Strong t → r.val ≤ (Dist password.val t : ℤ) := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (password : Slice Std.U8)
    (hpre_len : 1 ≤ password.val.length) (hpre_len_max : password.val.length ≤ 50)
    (hpre_bytes : ∀ b, b ∈ password.val → IsAllowed b), ∃ r : I64, Aegis.StrongPasswordChecker.strong_password_checker password = ok r ∧
      ∀ t : List Std.U8, Strong t → r.val ≤ (Dist password.val t : ℤ)) := by
  sorry

/-- The function returns a result r with r <= max(0, 6 - len(password)) + max(0, len(password) - 20) + 6.
  Preconditions: password is a byte slice with 1 <= len(password) <= 50, and every byte is one of: an ASCII lowercase letter ('a'..'z'), an ASCII uppercase letter ('A'..'Z'), an ASCII digit ('0'..'9'), the byte '.' (46), or the byte '!' (33). -/
theorem spec_10 (password : Slice Std.U8)
    (hpre_len : 1 ≤ password.val.length) (hpre_len_max : password.val.length ≤ 50)
    (hpre_bytes : ∀ b, b ∈ password.val → IsAllowed b) :
    ∃ r : I64, Aegis.StrongPasswordChecker.strong_password_checker password = ok r ∧
      r.val ≤ max 0 (6 - (password.val.length : ℤ)) +
        max 0 ((password.val.length : ℤ) - 20) + 6 := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (password : Slice Std.U8)
    (hpre_len : 1 ≤ password.val.length) (hpre_len_max : password.val.length ≤ 50)
    (hpre_bytes : ∀ b, b ∈ password.val → IsAllowed b), ∃ r : I64, Aegis.StrongPasswordChecker.strong_password_checker password = ok r ∧
      r.val ≤ max 0 (6 - (password.val.length : ℤ)) +
        max 0 ((password.val.length : ℤ) - 20) + 6) := by
  sorry

/-- The function returns a result r with r <= len(password) + 5.
  Preconditions: password is a byte slice with 1 <= len(password) <= 50, and every byte is one of: an ASCII lowercase letter ('a'..'z'), an ASCII uppercase letter ('A'..'Z'), an ASCII digit ('0'..'9'), the byte '.' (46), or the byte '!' (33). -/
theorem spec_11 (password : Slice Std.U8)
    (hpre_len : 1 ≤ password.val.length) (hpre_len_max : password.val.length ≤ 50)
    (hpre_bytes : ∀ b, b ∈ password.val → IsAllowed b) :
    ∃ r : I64, Aegis.StrongPasswordChecker.strong_password_checker password = ok r ∧
      r.val ≤ (password.val.length : ℤ) + 5 := by
  sorry

theorem spec_11_neg :
    ¬ (∀ (password : Slice Std.U8)
    (hpre_len : 1 ≤ password.val.length) (hpre_len_max : password.val.length ≤ 50)
    (hpre_bytes : ∀ b, b ∈ password.val → IsAllowed b), ∃ r : I64, Aegis.StrongPasswordChecker.strong_password_checker password = ok r ∧
      r.val ≤ (password.val.length : ℤ) + 5) := by
  sorry

/-- Let m be the number of categories among {lowercase letter, uppercase letter, digit} that do not occur in password. The function returns a result r with r = max(6 - len(password), m).
  Preconditions: password is a byte slice with 1 <= len(password) <= 50, every byte is one of: an ASCII lowercase letter ('a'..'z'), an ASCII uppercase letter ('A'..'Z'), an ASCII digit ('0'..'9'), the byte '.' (46), or the byte '!' (33); and len(password) < 6. -/
theorem spec_12 (password : Slice Std.U8)
    (hpre_len : 1 ≤ password.val.length) (hpre_len_max : password.val.length ≤ 50)
    (hpre_bytes : ∀ b, b ∈ password.val → IsAllowed b)
    (hpre_short : password.val.length < 6) :
    ∃ r : I64, Aegis.StrongPasswordChecker.strong_password_checker password = ok r ∧
      r.val = max (6 - (password.val.length : ℤ)) (MissingCount password.val : ℤ) := by
  sorry

theorem spec_12_neg :
    ¬ (∀ (password : Slice Std.U8)
    (hpre_len : 1 ≤ password.val.length) (hpre_len_max : password.val.length ≤ 50)
    (hpre_bytes : ∀ b, b ∈ password.val → IsAllowed b)
    (hpre_short : password.val.length < 6), ∃ r : I64, Aegis.StrongPasswordChecker.strong_password_checker password = ok r ∧
      r.val = max (6 - (password.val.length : ℤ)) (MissingCount password.val : ℤ)) := by
  sorry

/-- Let m be the number of categories among {lowercase letter, uppercase letter, digit} that do not occur in password. The function returns a result r with r = m.
  Preconditions: password is a byte slice with 1 <= len(password) <= 50, every byte is one of: an ASCII lowercase letter ('a'..'z'), an ASCII uppercase letter ('A'..'Z'), an ASCII digit ('0'..'9'), the byte '.' (46), or the byte '!' (33); 6 <= len(password) <= 20; and password has no index i with 0 <= i <= len(password)-3 such that password[i]=password[i+1]=password[i+2]. -/
theorem spec_13 (password : Slice Std.U8)
    (hpre_len : 1 ≤ password.val.length) (hpre_len_max : password.val.length ≤ 50)
    (hpre_bytes : ∀ b, b ∈ password.val → IsAllowed b)
    (hpre_min : 6 ≤ password.val.length) (hpre_max : password.val.length ≤ 20)
    (hpre_runs : NoThreeConsecutive password.val) :
    ∃ r : I64, Aegis.StrongPasswordChecker.strong_password_checker password = ok r ∧
      r.val = (MissingCount password.val : ℤ) := by
  sorry

theorem spec_13_neg :
    ¬ (∀ (password : Slice Std.U8)
    (hpre_len : 1 ≤ password.val.length) (hpre_len_max : password.val.length ≤ 50)
    (hpre_bytes : ∀ b, b ∈ password.val → IsAllowed b)
    (hpre_min : 6 ≤ password.val.length) (hpre_max : password.val.length ≤ 20)
    (hpre_runs : NoThreeConsecutive password.val), ∃ r : I64, Aegis.StrongPasswordChecker.strong_password_checker password = ok r ∧
      r.val = (MissingCount password.val : ℤ)) := by
  sorry

/-- The function returns a result r with r = len(password) - 20.
  Preconditions: password is a byte slice with 1 <= len(password) <= 50, every byte is one of: an ASCII lowercase letter ('a'..'z'), an ASCII uppercase letter ('A'..'Z'), an ASCII digit ('0'..'9'), the byte '.' (46), or the byte '!' (33); len(password) > 20; password contains at least one lowercase letter, at least one uppercase letter, and at least one digit; and password has no index i with 0 <= i <= len(password)-3 such that password[i]=password[i+1]=password[i+2]. -/
theorem spec_14 (password : Slice Std.U8)
    (hpre_len : 1 ≤ password.val.length) (hpre_len_max : password.val.length ≤ 50)
    (hpre_bytes : ∀ b, b ∈ password.val → IsAllowed b)
    (hpre_long : 20 < password.val.length)
    (hpre_lower : ContainsLower password.val)
    (hpre_upper : ContainsUpper password.val)
    (hpre_digit : ContainsDigit password.val)
    (hpre_runs : NoThreeConsecutive password.val) :
    ∃ r : I64, Aegis.StrongPasswordChecker.strong_password_checker password = ok r ∧
      r.val = (password.val.length : ℤ) - 20 := by
  sorry

theorem spec_14_neg :
    ¬ (∀ (password : Slice Std.U8)
    (hpre_len : 1 ≤ password.val.length) (hpre_len_max : password.val.length ≤ 50)
    (hpre_bytes : ∀ b, b ∈ password.val → IsAllowed b)
    (hpre_long : 20 < password.val.length)
    (hpre_lower : ContainsLower password.val)
    (hpre_upper : ContainsUpper password.val)
    (hpre_digit : ContainsDigit password.val)
    (hpre_runs : NoThreeConsecutive password.val), ∃ r : I64, Aegis.StrongPasswordChecker.strong_password_checker password = ok r ∧
      r.val = (password.val.length : ℤ) - 20) := by
  sorry

end AegisSpec.StrongPasswordChecker
