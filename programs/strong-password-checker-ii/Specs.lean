import Aegis.StrongPasswordCheckerIi.Code.Funs

/-!
# Specifications of `Aegis.StrongPasswordCheckerIi.strong_password_checker_ii`

LeetCode problem `strong-password-checker-ii`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result
  open Aegis.StrongPasswordCheckerIi

  namespace AegisSpec.StrongPasswordCheckerIi

  def IsLowerByte (b : Std.U8) : Prop := 97 ≤ b.val ∧ b.val ≤ 122

  def IsUpperByte (b : Std.U8) : Prop := 65 ≤ b.val ∧ b.val ≤ 90

  def IsDigitByte (b : Std.U8) : Prop := 48 ≤ b.val ∧ b.val ≤ 57

  def IsSpecialByte (b : Std.U8) : Prop :=
    b.val = 33 ∨ b.val = 64 ∨ b.val = 35 ∨ b.val = 36 ∨ b.val = 37 ∨ b.val = 94 ∨
      b.val = 38 ∨ b.val = 42 ∨ b.val = 40 ∨ b.val = 41 ∨ b.val = 45 ∨ b.val = 43

  def IsAllowedByte (b : Std.U8) : Prop :=
    IsUpperByte b ∨ IsLowerByte b ∨ IsDigitByte b ∨ IsSpecialByte b

  def SameCategory (a b : Std.U8) : Prop :=
    (IsUpperByte a ∧ IsUpperByte b) ∨ (IsLowerByte a ∧ IsLowerByte b) ∨
      (IsDigitByte a ∧ IsDigitByte b) ∨ (IsSpecialByte a ∧ IsSpecialByte b)

  def Occurs (password : Slice Std.U8) (P : Std.U8 → Prop) : Prop :=
    ∃ (i : Nat) (h : i < password.val.length), P (password.val[i]'h)

  def AllBytes (password : Slice Std.U8) (P : Std.U8 → Prop) : Prop :=
    ∀ (i : Nat) (h : i < password.val.length), P (password.val[i]'h)

  def IsValidInput (password : Slice Std.U8) : Prop :=
    1 ≤ password.val.length ∧ password.val.length ≤ 100 ∧ AllBytes password IsAllowedByte

  def NoAdjacentEqual (password : Slice Std.U8) : Prop :=
    ∀ (i : Nat) (h : i < password.val.length - 1),
      (password.val[i]'(by omega)).val ≠ (password.val[i+1]'(by omega)).val

  def AdjacentRepeat (password : Slice Std.U8) : Prop :=
    ∃ (i : Nat) (h : i < password.val.length - 1),
      (password.val[i]'(by omega)).val = (password.val[i+1]'(by omega)).val

  def MeetsAllConditions (password : Slice Std.U8) : Prop :=
    8 ≤ password.val.length ∧ Occurs password IsLowerByte ∧ Occurs password IsUpperByte ∧
      Occurs password IsDigitByte ∧ Occurs password IsSpecialByte ∧
        NoAdjacentEqual password

  /-- The function returns a result r : Bool (it does not fail) and r = true if and only if all of the following hold: (1) len(password) >= 8; (2) there exists an index i with 0 <= i < len(password) and 97 <= password[i] <= 122; (3) there exists an index i with 0 <= i < len(password) and 65 <= password[i] <= 90; (4) there exists an index i with 0 <= i < len(password) and 48 <= password[i] <= 57; (5) there exists an index i with 0 <= i < len(password) such that password[i] is one of the special bytes '!', '@', '#', '$', '%', '^', '&', '*', '(', ')', '-', '+'; (6) for every index i with 0 <= i < len(password)-1, password[i] != password[i+1].
    Preconditions: password is a Slice U8 with 1 <= len(password) <= 100, and every byte password[i], for 0 <= i < len(password), is an ASCII uppercase letter (65 <= password[i] <= 90), an ASCII lowercase letter (97 <= password[i] <= 122), an ASCII digit (48 <= password[i] <= 57), or one of the special bytes '!', '@', '#', '$', '%', '^', '&', '*', '(', ')', '-', '+'. -/
  theorem spec_1 (password : Slice Std.U8) (hpre : IsValidInput password) :
      ∃ r : Bool,
        strong_password_checker_ii password = ok r ∧
          (r = true ↔ 8 ≤ password.val.length ∧ Occurs password IsLowerByte ∧
            Occurs password IsUpperByte ∧ Occurs password IsDigitByte ∧
              Occurs password IsSpecialByte ∧ NoAdjacentEqual password) := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (password : Slice Std.U8) (hpre : IsValidInput password), ∃ r : Bool,
          strong_password_checker_ii password = ok r ∧
            (r = true ↔ 8 ≤ password.val.length ∧ Occurs password IsLowerByte ∧
              Occurs password IsUpperByte ∧ Occurs password IsDigitByte ∧
                Occurs password IsSpecialByte ∧ NoAdjacentEqual password)) := by
    sorry

  /-- The function returns a result r : Bool; equivalently, the computation does not fail on any input satisfying the preconditions.
    Preconditions: password is a Slice U8 with 1 <= len(password) <= 100, and every byte password[i], for 0 <= i < len(password), is an ASCII uppercase letter (65 <= password[i] <= 90), an ASCII lowercase letter (97 <= password[i] <= 122), an ASCII digit (48 <= password[i] <= 57), or one of the special bytes '!', '@', '#', '$', '%', '^', '&', '*', '(', ')', '-', '+'. -/
  theorem spec_2 (password : Slice Std.U8) (hpre : IsValidInput password) :
      ∃ r : Bool, strong_password_checker_ii password = ok r := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (password : Slice Std.U8) (hpre : IsValidInput password), ∃ r : Bool, strong_password_checker_ii password = ok r) := by
    sorry

  /-- Whenever the function returns a result r : Bool, if r = true then all six conditions hold: len(password) >= 8; there exists a lowercase ASCII letter; there exists an uppercase ASCII letter; there exists an ASCII digit; there exists a special byte from '!', '@', '#', '$', '%', '^', '&', '*', '(', ')', '-', '+'; and for every i with 0 <= i < len(password)-1, password[i] != password[i+1].
    Preconditions: password is a Slice U8 satisfying the problem constraints. -/
  theorem spec_3 (password : Slice Std.U8) (hpre : IsValidInput password) :
      ∀ r : Bool,
        strong_password_checker_ii password = ok r → r = true →
          8 ≤ password.val.length ∧ Occurs password IsLowerByte ∧
            Occurs password IsUpperByte ∧ Occurs password IsDigitByte ∧
              Occurs password IsSpecialByte ∧ NoAdjacentEqual password := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (password : Slice Std.U8) (hpre : IsValidInput password), ∀ r : Bool,
          strong_password_checker_ii password = ok r → r = true →
            8 ≤ password.val.length ∧ Occurs password IsLowerByte ∧
              Occurs password IsUpperByte ∧ Occurs password IsDigitByte ∧
                Occurs password IsSpecialByte ∧ NoAdjacentEqual password) := by
    sorry

  /-- The function returns a result r : Bool with r = true.
    Preconditions: password is a Slice U8 satisfying the problem constraints, len(password) >= 8, password contains at least one lowercase ASCII letter, at least one uppercase ASCII letter, at least one ASCII digit, at least one special byte from '!', '@', '#', '$', '%', '^', '&', '*', '(', ')', '-', '+', and for every i with 0 <= i < len(password)-1, password[i] != password[i+1]. -/
  theorem spec_4 (password : Slice Std.U8) (hpre : IsValidInput password)
      (hlen : 8 ≤ password.val.length) (hlower : Occurs password IsLowerByte)
      (hupper : Occurs password IsUpperByte) (hdigit : Occurs password IsDigitByte)
      (hspecial : Occurs password IsSpecialByte) (hadjacent : NoAdjacentEqual password) :
      ∃ r : Bool, strong_password_checker_ii password = ok r ∧ r = true := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (password : Slice Std.U8) (hpre : IsValidInput password)
        (hlen : 8 ≤ password.val.length) (hlower : Occurs password IsLowerByte)
        (hupper : Occurs password IsUpperByte) (hdigit : Occurs password IsDigitByte)
        (hspecial : Occurs password IsSpecialByte) (hadjacent : NoAdjacentEqual password), ∃ r : Bool, strong_password_checker_ii password = ok r ∧ r = true) := by
    sorry

  /-- Whenever strong_password_checker_ii(password) returns a result r1 : Bool and strong_password_checker_ii(other) returns a result r2 : Bool, we have r1 = r2.
    Preconditions: password and other are two Slice U8 values satisfying the problem constraints, len(password) = len(other), for every i with 0 <= i < len(password) the bytes password[i] and other[i] lie in the same one of the four categories (uppercase ASCII letter, lowercase ASCII letter, ASCII digit, special byte), and for every i with 0 <= i < len(password)-1, password[i] = password[i+1] if and only if other[i] = other[i+1]. -/
  theorem spec_5 (password other : Slice Std.U8)
      (hpre : IsValidInput password ∧ IsValidInput other)
      (hlen : password.val.length = other.val.length)
      (hcategory : ∀ (i : Nat) (h : i < password.val.length),
        SameCategory (password.val[i]'h) (other.val[i]'(by omega)))
      (hadjacent : ∀ (i : Nat) (h : i < password.val.length - 1),
        ((password.val[i]'(by omega)).val = (password.val[i+1]'(by omega)).val ↔
          (other.val[i]'(by omega)).val = (other.val[i+1]'(by omega)).val)) :
      ∀ (r1 r2 : Bool),
        strong_password_checker_ii password = ok r1 → strong_password_checker_ii other = ok r2 →
          r1 = r2 := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (password other : Slice Std.U8)
        (hpre : IsValidInput password ∧ IsValidInput other)
        (hlen : password.val.length = other.val.length)
        (hcategory : ∀ (i : Nat) (h : i < password.val.length),
          SameCategory (password.val[i]'h) (other.val[i]'(by omega)))
        (hadjacent : ∀ (i : Nat) (h : i < password.val.length - 1),
          ((password.val[i]'(by omega)).val = (password.val[i+1]'(by omega)).val ↔
            (other.val[i]'(by omega)).val = (other.val[i+1]'(by omega)).val)), ∀ (r1 r2 : Bool),
          strong_password_checker_ii password = ok r1 → strong_password_checker_ii other = ok r2 →
            r1 = r2) := by
    sorry

  /-- Whenever the function returns a result r : Bool with r = true, there exist indices iL, iU, iD, iS such that 0 <= iL, iU, iD, iS < len(password), password[iL] is a lowercase ASCII letter, password[iU] is an uppercase ASCII letter, password[iD] is an ASCII digit, password[iS] is a special byte from '!', '@', '#', '$', '%', '^', '&', '*', '(', ')', '-', '+', and for every j with 0 <= j < len(password)-1, password[j] != password[j+1].
    Preconditions: password is a Slice U8 satisfying the problem constraints. -/
  theorem spec_6 (password : Slice Std.U8) (hpre : IsValidInput password) :
      ∀ r : Bool,
        strong_password_checker_ii password = ok r → r = true →
          ∃ (iL iU iD iS : Nat) (hL : iL < password.val.length)
            (hU : iU < password.val.length) (hD : iD < password.val.length)
            (hS : iS < password.val.length),
            IsLowerByte (password.val[iL]'hL) ∧ IsUpperByte (password.val[iU]'hU) ∧
              IsDigitByte (password.val[iD]'hD) ∧ IsSpecialByte (password.val[iS]'hS) ∧
                NoAdjacentEqual password := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (password : Slice Std.U8) (hpre : IsValidInput password), ∀ r : Bool,
          strong_password_checker_ii password = ok r → r = true →
            ∃ (iL iU iD iS : Nat) (hL : iL < password.val.length)
              (hU : iU < password.val.length) (hD : iD < password.val.length)
              (hS : iS < password.val.length),
              IsLowerByte (password.val[iL]'hL) ∧ IsUpperByte (password.val[iU]'hU) ∧
                IsDigitByte (password.val[iD]'hD) ∧ IsSpecialByte (password.val[iS]'hS) ∧
                  NoAdjacentEqual password) := by
    sorry

  /-- Whenever the function returns a result r : Bool, if r = false then at least one of the following holds: len(password) < 8; there is no lowercase ASCII letter; there is no uppercase ASCII letter; there is no ASCII digit; there is no special byte from '!', '@', '#', '$', '%', '^', '&', '*', '(', ')', '-', '+'; or there exists i with 0 <= i < len(password)-1 and password[i] = password[i+1].
    Preconditions: password is a Slice U8 satisfying the problem constraints. -/
  theorem spec_7 (password : Slice Std.U8) (hpre : IsValidInput password) :
      ∀ r : Bool,
        strong_password_checker_ii password = ok r → r = false →
          (password.val.length < 8 ∨ ¬ Occurs password IsLowerByte ∨
            ¬ Occurs password IsUpperByte ∨ ¬ Occurs password IsDigitByte ∨
              ¬ Occurs password IsSpecialByte ∨ AdjacentRepeat password) := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (password : Slice Std.U8) (hpre : IsValidInput password), ∀ r : Bool,
          strong_password_checker_ii password = ok r → r = false →
            (password.val.length < 8 ∨ ¬ Occurs password IsLowerByte ∨
              ¬ Occurs password IsUpperByte ∨ ¬ Occurs password IsDigitByte ∨
                ¬ Occurs password IsSpecialByte ∨ AdjacentRepeat password)) := by
    sorry

  end AegisSpec.StrongPasswordCheckerIi
