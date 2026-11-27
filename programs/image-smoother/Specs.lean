import Aegis.ImageSmoother.Code.Funs

/-!
# Specifications of `Aegis.ImageSmoother.image_smoother`

LeetCode problem `image-smoother`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result
  open Aegis.ImageSmoother

  namespace AegisSpec.ImageSmoother

  def nrows (img : Slice (alloc.vec.Vec I64)) : Nat := img.val.length

  def ncols (img : Slice (alloc.vec.Vec I64)) : Nat := ((img.val[0]!).val).length

  def imgRow (img : Slice (alloc.vec.Vec I64)) (i : Nat) : List I64 := (img.val[i]!).val

  def outRow (r : alloc.vec.Vec (alloc.vec.Vec I64)) (i : Nat) : List I64 :=
    (r.val[i]!).val

  def imgEntry (img : Slice (alloc.vec.Vec I64)) (i j : Nat) : ℤ := ((imgRow img i)[j]!).val

  def outEntry (r : alloc.vec.Vec (alloc.vec.Vec I64)) (i j : Nat) : ℤ :=
    ((outRow r i)[j]!).val

  def nbhdList (m n i j : Nat) : List (Nat × Nat) :=
    ((List.range m).product (List.range n)).filter
      (fun pq => decide (|(pq.1 : ℤ) - (i : ℤ)| ≤ 1 ∧ |(pq.2 : ℤ) - (j : ℤ)| ≤ 1))

  def nbhd (m n i j : Nat) : Finset (Nat × Nat) :=
    (nbhdList m n i j).toFinset

  def nbhdCard (m n i j : Nat) : Nat := (nbhd m n i j).card

  def nbhdSum (img : Slice (alloc.vec.Vec I64)) (m n i j : Nat) : ℤ :=
    (nbhd m n i j).sum (fun pq => imgEntry img pq.1 pq.2)

  def nbhdVals (img : Slice (alloc.vec.Vec I64)) (m n i j : Nat) : List ℤ :=
    (nbhdList m n i j).map (fun pq => imgEntry img pq.1 pq.2)

  def nbhdMin (img : Slice (alloc.vec.Vec I64)) (m n i j : Nat) : ℤ :=
    match nbhdVals img m n i j with
    | [] => 0
    | x :: xs => xs.foldl min x

  def nbhdMax (img : Slice (alloc.vec.Vec I64)) (m n i j : Nat) : ℤ :=
    match nbhdVals img m n i j with
    | [] => 0
    | x :: xs => xs.foldl max x

  def IsMatrix (img : Slice (alloc.vec.Vec I64)) (m n : Nat) : Prop :=
    img.val.length = m ∧ ∀ i, i < m → (imgRow img i).length = n

  def IsImage (img : Slice (alloc.vec.Vec I64)) (m n : Nat) : Prop :=
    IsMatrix img m n ∧ ∀ i j, i < m → j < n → 0 ≤ imgEntry img i j ∧ imgEntry img i j ≤ 255

  /-- Whenever image_smoother(img) returns a result r, the following holds. len(r) = m; for every i with 0 <= i < m, len(r[i]) = n; and for every i,j with 0 <= i < m and 0 <= j < n, let N(i,j) = { (p,q) | 0 <= p < m, 0 <= q < n, |p-i| <= 1, |q-j| <= 1 }, let c = |N(i,j)| (the number of cells in N(i,j)), and let S = sum_{(p,q) in N(i,j)} img[p][q]. Then r[i][j] = floor(S / c), where S and c are nonnegative integers and floor is mathematical floor (equivalently, integer division of S by c).
    Preconditions: Let m = len(img). Assume 1 <= m <= 200. Let n = len(img[0]) (well-defined since m >= 1). Assume 1 <= n <= 200, for every i with 0 <= i < m we have len(img[i]) = n, and for every i,j with 0 <= i < m and 0 <= j < n we have 0 <= img[i][j] <= 255. -/
  theorem spec_1 (img : Slice (alloc.vec.Vec I64)) (m n : Nat)
      (hm : 1 ≤ m) (hm200 : m ≤ 200) (hn : 1 ≤ n) (hn200 : n ≤ 200)
      (himg : IsImage img m n) :
      ∀ r, image_smoother img = ok r →
        r.val.length = m ∧
        (∀ i, i < m → (outRow r i).length = n) ∧
        (∀ i j, i < m → j < n →
          outEntry r i j = nbhdSum img m n i j / (nbhdCard m n i j : ℤ)) := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (img : Slice (alloc.vec.Vec I64)) (m n : Nat)
        (hm : 1 ≤ m) (hm200 : m ≤ 200) (hn : 1 ≤ n) (hn200 : n ≤ 200)
        (himg : IsImage img m n), ∀ r, image_smoother img = ok r →
          r.val.length = m ∧
          (∀ i, i < m → (outRow r i).length = n) ∧
          (∀ i j, i < m → j < n →
            outEntry r i j = nbhdSum img m n i j / (nbhdCard m n i j : ℤ))) := by
    sorry

  /-- For every img satisfying the preconditions, image_smoother(img) returns a result r. In particular, it does not fail from arithmetic overflow, index out of bounds, or panic on these inputs.
    Preconditions: Let m = len(img). Assume 1 <= m <= 200. Let n = len(img[0]) (well-defined since m >= 1). Assume 1 <= n <= 200, for every i with 0 <= i < m we have len(img[i]) = n, and for every i,j with 0 <= i < m and 0 <= j < n we have 0 <= img[i][j] <= 255. -/
  theorem spec_2 (img : Slice (alloc.vec.Vec I64)) (m n : Nat)
      (hm : 1 ≤ m) (hm200 : m ≤ 200) (hn : 1 ≤ n) (hn200 : n ≤ 200)
      (himg : IsImage img m n) :
      ∃ r, image_smoother img = ok r := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (img : Slice (alloc.vec.Vec I64)) (m n : Nat)
        (hm : 1 ≤ m) (hm200 : m ≤ 200) (hn : 1 ≤ n) (hn200 : n ≤ 200)
        (himg : IsImage img m n), ∃ r, image_smoother img = ok r) := by
    sorry

  /-- Whenever image_smoother(img) returns a result r, len(r) = len(img) and for every i with 0 <= i < len(img), len(r[i]) = len(img[i]).
    Preconditions: Let m = len(img). Assume 1 <= m <= 200. Let n = len(img[0]) (well-defined since m >= 1). Assume 1 <= n <= 200, for every i with 0 <= i < m we have len(img[i]) = n, and for every i,j with 0 <= i < m and 0 <= j < n we have 0 <= img[i][j] <= 255. -/
  theorem spec_3 (img : Slice (alloc.vec.Vec I64)) (m n : Nat)
      (hm : 1 ≤ m) (hm200 : m ≤ 200) (hn : 1 ≤ n) (hn200 : n ≤ 200)
      (himg : IsImage img m n) :
      ∀ r, image_smoother img = ok r →
        r.val.length = img.val.length ∧
        ∀ i, i < img.val.length → (outRow r i).length = (imgRow img i).length := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (img : Slice (alloc.vec.Vec I64)) (m n : Nat)
        (hm : 1 ≤ m) (hm200 : m ≤ 200) (hn : 1 ≤ n) (hn200 : n ≤ 200)
        (himg : IsImage img m n), ∀ r, image_smoother img = ok r →
          r.val.length = img.val.length ∧
          ∀ i, i < img.val.length → (outRow r i).length = (imgRow img i).length) := by
    sorry

  /-- Whenever image_smoother(img) returns a result r, for every i,j with 0 <= i < m and 0 <= j < n we have 0 <= r[i][j] <= 255.
    Preconditions: Let m = len(img). Assume 1 <= m <= 200. Let n = len(img[0]) (well-defined since m >= 1). Assume 1 <= n <= 200, for every i with 0 <= i < m we have len(img[i]) = n, and for every i,j with 0 <= i < m and 0 <= j < n we have 0 <= img[i][j] <= 255. -/
  theorem spec_4 (img : Slice (alloc.vec.Vec I64)) (m n : Nat)
      (hm : 1 ≤ m) (hm200 : m ≤ 200) (hn : 1 ≤ n) (hn200 : n ≤ 200)
      (himg : IsImage img m n) :
      ∀ r, image_smoother img = ok r →
        ∀ i j, i < m → j < n → 0 ≤ outEntry r i j ∧ outEntry r i j ≤ 255 := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (img : Slice (alloc.vec.Vec I64)) (m n : Nat)
        (hm : 1 ≤ m) (hm200 : m ≤ 200) (hn : 1 ≤ n) (hn200 : n ≤ 200)
        (himg : IsImage img m n), ∀ r, image_smoother img = ok r →
          ∀ i j, i < m → j < n → 0 ≤ outEntry r i j ∧ outEntry r i j ≤ 255) := by
    sorry

  /-- Whenever image_smoother(img) returns a result r, for every i,j with 0 <= i < m and 0 <= j < n, let N(i,j) = { (p,q) | 0 <= p < m, 0 <= q < n, |p-i| <= 1, |q-j| <= 1 }, let lo = min { img[p][q] | (p,q) in N(i,j) }, and let hi = max { img[p][q] | (p,q) in N(i,j) }. Then lo <= r[i][j] <= hi.
    Preconditions: Let m = len(img). Assume 1 <= m <= 200. Let n = len(img[0]) (well-defined since m >= 1). Assume 1 <= n <= 200, for every i with 0 <= i < m we have len(img[i]) = n, and for every i,j with 0 <= i < m and 0 <= j < n we have 0 <= img[i][j] <= 255. -/
  theorem spec_5 (img : Slice (alloc.vec.Vec I64)) (m n : Nat)
      (hm : 1 ≤ m) (hm200 : m ≤ 200) (hn : 1 ≤ n) (hn200 : n ≤ 200)
      (himg : IsImage img m n) :
      ∀ r, image_smoother img = ok r →
        ∀ i j, i < m → j < n →
          nbhdMin img m n i j ≤ outEntry r i j ∧ outEntry r i j ≤ nbhdMax img m n i j := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (img : Slice (alloc.vec.Vec I64)) (m n : Nat)
        (hm : 1 ≤ m) (hm200 : m ≤ 200) (hn : 1 ≤ n) (hn200 : n ≤ 200)
        (himg : IsImage img m n), ∀ r, image_smoother img = ok r →
          ∀ i j, i < m → j < n →
            nbhdMin img m n i j ≤ outEntry r i j ∧ outEntry r i j ≤ nbhdMax img m n i j) := by
    sorry

  /-- Whenever image_smoother(img) returns a result r, if there exists an integer v such that for every i,j with 0 <= i < m and 0 <= j < n we have img[i][j] = v, then for every i,j with 0 <= i < m and 0 <= j < n we have r[i][j] = v.
    Preconditions: Let m = len(img). Assume 1 <= m <= 200. Let n = len(img[0]) (well-defined since m >= 1). Assume 1 <= n <= 200, for every i with 0 <= i < m we have len(img[i]) = n, and for every i,j with 0 <= i < m and 0 <= j < n we have 0 <= img[i][j] <= 255. -/
  theorem spec_6 (img : Slice (alloc.vec.Vec I64)) (m n : Nat)
      (hm : 1 ≤ m) (hm200 : m ≤ 200) (hn : 1 ≤ n) (hn200 : n ≤ 200)
      (himg : IsImage img m n) :
      ∀ v : ℤ, (∀ i j, i < m → j < n → imgEntry img i j = v) →
        ∀ r, image_smoother img = ok r →
          ∀ i j, i < m → j < n → outEntry r i j = v := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (img : Slice (alloc.vec.Vec I64)) (m n : Nat)
        (hm : 1 ≤ m) (hm200 : m ≤ 200) (hn : 1 ≤ n) (hn200 : n ≤ 200)
        (himg : IsImage img m n), ∀ v : ℤ, (∀ i j, i < m → j < n → imgEntry img i j = v) →
          ∀ r, image_smoother img = ok r →
            ∀ i j, i < m → j < n → outEntry r i j = v) := by
    sorry

  /-- Let d be any integer such that for every i,j with 0 <= i < m and 0 <= j < n we have 0 <= img[i][j] + d <= 255, and let img2 be the m x n matrix defined by img2[i][j] = img[i][j] + d. Whenever image_smoother(img) returns r and image_smoother(img2) returns r2, for every i,j with 0 <= i < m and 0 <= j < n we have r2[i][j] = r[i][j] + d.
    Preconditions: Let m = len(img). Assume 1 <= m <= 200. Let n = len(img[0]) (well-defined since m >= 1). Assume 1 <= n <= 200, every row of img has length n, and every entry of img is in 0..255. -/
  theorem spec_7 (img img2 : Slice (alloc.vec.Vec I64)) (m n : Nat) (d : ℤ)
      (hm : 1 ≤ m) (hm200 : m ≤ 200) (hn : 1 ≤ n) (hn200 : n ≤ 200)
      (himg : IsImage img m n)
      (himg2 : IsMatrix img2 m n)
      (hshift : ∀ i j, i < m → j < n → 0 ≤ imgEntry img i j + d ∧ imgEntry img i j + d ≤ 255)
      (hdef : ∀ i j, i < m → j < n → imgEntry img2 i j = imgEntry img i j + d) :
      ∀ r r2, image_smoother img = ok r → image_smoother img2 = ok r2 →
        ∀ i j, i < m → j < n → outEntry r2 i j = outEntry r i j + d := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (img img2 : Slice (alloc.vec.Vec I64)) (m n : Nat) (d : ℤ)
        (hm : 1 ≤ m) (hm200 : m ≤ 200) (hn : 1 ≤ n) (hn200 : n ≤ 200)
        (himg : IsImage img m n)
        (himg2 : IsMatrix img2 m n)
        (hshift : ∀ i j, i < m → j < n → 0 ≤ imgEntry img i j + d ∧ imgEntry img i j + d ≤ 255)
        (hdef : ∀ i j, i < m → j < n → imgEntry img2 i j = imgEntry img i j + d), ∀ r r2, image_smoother img = ok r → image_smoother img2 = ok r2 →
          ∀ i j, i < m → j < n → outEntry r2 i j = outEntry r i j + d) := by
    sorry

  /-- If for every i,j with 0 <= i < m and 0 <= j < n we have img[i][j] <= img2[i][j], then whenever image_smoother(img) returns r and image_smoother(img2) returns r2, for every i,j with 0 <= i < m and 0 <= j < n we have r[i][j] <= r2[i][j].
    Preconditions: Let img and img2 be two inputs. Let m = len(img) and n = len(img[0]) with 1 <= m <= 200 and 1 <= n <= 200. Assume every row of img and of img2 has length n, len(img2) = m, and every entry of both img and img2 is in 0..255. -/
  theorem spec_8 (img img2 : Slice (alloc.vec.Vec I64)) (m n : Nat)
      (hm : 1 ≤ m) (hm200 : m ≤ 200) (hn : 1 ≤ n) (hn200 : n ≤ 200)
      (himg : IsImage img m n) (himg2 : IsImage img2 m n)
      (hle : ∀ i j, i < m → j < n → imgEntry img i j ≤ imgEntry img2 i j) :
      ∀ r r2, image_smoother img = ok r → image_smoother img2 = ok r2 →
        ∀ i j, i < m → j < n → outEntry r i j ≤ outEntry r2 i j := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (img img2 : Slice (alloc.vec.Vec I64)) (m n : Nat)
        (hm : 1 ≤ m) (hm200 : m ≤ 200) (hn : 1 ≤ n) (hn200 : n ≤ 200)
        (himg : IsImage img m n) (himg2 : IsImage img2 m n)
        (hle : ∀ i j, i < m → j < n → imgEntry img i j ≤ imgEntry img2 i j), ∀ r r2, image_smoother img = ok r → image_smoother img2 = ok r2 →
          ∀ i j, i < m → j < n → outEntry r i j ≤ outEntry r2 i j) := by
    sorry

  /-- Whenever image_smoother(img) returns a result r, for every i,j with 0 <= i < m and 0 <= j < m we have r[i][j] = r[j][i].
    Preconditions: Let m = len(img). Assume 1 <= m <= 200. Let n = len(img[0]) (well-defined since m >= 1). Assume 1 <= n <= 200, every row has length n, every entry is in 0..255, and additionally m = n and for every i,j with 0 <= i < m and 0 <= j < m we have img[i][j] = img[j][i]. -/
  theorem spec_9 (img : Slice (alloc.vec.Vec I64)) (m n : Nat)
      (hm : 1 ≤ m) (hm200 : m ≤ 200) (hn : 1 ≤ n) (hn200 : n ≤ 200)
      (himg : IsImage img m n)
      (hmn : m = n)
      (hsymm : ∀ i j, i < m → j < m → imgEntry img i j = imgEntry img j i) :
      ∀ r, image_smoother img = ok r →
        ∀ i j, i < m → j < m → outEntry r i j = outEntry r j i := by
    sorry

  theorem spec_9_neg :
      ¬ (∀ (img : Slice (alloc.vec.Vec I64)) (m n : Nat)
        (hm : 1 ≤ m) (hm200 : m ≤ 200) (hn : 1 ≤ n) (hn200 : n ≤ 200)
        (himg : IsImage img m n)
        (hmn : m = n)
        (hsymm : ∀ i j, i < m → j < m → imgEntry img i j = imgEntry img j i), ∀ r, image_smoother img = ok r →
          ∀ i j, i < m → j < m → outEntry r i j = outEntry r j i) := by
    sorry

  /-- Whenever image_smoother(img) returns a result r, for every i,j with 0 <= i < m and 0 <= j < n, let N(i,j) = { (p,q) | 0 <= p < m, 0 <= q < n, |p-i| <= 1, |q-j| <= 1 }, let c = |N(i,j)|, and let S = sum_{(p,q) in N(i,j)} img[p][q]. Then r[i][j] is the unique integer q such that q*c <= S < (q+1)*c.
    Preconditions: Let m = len(img). Assume 1 <= m <= 200. Let n = len(img[0]) (well-defined since m >= 1). Assume 1 <= n <= 200, every row has length n, and every entry is in 0..255. -/
  theorem spec_10 (img : Slice (alloc.vec.Vec I64)) (m n : Nat)
      (hm : 1 ≤ m) (hm200 : m ≤ 200) (hn : 1 ≤ n) (hn200 : n ≤ 200)
      (himg : IsImage img m n) :
      ∀ r, image_smoother img = ok r →
        ∀ i j, i < m → j < n →
          outEntry r i j * (nbhdCard m n i j : ℤ) ≤ nbhdSum img m n i j ∧
          nbhdSum img m n i j < (outEntry r i j + 1) * (nbhdCard m n i j : ℤ) ∧
          ∀ q : ℤ, q * (nbhdCard m n i j : ℤ) ≤ nbhdSum img m n i j →
            nbhdSum img m n i j < (q + 1) * (nbhdCard m n i j : ℤ) →
            q = outEntry r i j := by
    sorry

  theorem spec_10_neg :
      ¬ (∀ (img : Slice (alloc.vec.Vec I64)) (m n : Nat)
        (hm : 1 ≤ m) (hm200 : m ≤ 200) (hn : 1 ≤ n) (hn200 : n ≤ 200)
        (himg : IsImage img m n), ∀ r, image_smoother img = ok r →
          ∀ i j, i < m → j < n →
            outEntry r i j * (nbhdCard m n i j : ℤ) ≤ nbhdSum img m n i j ∧
            nbhdSum img m n i j < (outEntry r i j + 1) * (nbhdCard m n i j : ℤ) ∧
            ∀ q : ℤ, q * (nbhdCard m n i j : ℤ) ≤ nbhdSum img m n i j →
              nbhdSum img m n i j < (q + 1) * (nbhdCard m n i j : ℤ) →
              q = outEntry r i j) := by
    sorry

  end AegisSpec.ImageSmoother
