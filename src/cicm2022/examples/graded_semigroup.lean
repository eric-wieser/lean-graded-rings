import algebra.group.basic

variables {ι : Type*} {A : ι → Type*}

-- uncomment this to get an error
/-
class «fails».g_semigroup [add_semigroup ι] :=
(mul {i j} : A i → A j → A (i + j))
(mul_assoc {i j k} (x : A i) (y : A j) (z : A k) :
  mul (mul x y) z = mul x (mul y z))
-/

class «sigma».g_semigroup [add_semigroup ι] :=
(mul {i j} : A i → A j → A (i + j))
(mul_assoc {i j k} (x : A i) (y : A j) (z : A k) :
  mul (mul x y) z == mul x (mul y z))

class «extends».g_semigroup [add_semigroup ι] extends semigroup (Σ i, A i) :=
(fst_mul {i j} (x : A i) (y : A j) :
  (⟨_, x⟩ * ⟨_, y⟩ : Σ i, A i).fst = i + j)

class «eq.rec».g_semigroup [add_semigroup ι] :=
(mul {i j} : A i → A j → A (i + j))
(mul_assoc {i j k : ι} (x : A i) (y : A j) (z : A k) :
  (add_assoc i j k).rec (mul (mul x y) z) = mul x (mul y z))

class «cast».g_semigroup [add_semigroup ι] :=
(cast {i j} (h : i = j) : A i → A j)
(cast_eq_eq_rec {i j} (h : i = j) (x : A i) : cast h x = h.rec x)
(mul {i j} : A i → A j → A (i + j))
(mul_assoc {i j k : ι} (x : A i) (y : A j) (z : A k) :
  cast (add_assoc i j k) (mul (mul x y) z) = mul x (mul y z))

class «h : i+j=k».g_semigroup [add_semigroup ι] :=
(mul {i j k} (h : i + j = k) : A i → A j → A k)
(mul_assoc {i j k ij jk ijk : ι}
  (hij : i + j = ij) (hjk : j + k = jk)
  (hi_jk : i + jk = ijk) (hij_k : ij + k = ijk)
  (x : A i) (y : A j) (z : A k) :
    (mul hij_k (mul hij x y) z) = mul hi_jk x (mul hjk y z))
