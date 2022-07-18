import cicm2022.examples.Proj.degree_zero_part
import cicm2022.examples.Proj.structure_sheaf
import cicm2022.examples.Proj.lemmas
import cicm2022.examples.Proj.Proj_iso_Spec.Top_component.from_Spec

import algebraic_geometry.structure_sheaf
import algebraic_geometry.Spec

noncomputable theory

namespace algebraic_geometry

open_locale direct_sum big_operators pointwise big_operators
open direct_sum set_like.graded_monoid localization finset (hiding mk_zero)

variables {R A : Type*}
variables [comm_ring R] [comm_ring A] [algebra R A]

variables (𝒜 : ℕ → submodule R A)
variables [graded_algebra 𝒜]

open Top topological_space
open category_theory opposite
open projective_spectrum.structure_sheaf

local notation `Proj` := Proj.to_LocallyRingedSpace 𝒜
-- `Proj` as a locally ringed space
local notation `Proj.T` := Proj .1.1.1
-- the underlying topological space of `Proj`
local notation `Proj| ` U := Proj .restrict (opens.open_embedding (U : opens Proj.T))
-- `Proj` restrict to some open set
local notation `Proj.T| ` U :=
  (Proj .restrict (opens.open_embedding (U : opens Proj.T))).to_SheafedSpace.to_PresheafedSpace.1
-- the underlying topological space of `Proj` restricted to some open set
local notation `pbo` x := projective_spectrum.basic_open 𝒜 x
-- basic open sets in `Proj`
local notation `sbo` f := prime_spectrum.basic_open f
-- basic open sets in `Spec`
local notation `Spec` ring := Spec.LocallyRingedSpace_obj (CommRing.of ring)
-- `Spec` as a locally ringed space
local notation `Spec.T` ring :=
  (Spec.LocallyRingedSpace_obj (CommRing.of ring)).to_SheafedSpace.to_PresheafedSpace.1
-- the underlying topological space of `Spec`
local notation `A⁰_` f_deg := degree_zero_part f_deg

namespace Proj_iso_Spec_Sheaf_component

namespace from_Spec

open algebraic_geometry

variables {𝒜} {m : ℕ} {f : A} (hm : 0 < m) (f_deg : f ∈ 𝒜 m) (V : (opens (Spec (A⁰_ f_deg)))ᵒᵖ) 
variables (hh : (Spec (A⁰_ f_deg)).presheaf.obj V)
variables (y : ((@opens.open_embedding Proj.T (pbo f)).is_open_map.functor.op.obj 
  ((opens.map (Proj_iso_Spec_Top_component hm f_deg).hom).op.obj V)).unop)

lemma data_prop1 : y.1 ∈ (pbo f) :=
begin
  obtain ⟨⟨a, ha1⟩, -, ha2⟩ := y.2,
  rw ← ha2,
  exact ha1,
end

lemma data_prop2 :
  (Proj_iso_Spec_Top_component hm f_deg).hom ⟨y.1, data_prop1 hm f_deg V y⟩ ∈ unop V :=
begin
  obtain ⟨⟨a, ha1⟩, ha2, ha3⟩ := y.2,
  erw set.mem_preimage at ha2,
  convert ha2,
  rw ← ha3,
  refl,
end

variable {V}
def data : structure_sheaf.localizations (A⁰_ f_deg) 
  ((Proj_iso_Spec_Top_component hm f_deg).hom ⟨y.1, data_prop1 _ _ _ _⟩) :=
hh.1 ⟨_, data_prop2 _ _ _ _⟩

lemma data.one :
  data hm f_deg (1 : (Spec (A⁰_ f_deg)).presheaf.obj V) = 1 := rfl

lemma data.zero :
  data hm f_deg (0 : (Spec (A⁰_ f_deg)).presheaf.obj V) = 0 := rfl

lemma data.add_apply (x y : (Spec (A⁰_ f_deg)).presheaf.obj V) (z):
  data hm f_deg (x + y) z = data hm f_deg x z + data hm f_deg y z := rfl

lemma data.mul_apply (x y : (Spec (A⁰_ f_deg)).presheaf.obj V) (z):
  data hm f_deg (x * y) z = data hm f_deg x z * data hm f_deg y z := rfl

private lemma data.exist_rep 
  (data : structure_sheaf.localizations (A⁰_ f_deg) ((Proj_iso_Spec_Top_component hm f_deg).hom ⟨y.1, data_prop1 _ _ _ _⟩)) :
  ∃ (a : A⁰_ f_deg) (b : ((Proj_iso_Spec_Top_component hm f_deg).hom ⟨y.1, data_prop1 _ _ _ _⟩).as_ideal.prime_compl),
  data = mk a b :=
begin
  induction data using localization.induction_on with d,
  rcases d with ⟨a, b⟩,
  refine ⟨a, b, rfl⟩,
end

def data.num : A⁰_ f_deg :=
classical.some $ data.exist_rep hm f_deg y (data hm f_deg hh y)

def data.denom : A⁰_ f_deg :=
(classical.some $ classical.some_spec $ data.exist_rep hm f_deg y (data hm f_deg hh y)).1

lemma data.denom_not_mem : 
  (data.denom hm f_deg hh y) ∉ ((Proj_iso_Spec_Top_component hm f_deg).hom ⟨y.1, data_prop1 _ _ _ _⟩).as_ideal :=
(classical.some $ classical.some_spec $ data.exist_rep hm f_deg y (data hm f_deg hh y)).2

lemma data.eq_num_div_denom :
  (data hm f_deg hh y) = 
  localization.mk (data.num hm f_deg hh y) ⟨data.denom hm f_deg hh y, data.denom_not_mem hm f_deg hh y⟩ :=
begin 
  rw classical.some_spec (classical.some_spec (data.exist_rep hm f_deg y (data hm f_deg hh y))), 
  congr, 
  rw subtype.ext_iff, 
  refl,
end

def num : A :=
degree_zero_part.num (data.num hm f_deg hh y) * f^(degree_zero_part.deg (data.denom hm f_deg hh y))

lemma num.mem :
  (num hm f_deg hh y) ∈ 
    𝒜 (m * (degree_zero_part.deg (data.num hm f_deg hh y)) 
      + m * (degree_zero_part.deg (data.denom hm f_deg hh y))) :=
mul_mem (degree_zero_part.num_mem _) $ begin
  convert (set_like.graded_monoid.pow_mem (degree_zero_part.deg (data.denom hm f_deg hh y)) f_deg) using 1,
  rw mul_comm,
  refl,
end

def denom : A :=
degree_zero_part.num (data.denom hm f_deg hh y) * f^(degree_zero_part.deg (data.num hm f_deg hh y))

lemma denom.mem :
  (denom hm f_deg hh y) ∈ 
  𝒜 (m * (degree_zero_part.deg (data.num hm f_deg hh y)) 
      + m * (degree_zero_part.deg (data.denom hm f_deg hh y))) :=
begin
  change _ * _ ∈ _,
  rw mul_comm,
  apply set_like.graded_monoid.mul_mem,
  { rw mul_comm,
    exact set_like.graded_monoid.pow_mem (degree_zero_part.deg (data.num hm f_deg hh y)) f_deg, },
  { apply degree_zero_part.num_mem, },
end

lemma denom_not_mem :
  denom hm f_deg hh y ∉ y.1.as_homogeneous_ideal := λ rid,
begin
  rcases y.1.is_prime.mem_or_mem rid with H1 | H2,
  { have mem1 := data.denom_not_mem hm f_deg hh y,
    have eq1 := degree_zero_part.eq (data.denom hm f_deg hh y),
    dsimp only at mem1,
    change _ ∉ _ at mem1,
    apply mem1,
    change
      (data.denom hm f_deg hh y) ∈ ((Proj_iso_Spec_Top_component.to_Spec.carrier f_deg) ⟨y.1, _⟩),
    rw Proj_iso_Spec_Top_component.to_Spec.mem_carrier_iff,
    rw eq1,
    convert ideal.mul_mem_left _ _ _,
    work_on_goal 2
    { exact mk 1 ⟨f^degree_zero_part.deg (data.denom hm f_deg hh y), ⟨_, rfl⟩⟩ },
    work_on_goal 2
    { exact mk (degree_zero_part.num (data.denom hm f_deg hh y)) 1 },
    { rw [mk_mul, one_mul, mul_one], },
    { apply ideal.subset_span,
      exact ⟨_, H1, rfl⟩ }, },
  { replace H2 := y.1.is_prime.mem_of_pow_mem _ H2,
    obtain ⟨⟨a, ha1⟩, ha2, ha3⟩ := y.2,
    erw projective_spectrum.mem_basic_open at ha1,
    apply ha1,
    convert H2, }
end

variable (V)
def bmk : homogeneous_localization 𝒜 y.1.as_homogeneous_ideal.to_ideal := quotient.mk' 
{ deg := m * (degree_zero_part.deg (data.num hm f_deg hh y)) 
      + m * (degree_zero_part.deg (data.denom hm f_deg hh y)),
  num := ⟨num hm f_deg hh y, num.mem hm f_deg hh y⟩,
  denom := ⟨denom hm f_deg hh y, denom.mem hm f_deg hh y⟩,
  denom_not_mem := denom_not_mem hm f_deg hh y }

lemma bmk_one :
  bmk hm f_deg V 1 = 1 :=
begin
  ext1 y,
  have y_mem : y.val ∈ (pbo f).val,
  { erw projective_spectrum.mem_basic_open,
    intro rid,
    have mem1 := y.2,
    erw set.mem_preimage at mem1,
    obtain ⟨⟨a, ha1⟩, ha, ha2⟩ := mem1,
    change a = y.1 at ha2,
    erw set.mem_preimage at ha,
    erw ←ha2 at rid,
    apply ha1,
    exact rid },

  rw pi.one_apply,
  unfold bmk,
  rw [homogeneous_localization.ext_iff_val, homogeneous_localization.val_mk', homogeneous_localization.one_val],
  simp only [← subtype.val_eq_coe],
  unfold num denom,

  have eq1 := data.eq_num_div_denom hm f_deg 1 y,
  rw [data.one, pi.one_apply] at eq1,
  replace eq1 := eq1.symm,
  rw [show (1 : structure_sheaf.localizations (A⁰_ f_deg)
    (((Proj_iso_Spec_Top_component hm f_deg).hom) ⟨y.val, y_mem⟩)) = localization.mk 1 1,
    by erw localization.mk_self 1, localization.mk_eq_mk'] at eq1,
  replace eq1 := (@@is_localization.eq _ _ _ _).mp eq1,
  obtain ⟨⟨⟨C, C_degree_zero⟩, hC⟩, eq1⟩ := eq1,
  induction C using localization.induction_on with 𝔻,
  obtain ⟨C, ⟨_, ⟨l, rfl⟩⟩⟩ := 𝔻,
  simp only [mul_one, one_mul, subtype.coe_mk] at eq1,
  simp only [localization.mk_eq_mk', is_localization.eq],
  change _ ∉ _ at hC,
  erw Proj_iso_Spec_Top_component.to_Spec.mem_carrier_iff at hC,
  rw subtype.coe_mk at hC,
  dsimp only at C_degree_zero hC,

  have eq_num := degree_zero_part.eq (data.num hm f_deg 1 y),
  have eq_denom := degree_zero_part.eq (data.denom hm f_deg 1 y),

  simp only [subtype.val_eq_coe, submonoid.coe_one, mul_one] at eq1,
  rw subtype.ext_iff at eq1,
  simp only [subring.coe_mul] at eq1,
  erw [eq_num, eq_denom, localization.mk_mul, localization.mk_mul] at eq1,
  simp only [localization.mk_eq_mk', is_localization.eq, subtype.coe_mk] at eq1,
  obtain ⟨⟨_, ⟨n1, rfl⟩⟩, eq1⟩ := eq1,
  simp only [submonoid.coe_mul, subtype.coe_mk] at eq1,

  have C_not_mem : C ∉ y.1.as_homogeneous_ideal,
  { intro rid,
    have eq1 : (localization.mk C ⟨f ^ l, ⟨_, rfl⟩⟩ : localization.away f) =
      (localization.mk 1 ⟨f^l, ⟨_, rfl⟩⟩ : localization.away f) * localization.mk C 1,
      rw [localization.mk_mul, one_mul, mul_one],
    erw eq1 at hC,
    apply hC,
    convert ideal.mul_mem_left _ _ _,
    apply ideal.subset_span,
    refine ⟨_, rid, rfl⟩, },

  rw [show (1 : localization.at_prime y.1.as_homogeneous_ideal.to_ideal) = mk (1 : _) 1, by erw mk_self 1, mk_eq_mk', is_localization.eq],
  use C * (f^l * f^n1),
  { intros rid,
    rcases y.1.is_prime.mem_or_mem rid with H1 | H3,
    exact C_not_mem H1,
    rw ←pow_add at H3,
    replace H3 := y.1.is_prime.mem_of_pow_mem _ H3,
    apply y_mem,
    exact H3, },

  simp only [submonoid.coe_one, one_mul, mul_one],
  simp only [subtype.coe_mk],

  rw calc degree_zero_part.num (data.num hm f_deg 1 y)
        * f ^ degree_zero_part.deg (data.denom hm f_deg 1 y)
        * (C * (f ^ l * f ^ n1))
      = degree_zero_part.num (data.num hm f_deg 1 y) * C
        * f ^ (degree_zero_part.deg (data.denom hm f_deg 1 y) + l)
        * f^n1 : by ring_exp,
  rw [pow_add, eq1],
  ring,
end

lemma bmk_zero :
  bmk hm f_deg V 0 = 0 :=
begin
  ext1 y,
  have y_mem : y.val ∈ (pbo f).val,
  { erw projective_spectrum.mem_basic_open,
    intro rid,
    have mem1 := y.2,
    erw set.mem_preimage at mem1,
    obtain ⟨⟨a, ha1⟩, ha, ha2⟩ := mem1,
    change a = y.1 at ha2,
    erw set.mem_preimage at ha,
    erw ←ha2 at rid,
    apply ha1,
    exact rid },

  rw pi.zero_apply,
  unfold bmk,
  rw [homogeneous_localization.ext_iff_val, homogeneous_localization.val_mk', homogeneous_localization.zero_val],
  simp only [← subtype.val_eq_coe],
  rw [show (0 : localization.at_prime y.1.as_homogeneous_ideal.to_ideal) = localization.mk 0 1,
    by erw localization.mk_zero],
  dsimp only,
  unfold num denom,

  have eq1 := data.eq_num_div_denom hm f_deg 0 y,
  rw [data.zero, pi.zero_apply] at eq1,
  replace eq1 := eq1.symm,
  erw [show (0 : structure_sheaf.localizations (A⁰_ f_deg)
    (((Proj_iso_Spec_Top_component hm f_deg).hom) ⟨y.val, y_mem⟩)) = localization.mk 0 1,
    by erw localization.mk_zero, localization.mk_eq_mk', is_localization.eq] at eq1,

  obtain ⟨⟨⟨C, C_degree_zero⟩, hC⟩, eq1⟩ := eq1,
  induction C using localization.induction_on with 𝔻,
  obtain ⟨C, ⟨_, ⟨l, rfl⟩⟩⟩ := 𝔻,
  simp only [submonoid.coe_one, mul_one, one_mul, subtype.coe_mk] at eq1,
  simp only [zero_mul] at eq1,
  simp only [localization.mk_eq_mk', is_localization.eq],
  change _ ∉ _ at hC,
  erw Proj_iso_Spec_Top_component.to_Spec.mem_carrier_iff at hC,
  dsimp only [subtype.coe_mk] at C_degree_zero hC,

  have eq_num := degree_zero_part.eq (data.num hm f_deg 0 y),
  have eq_denom := degree_zero_part.eq (data.denom hm f_deg 0 y),

  rw subtype.ext_iff at eq1,
  simp only [subring.coe_mul, subtype.coe_mk] at eq1,
  rw [eq_num, subring.coe_zero,
    show (0 : localization.away f) = localization.mk 0 1, by rw localization.mk_zero,
    localization.mk_mul] at eq1,
  simp only [localization.mk_eq_mk', is_localization.eq] at eq1,
  obtain ⟨⟨_, ⟨n1, rfl⟩⟩, eq1⟩ := eq1,
  simp only [submonoid.coe_mul, ←pow_add,
    submonoid.coe_one, mul_one, zero_mul, subtype.coe_mk] at eq1,

  have C_not_mem : C ∉ y.1.as_homogeneous_ideal,
  { intro rid,
    have eq1 : (localization.mk C ⟨f ^ l, ⟨_, rfl⟩⟩ : localization.away f) =
      (localization.mk 1 ⟨f^l, ⟨_, rfl⟩⟩ : localization.away f) * localization.mk C 1,
      rw [localization.mk_mul, one_mul, mul_one],
    erw eq1 at hC,
    apply hC,
    convert ideal.mul_mem_left _ _ _,
    apply ideal.subset_span,
    refine ⟨C, rid, rfl⟩, },

  use C * f^n1,
  { intro rid,
    rcases y.1.is_prime.mem_or_mem rid with H1 | H2,
    apply C_not_mem H1,
    replace H2 := y.1.is_prime.mem_of_pow_mem _ H2,
    apply y_mem,
    exact H2, },

  simp only [submonoid.coe_one, zero_mul, mul_one],
  simp only [← subtype.val_eq_coe],

  rw calc degree_zero_part.num (data.num hm f_deg 0 y)
        * f ^ degree_zero_part.deg (data.denom hm f_deg 0 y)
        * (C * f ^ n1)
      = degree_zero_part.num (data.num hm f_deg 0 y)
        * C * f ^ n1
        * f ^ degree_zero_part.deg (data.denom hm f_deg 0 y)
      : by ring,
  rw [eq1, zero_mul],
end

lemma bmk_add (x y : (Spec (A⁰_ f_deg)).presheaf.obj V) :
  bmk hm f_deg V (x + y) = bmk hm f_deg V x + bmk hm f_deg V y :=
begin
  ext1 z,
  have z_mem : z.val ∈ (projective_spectrum.basic_open 𝒜 f).val,
  { erw projective_spectrum.mem_basic_open,
    intro rid,
    have mem1 := z.2,
    erw set.mem_preimage at mem1,
    obtain ⟨⟨a, ha1⟩, ha, ha2⟩ := mem1,
    change a = z.1 at ha2,
    erw set.mem_preimage at ha,
    erw ←ha2 at rid,
    apply ha1,
    exact rid },

  rw pi.add_apply,
  unfold bmk,
  simp only [homogeneous_localization.ext_iff_val, homogeneous_localization.val_mk', homogeneous_localization.add_val, ←subtype.val_eq_coe],
  unfold num denom,
  dsimp only,

  have add_eq := data.eq_num_div_denom hm f_deg (x + y) z,
  rw [data.add_apply, data.eq_num_div_denom, data.eq_num_div_denom, add_mk] at add_eq,
  simp only [localization.mk_eq_mk'] at add_eq,
  erw is_localization.eq at add_eq,
  obtain ⟨⟨⟨C, C_degree_zero⟩, hC⟩, add_eq⟩ := add_eq,
  induction C using localization.induction_on with 𝔻,
  obtain ⟨C, ⟨_, ⟨l, rfl⟩⟩⟩ := 𝔻,
  change _ ∉ _ at hC, 
  erw Proj_iso_Spec_Top_component.to_Spec.mem_carrier_iff at hC,
  simp only [subtype.coe_mk] at hC,
  simp only [submonoid.coe_mul, subtype.coe_mk] at add_eq,
  rw subtype.ext_iff at add_eq,
  simp only [subring.coe_add, subring.coe_mul, subtype.coe_mk] at add_eq,

  have C_not_mem : C ∉ z.1.as_homogeneous_ideal,
  { intro rid,
    have eq1 : (localization.mk C ⟨f ^ l, ⟨_, rfl⟩⟩ : localization.away f) =
      (localization.mk 1 ⟨f^l, ⟨_, rfl⟩⟩ : localization.away f) * localization.mk C 1,
      rw [localization.mk_mul, one_mul, mul_one],
    erw eq1 at hC,
    apply hC,
    convert ideal.mul_mem_left _ _ _,
    apply ideal.subset_span,
    exact ⟨C, rid, rfl⟩, },

  simp only [degree_zero_part.eq, localization.mk_mul, localization.add_mk,
    submonoid.coe_mul] at add_eq,
  rw [localization.mk_eq_mk', is_localization.eq] at add_eq,
  obtain ⟨⟨_, ⟨n1, rfl⟩⟩, add_eq⟩ := add_eq,
  simp only [←subtype.val_eq_coe,
    submonoid.coe_mul] at add_eq,

  set a_xy : A := degree_zero_part.num (data.num hm f_deg (x + y) z) with a_xy_eq,
  set i_xy : ℕ := degree_zero_part.deg (data.num hm f_deg (x + y) z) with i_xy_eq,
  set b_xy : A := degree_zero_part.num (data.denom hm f_deg (x + y) z) with b_xy_eq,
  set j_xy : ℕ := degree_zero_part.deg (data.denom hm f_deg (x + y) z) with j_xy_eq,

  set a_x : A := degree_zero_part.num (data.num hm f_deg x z) with a_x_eq,
  set i_x : ℕ := degree_zero_part.deg (data.num hm f_deg x z) with i_x_eq,
  set b_x : A := degree_zero_part.num (data.denom hm f_deg x z) with b_x_eq,
  set j_x : ℕ := degree_zero_part.deg (data.denom hm f_deg x z) with j_x_eq,

  set a_y : A := degree_zero_part.num (data.num hm f_deg y z) with a_y_eq,
  set i_y : ℕ := degree_zero_part.deg (data.num hm f_deg y z) with i_y_eq,
  set b_y : A := degree_zero_part.num (data.denom hm f_deg y z) with b_y_eq,
  set j_y : ℕ := degree_zero_part.deg (data.denom hm f_deg y z) with j_y_eq,

  simp only [←a_xy_eq, ←i_xy_eq, ←b_xy_eq, ←j_xy_eq, ←a_x_eq, ←i_x_eq, ←b_x_eq, ←j_x_eq, ←a_y_eq, ←b_y_eq, ←i_y_eq, ←j_y_eq] at add_eq ⊢,

  rw localization.add_mk,
  simp only [←subtype.val_eq_coe,
    show ∀ (α β : z.1.as_homogeneous_ideal.to_ideal.prime_compl), α * β = ⟨α.1 * β.1, begin
      intro rid,
      rcases z.1.is_prime.mem_or_mem rid,
      apply α.2 h,
      apply β.2 h,
    end⟩,
    begin
      intros α β,
      simp only [subtype.ext_iff],
      refl,
    end,
    show b_x * f ^ i_x * (a_y * f ^ j_y) = a_y * b_x * f ^ (i_x + j_y),
    begin
      rw pow_add, ring,
    end,
    show b_y * f ^ i_y * (a_x * f ^ j_x) = a_x * b_y * f ^ (i_y + j_x),
    begin
      rw pow_add, ring
    end,
    show b_x * f ^ i_x * (b_y * f ^ i_y) = b_x * b_y * f ^ (i_x + i_y),
    begin
      rw pow_add, ring
    end],
  rw [calc (f ^ j_x * f ^ i_y * (b_y * a_x) + f ^ j_y * f ^ i_x * (b_x * a_y)) * b_xy * C
          * (f ^ i_xy * (f ^ j_x * f ^ j_y) * f ^ l) * f ^ n1
        = ((f ^ j_x * f ^ i_y) * (b_y * a_x) + (f ^ j_y * f ^ i_x) * (b_x * a_y)) * b_xy * C
          * ((f ^ i_xy * (f ^ j_x * f ^ j_y) * f ^ l) * f ^ n1) : by ring
    ... = ((f ^ (j_x + i_y)) * (b_y * a_x) + (f ^ (j_y + i_x)) * (b_x * a_y)) * b_xy * C
          * f ^ ((((i_xy + (j_x + j_y))) + l) + n1)
        : begin
          congr',
          all_goals { repeat { rw pow_add } },
        end,
      calc a_xy * (b_x * b_y) * C * (f ^ j_x * f ^ i_y * (f ^ j_y * f ^ i_x) * f ^ j_xy * f ^ l) * f ^ n1
        = a_xy * (b_x * b_y) * C * ((f ^ j_x * f ^ i_y * (f ^ j_y * f ^ i_x) * f ^ j_xy * f ^ l) * f ^ n1) : by ring
    ... = a_xy * (b_x * b_y) * C * f ^ (((((j_x + i_y) + (j_y + i_x)) + j_xy) + l) + n1) : by simp only [pow_add]] at add_eq,

  simp only [localization.mk_eq_mk', is_localization.eq],
  refine ⟨⟨C * f ^ ((j_x + j_y) + l + n1), begin
    intro rid,
    rcases z.1.is_prime.mem_or_mem rid with H1 | H2,
    apply C_not_mem H1,
    replace H2 := z.1.is_prime.mem_of_pow_mem _ H2,
    apply z_mem H2,
  end⟩, _⟩,
  simp only [←subtype.val_eq_coe],

  rw [calc (a_y * b_x * f ^ (i_x + j_y) + a_x * b_y * f ^ (i_y + j_x)) * (b_xy * f ^ i_xy)
          * (C * f ^ ((j_x + j_y) + l + n1))
        = (f ^ (i_y + j_x) * (b_y * a_x) +  f ^ (i_x + j_y) * (b_x * a_y)) * b_xy * C
          * (f ^ i_xy * f ^ ((j_x + j_y) + l + n1)) : by ring
    ... = (f ^ (i_y + j_x) * (b_y * a_x) +  f ^ (i_x + j_y) * (b_x * a_y)) * b_xy * C
          * (f ^ (i_xy + ((j_x + j_y) + l + n1))) : by simp only [pow_add]
    ... = (f ^ (j_x + i_y) * (b_y * a_x) +  f ^ (j_y + i_x) * (b_x * a_y)) * b_xy * C
          * (f ^ (i_xy + (j_x + j_y) + l + n1))
        : begin
          congr' 1,
          congr' 5,
          all_goals { simp only [add_comm, add_assoc], },
        end, add_eq],
  simp only [pow_add],
  ring,
end

lemma bmk_mul (x y : (Spec (A⁰_ f_deg)).presheaf.obj V) :
  bmk hm f_deg V (x * y) = bmk hm f_deg V x * bmk hm f_deg V y :=
begin
  ext1 z,
  have z_mem : z.val ∈ (projective_spectrum.basic_open 𝒜 f).val,
  { erw projective_spectrum.mem_basic_open,
    intro rid,
    have mem1 := z.2,
    erw set.mem_preimage at mem1,
    obtain ⟨⟨a, ha1⟩, ha, ha2⟩ := mem1,
    change a = z.1 at ha2,
    erw set.mem_preimage at ha,
    erw ←ha2 at rid,
    apply ha1,
    exact rid, },

  rw pi.mul_apply,
  unfold bmk,
  simp only [homogeneous_localization.ext_iff_val, homogeneous_localization.val_mk', homogeneous_localization.mul_val, ← subtype.val_eq_coe],
  unfold num denom,

  have mul_eq := data.eq_num_div_denom hm f_deg (x * y) z,
  rw [data.mul_apply, data.eq_num_div_denom, data.eq_num_div_denom, localization.mk_mul] at mul_eq,
  simp only [localization.mk_eq_mk'] at mul_eq,
  erw is_localization.eq at mul_eq,
  obtain ⟨⟨⟨C, C_degree_zero⟩, hC⟩, mul_eq⟩ := mul_eq,
  induction C using localization.induction_on with 𝔻,
  obtain ⟨C, ⟨_, ⟨l, rfl⟩⟩⟩ := 𝔻,
  change _ ∉ _ at hC,
  erw Proj_iso_Spec_Top_component.to_Spec.mem_carrier_iff at hC,
  simp only [subtype.coe_mk] at hC,
  simp only [←subtype.val_eq_coe] at mul_eq,
  rw subtype.ext_iff at mul_eq,

  have C_not_mem : C ∉ z.1.as_homogeneous_ideal,
  { intro rid,
    have eq1 : (localization.mk C ⟨f ^ l, ⟨_, rfl⟩⟩ : localization.away f) =
      (localization.mk 1 ⟨f^l, ⟨_, rfl⟩⟩ : localization.away f) * localization.mk C 1,
      rw [localization.mk_mul, one_mul, mul_one],
    erw eq1 at hC,
    apply hC,
    convert ideal.mul_mem_left _ _ _,
    apply ideal.subset_span,
    exact ⟨C, rid, rfl⟩, },

  simp only [subring.coe_mul, coe_add, subtype.coe_mk,
    show ∀ (α β : (prime_spectrum.as_ideal (((Proj_iso_Spec_Top_component hm f_deg).hom)
      ⟨z.val, z_mem⟩)).prime_compl),
      (α * β).1 = α.1 * β.1, from λ _ _, rfl] at mul_eq,
  simp only [degree_zero_part.eq, localization.mk_mul, localization.add_mk,
    submonoid.coe_mul] at mul_eq,
  rw [localization.mk_eq_mk', is_localization.eq] at mul_eq,
  obtain ⟨⟨_, ⟨n1, rfl⟩⟩, mul_eq⟩ := mul_eq,
  simp only [←subtype.val_eq_coe,
    submonoid.coe_mul] at mul_eq,

  set a_xy : A := degree_zero_part.num (data.num hm f_deg (x * y) z) with a_xy_eq,
  set i_xy : ℕ := degree_zero_part.deg (data.num hm f_deg (x * y) z) with i_xy_eq,
  set b_xy : A := degree_zero_part.num (data.denom hm f_deg (x * y) z) with b_xy_eq,
  set j_xy : ℕ := degree_zero_part.deg (data.denom hm f_deg (x * y) z) with j_xy_eq,

  set a_x : A := degree_zero_part.num (data.num hm f_deg x z) with a_x_eq,
  set i_x : ℕ := degree_zero_part.deg (data.num hm f_deg x z) with i_x_eq,
  set b_x : A := degree_zero_part.num (data.denom hm f_deg x z) with b_x_eq,
  set j_x : ℕ := degree_zero_part.deg (data.denom hm f_deg x z) with j_x_eq,

  set a_y : A := degree_zero_part.num (data.num hm f_deg y z) with a_y_eq,
  set i_y : ℕ := degree_zero_part.deg (data.num hm f_deg y z) with i_y_eq,
  set b_y : A := degree_zero_part.num (data.denom hm f_deg y z) with b_y_eq,
  set j_y : ℕ := degree_zero_part.deg (data.denom hm f_deg y z) with j_y_eq,

  simp only [←a_xy_eq, ←i_xy_eq, ←b_xy_eq, ←j_xy_eq, ←a_x_eq, ←i_x_eq, ←b_x_eq, ←j_x_eq, ←a_y_eq, ←b_y_eq, ←i_y_eq, ←j_y_eq] at mul_eq ⊢,
  rw [localization.mk_mul, localization.mk_eq_mk', is_localization.eq],
  refine ⟨⟨C * f^(l + n1), begin
    intro rid,
    rcases z.1.is_prime.mem_or_mem rid with H1 | H2,
    apply C_not_mem H1,
    replace H2 := z.1.is_prime.mem_of_pow_mem _ H2,
    apply z_mem H2,
  end⟩, _⟩,
  simp only [←subtype.val_eq_coe,
    show ∀ (α β : z.1.as_homogeneous_ideal.to_ideal.prime_compl), (α * β).1 = α.1 * β.1,
    from λ _ _, rfl],
  simp only [pow_add],
  ring_nf at mul_eq ⊢,
  rw mul_eq,
end

namespace is_locally_quotient

variable {V}
lemma mem_pbo : y.1 ∈ pbo f :=
begin
  rw projective_spectrum.mem_basic_open,
  intro rid,
  have mem1 := y.2,
  erw set.mem_preimage at mem1,
  obtain ⟨⟨a, ha1⟩, ha, ha2⟩ := mem1,
  erw set.mem_preimage at ha,
  erw ←ha2 at rid,
  apply ha1,
  exact rid,
end

lemma hom_apply_mem :
  (Proj_iso_Spec_Top_component hm f_deg).hom ⟨y.1, mem_pbo hm f_deg y⟩ ∈ unop V := 
begin
  obtain ⟨a, ha1, ha2⟩ := y.2,
  erw set.mem_preimage at ha1,
  change ((Proj_iso_Spec_Top_component hm f_deg).hom ⟨y.1, _⟩) ∈ (unop V).1,
  convert ha1,
  rw subtype.ext_iff,
  exact ha2.symm,
end

def Uo (VV : opens (Spec.T (A⁰_ f_deg))) :
  opens (projective_spectrum.Top 𝒜) :=
⟨{x | ∃ x' : homeo_of_iso (Proj_iso_Spec_Top_component hm f_deg) ⁻¹' VV.1, x = x'.1.1}, begin
  have O1 := (homeomorph.is_open_preimage (homeo_of_iso (Proj_iso_Spec_Top_component hm f_deg))).2 VV.2,
  rw is_open_induced_iff at O1,
  obtain ⟨s, Os, set_eq1⟩ := O1,
  have O2 : is_open (s ∩ (projective_spectrum.basic_open 𝒜 f).1),
  apply is_open.inter Os (projective_spectrum.basic_open 𝒜 f).2,
  convert O2,
  ext γ, split; intros hγ,
  { obtain ⟨x', rfl⟩ := hγ,
    have mem1 := x'.2,
    simp only [←set_eq1] at mem1,
    erw set.mem_preimage at mem1,
    refine ⟨mem1, _⟩,
    have mem2 := x'.2,
    rw set.mem_preimage at mem2,
    intro rid,
    have mem3 : (⟨localization.mk f ⟨f^1, ⟨_, rfl⟩⟩, ⟨1, ⟨_, by simpa [mul_one] using f_deg⟩, rfl⟩⟩ : A⁰_ f_deg) ∈ ((Proj_iso_Spec_Top_component hm f_deg).hom x'.1).as_ideal,
    { erw Proj_iso_Spec_Top_component.to_Spec.mem_carrier_iff,
      change (localization.mk f ⟨f^1, ⟨_, rfl⟩⟩ : localization.away f) ∈ ideal.span _,
      convert ideal.mul_mem_left _ _ _,
      work_on_goal 2
      { exact mk 1 ⟨f^1, ⟨_, rfl⟩⟩ },
      work_on_goal 2
      { exact mk f 1 },
      { rw [mk_mul, one_mul, mul_one], },
      { apply ideal.subset_span,
        refine ⟨f, rid, rfl⟩, } },
    have mem4 : (1 : A⁰_ f_deg) ∈ ((Proj_iso_Spec_Top_component hm f_deg).hom x'.1).as_ideal,
    { convert mem3,
      rw [subtype.ext_iff, subring.coe_one],
      dsimp only [subtype.coe_mk],
      symmetry,
      convert localization.mk_self _,
      erw [←subtype.val_eq_coe],
      dsimp only,
      rw pow_one, },
    apply ((Proj_iso_Spec_Top_component hm f_deg).hom x'.1).is_prime.1,
    rw ideal.eq_top_iff_one,
    exact mem4, },

  { rcases hγ with ⟨hγ1, hγ2⟩,
    use ⟨γ, hγ2⟩,
    rw [←set_eq1, set.mem_preimage],
        convert hγ1, }
end⟩

lemma subset2 (VV : opens (Spec.T (A⁰_ f_deg)))
  (subset1 : VV ⟶ unop V) :
  Uo hm f_deg VV ⟶
  (((@opens.open_embedding Proj.T (pbo f)).is_open_map.functor.op.obj
        ((opens.map (Proj_iso_Spec_Top_component hm f_deg).hom).op.obj V)).unop) :=
begin
  apply hom_of_le,
  intros γ γ_mem,
  change γ ∈ _ at γ_mem,
  replace subset3 := le_of_hom subset1,
  obtain ⟨⟨γ, γ_mem⟩, rfl⟩ := γ_mem,
  erw set.mem_preimage at γ_mem,
  refine ⟨γ, _, _⟩,
  erw set.mem_preimage,
  apply subset3,
  exact γ_mem,
  rw subtype.ext_iff,
  dsimp only,
  rw show (opens.inclusion _ γ = γ.1), from rfl,
end

end is_locally_quotient

lemma is_locally_quotient :
  ∃ (U : opens _) (mem : y.val ∈ U)
    (subset1 : U ⟶
      (((@opens.open_embedding (projective_spectrum.Top 𝒜) (projective_spectrum.basic_open 𝒜 f)).is_open_map.functor.op.obj
        ((opens.map (Proj_iso_Spec_Top_component hm f_deg).hom).op.obj V)).unop))
    (a b : A) (degree : ℕ) (a_hom : a ∈ 𝒜 degree) (b_hom : b ∈ 𝒜 degree),
    ∀ (x : U),
      ∃ (s_nin : b ∉ projective_spectrum.as_homogeneous_ideal x.val),
        (bmk hm f_deg V hh ⟨x.1, (subset1 x).2⟩).val = mk a ⟨b, s_nin⟩ :=
begin
  have y_mem : y.val ∈ projective_spectrum.basic_open 𝒜 f,
  { convert is_locally_quotient.mem_pbo hm f_deg y, },

  have hom_y_mem : (Proj_iso_Spec_Top_component hm f_deg).hom ⟨y.1, y_mem⟩ ∈ unop V,
  { convert is_locally_quotient.hom_apply_mem hm f_deg y, },
  have is_local := hh.2,
  rw structure_sheaf.is_locally_fraction_pred' at is_local,
  specialize is_local ⟨(Proj_iso_Spec_Top_component hm f_deg).hom ⟨y.1, y_mem⟩, hom_y_mem⟩,
  obtain ⟨VV, hom_y_mem_VV, subset1, ⟨α, ⟨l1, ⟨α', α'_mem⟩, rfl⟩⟩, ⟨β, ⟨l2, ⟨β', β'_mem⟩, rfl⟩⟩, is_local⟩ := is_local,

  set U := is_locally_quotient.Uo hm f_deg VV with U_eq,

  have y_mem_U : y.1 ∈ U,
  { use ⟨y.1, y_mem⟩,
    rw set.mem_preimage,
    exact hom_y_mem_VV, },

  set subset2 : U ⟶ _ := is_locally_quotient.subset2 hm f_deg VV subset1,
  refine ⟨U, y_mem_U, subset2, α' * f^l2, β' * f^l1, m * l1 + l2 * m,
    set_like.graded_monoid.mul_mem α'_mem (set_like.graded_monoid.pow_mem _ f_deg),
    by { convert set_like.graded_monoid.mul_mem β'_mem (set_like.graded_monoid.pow_mem _ f_deg) using 2, rw [smul_eq_mul], ring, }, _⟩,


  rintros ⟨z, z_mem_U⟩,
  have z_mem_bo : z ∈ pbo f,
  { obtain ⟨⟨z, hz⟩, rfl⟩ := z_mem_U,
    rw set.mem_preimage at hz,
    apply z.2, },

  have hom_z_mem_VV : ((Proj_iso_Spec_Top_component hm f_deg).hom) ⟨z, z_mem_bo⟩ ∈ VV,
  { obtain ⟨γ, h1, h2⟩ := z_mem_U,
    have mem1 := γ.2,
    erw set.mem_preimage at mem1,
    exact mem1, },

  specialize is_local ⟨((Proj_iso_Spec_Top_component hm f_deg).hom ⟨z, z_mem_bo⟩), hom_z_mem_VV⟩,
  obtain ⟨not_mem1, eq1⟩ := is_local,

  have not_mem2 : β' * f ^ l1 ∉ z.as_homogeneous_ideal,
  { intro rid,
    rcases z.is_prime.mem_or_mem rid with H1 | H2,
    { apply not_mem1,
      have eq2 : (localization.mk β' ⟨f^l2, ⟨_, rfl⟩⟩ : localization.away f) =
        localization.mk 1 ⟨f^l2, ⟨_, rfl⟩⟩ * localization.mk β' 1,
      { rw [localization.mk_mul, one_mul, mul_one], },
      simp only [eq2],
      erw Proj_iso_Spec_Top_component.to_Spec.mem_carrier_iff,
      dsimp only,
      convert ideal.mul_mem_left _ _ _,
      apply ideal.subset_span,
      refine ⟨β', H1, rfl⟩, },
    { replace H2 := z.is_prime.mem_of_pow_mem _ H2,
      exact z_mem_bo H2, } },
  refine ⟨not_mem2, _⟩,
  have data_eq : data hm f_deg hh (subset2 ⟨z, z_mem_U⟩) =
    hh.val (subset1 ⟨((Proj_iso_Spec_Top_component hm f_deg).hom) ⟨z, z_mem_bo⟩, hom_z_mem_VV⟩),
  { congr', },
  rw ←data_eq at eq1,

  have z_mem2 : z ∈ (((@opens.open_embedding Proj.T (pbo f)).is_open_map.functor.op.obj
        ((opens.map (Proj_iso_Spec_Top_component hm f_deg).hom).op.obj V)).unop),
  { use z,
    refine ⟨_, rfl⟩,
    erw set.mem_preimage,
    apply (le_of_hom subset1),
    exact hom_z_mem_VV, },

  have data_eq2 : data hm f_deg hh (subset2 ⟨z, z_mem_U⟩) = data hm f_deg hh ⟨z, z_mem2⟩,
  { congr', },
  rw [data_eq2, data.eq_num_div_denom, localization.mk_eq_mk'] at eq1,
  erw is_localization.eq at eq1,

  obtain ⟨⟨⟨_, ⟨L, ⟨C, C_mem⟩, rfl⟩⟩, hC⟩, eq1⟩ := eq1,
  simp only [subtype.ext_iff, subring.coe_mul] at eq1,
  simp only [degree_zero_part.eq, localization.mk_mul, subtype.coe_mk] at eq1,
  erw [localization.mk_eq_mk', is_localization.eq] at eq1,
  obtain ⟨⟨_, ⟨M, rfl⟩⟩, eq1⟩ := eq1,
  simp only [←subtype.val_eq_coe,
    submonoid.coe_mul, ←pow_add] at eq1,

  unfold bmk,
  rw [homogeneous_localization.val_mk'],
  simp only [← subtype.val_eq_coe],
  unfold num denom,

  set p := degree_zero_part.num (data.num hm f_deg hh ⟨z, z_mem2⟩) with p_eq,
  set q := degree_zero_part.num (data.denom hm f_deg hh ⟨z, z_mem2⟩) with q_eq,
  set ii := degree_zero_part.deg (data.num hm f_deg hh ⟨z, z_mem2⟩) with ii_eq,
  set jj := degree_zero_part.deg (data.denom hm f_deg hh ⟨z, z_mem2⟩) with jj_eq,

  simp only [localization.mk_eq_mk', is_localization.eq],

  have C_not_mem : C ∉ z.as_homogeneous_ideal,
  { intro rid,
    have eq1 : (localization.mk C ⟨f ^ L, ⟨_, rfl⟩⟩ : localization.away f) =
      (localization.mk 1 ⟨f^L, ⟨_, rfl⟩⟩ : localization.away f) * localization.mk C 1,
      rw [localization.mk_mul, one_mul, mul_one],
    simp only [eq1, subtype.coe_mk] at hC,
    apply hC,
    change _ * _ ∈ _,
    rw [set_like.mem_coe],
    convert ideal.mul_mem_left _ _ _,
    apply ideal.subset_span,
    refine ⟨C, rid, rfl⟩ },

  refine ⟨⟨C * f^(L+M), begin
    intro rid,
    rcases z.is_prime.mem_or_mem rid with H1 | H2,
    apply C_not_mem H1,
    replace H2 := z.is_prime.mem_of_pow_mem _ H2,
    apply z_mem_bo,
    exact H2,
  end⟩, _⟩,

  simp only [←subtype.val_eq_coe,
    submonoid.coe_mul],

  suffices EQ : p * f^jj * (β' * f^l1) * (C * f^(L+M)) = α' * f^l2 * (q * f^ii) * (C * f^(L + M)),
  convert EQ,
  rw calc p * f^jj * (β' * f^l1) * (C * f^(L+M))
        = p * f^jj * (β' * f^l1) * (C * (f^L * f^M)) : by simp only [pow_add]
    ... = p * β' * C * (f^l1 * f^jj * f^L) * f^M : by ring
    ... = p * β' * C * f^(l1 + jj + L) * f^M : by simp only [pow_add]
    ... = α' * q * C * f ^ (ii + l2 + L) * f ^ M : by rw eq1,

  simp only [pow_add],
  ring,
end

def to_fun.aux (hh : (Spec (A⁰_ f_deg)).presheaf.obj V) : ((Proj_iso_Spec_Top_component hm f_deg).hom _* (Proj| (pbo f)).presheaf).obj V :=
⟨bmk hm f_deg V hh, λ y, begin 
  rcases is_locally_quotient hm f_deg V hh y with ⟨VV, mem1, subset1, a, b, degree, a_mem, b_mem, l⟩,
  refine ⟨VV, mem1, subset1, degree, ⟨a, a_mem⟩, ⟨b, b_mem⟩, λ x, _⟩,
  rcases l x with ⟨s_nin, l⟩,
  refine ⟨s_nin, _⟩,
  dsimp only,
  rw [homogeneous_localization.ext_iff_val, homogeneous_localization.val_mk'],
  simp only [← subtype.val_eq_coe],
  erw ← l,
  rw ← homogeneous_localization.ext_iff_val,
  congr' 1
end⟩

def to_fun : (Spec (A⁰_ f_deg)).presheaf.obj V ⟶ ((Proj_iso_Spec_Top_component hm f_deg).hom _* (Proj| (pbo f)).presheaf).obj V :=
{ to_fun := λ hh, to_fun.aux hm f_deg V hh,
  map_one' := begin
    rw subtype.ext_iff,
    convert bmk_one hm f_deg V,
  end,
  map_mul' := λ x y, begin
    rw subtype.ext_iff,
    convert bmk_mul hm f_deg V x y,
  end,
  map_zero' := begin
    rw subtype.ext_iff,
    convert bmk_zero hm f_deg V,
  end,
  map_add' := λ x y, begin
    rw subtype.ext_iff,
    convert bmk_add hm f_deg V x y,
  end }

end from_Spec

def from_Spec {f : A} {m : ℕ} (hm : 0 < m) (f_deg : f ∈ 𝒜 m) : 
  (Spec (A⁰_ f_deg)).presheaf ⟶ (Proj_iso_Spec_Top_component hm f_deg).hom _* (Proj| (pbo f)).presheaf :=
{ app := λ V, from_Spec.to_fun hm f_deg V,
  naturality' := λ U V subset1, begin
    ext1 z,
    simp only [comp_apply, ring_hom.coe_mk, functor.op_map, presheaf.pushforward_obj_map],
    refl,
  end }

end Proj_iso_Spec_Sheaf_component

end algebraic_geometry