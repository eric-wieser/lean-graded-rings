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

namespace to_Spec

variables {𝒜} {f : A} {m : ℕ} (hm : 0 < m) (f_deg : f ∈ 𝒜 m)
variable (U : (opens (Spec.T (A⁰_ f_deg)))ᵒᵖ)

local notation `pf_sheaf` x := (Proj_iso_Spec_Top_component hm f_deg).hom _* x.presheaf -- pushforward a sheaf

variable (hh : (pf_sheaf (Proj| (pbo f))).obj U)

lemma pf_sheaf.one_val :
  (1 : (pf_sheaf (Proj| (pbo f))).obj U).1 = 1 := rfl

lemma pf_sheaf.zero_val :
  (0 : (pf_sheaf (Proj| (pbo f))).obj U).1 = 0 := rfl

lemma pf_sheaf.add_val (x y : (pf_sheaf (Proj| (pbo f))).obj U) :
  (x + y).1 = x.1 + y.1 := rfl

lemma pf_sheaf.mul_val (x y : (pf_sheaf (Proj| (pbo f))).obj U) :
  (x * y).1 = x.1 * y.1 := rfl

variables {f_deg hm U}
lemma inv_mem (y : unop U) :
  ((Proj_iso_Spec_Top_component hm f_deg).inv y.1).1 ∈
    ((@opens.open_embedding Proj.T (pbo f)).is_open_map.functor.op.obj
      ((opens.map (Proj_iso_Spec_Top_component hm f_deg).hom).op.obj U)).unop :=
begin
  refine ⟨⟨((Proj_iso_Spec_Top_component hm f_deg).inv y.1).1, ((Proj_iso_Spec_Top_component hm f_deg).inv y.1).2⟩, _, rfl⟩,
  change _ ∈ _ ⁻¹' _,
  erw set.mem_preimage,
  change (Proj_iso_Spec_Top_component.to_Spec.to_fun 𝒜 f_deg (Proj_iso_Spec_Top_component.from_Spec.to_fun f_deg hm y.1)) ∈ _,
  erw Proj_iso_Spec_Top_component.to_Spec_from_Spec 𝒜 hm f_deg y.1,
  exact y.2,
end

variable (hm)
def hl (y : unop U) : homogeneous_localization 𝒜 _ :=
hh.1 ⟨((Proj_iso_Spec_Top_component hm f_deg).inv y.1).1, inv_mem y⟩

lemma hl.one (y : unop U) :
  hl hm 1 y = 1 :=
by rw [hl, pf_sheaf.one_val, pi.one_apply]

lemma hl.zero (y : unop U) :
  hl hm 0 y = 0 :=
by rw [hl, pf_sheaf.zero_val, pi.zero_apply]

lemma hl.add (x y : (pf_sheaf (Proj| (pbo f))).obj U) (z : unop U) :
  hl hm (x + y) z = hl hm x z + hl hm y z :=
by rw [hl, pf_sheaf.add_val, pi.add_apply, hl, hl]

lemma hl.mul (x y : (pf_sheaf (Proj| (pbo f))).obj U) (z : unop U) :
  hl hm (x * y) z = hl hm x z * hl hm y z :=
by rw [hl, hl, hl, pf_sheaf.mul_val, pi.mul_apply]


def num (y : unop U) : A⁰_ f_deg :=
⟨mk ((hl hm hh y).num * (hl hm hh y).denom ^ m.pred) ⟨f^(hl hm hh y).deg, ⟨_, rfl⟩⟩,
  ⟨(hl hm hh y).deg, ⟨(hl hm hh y).num * (hl hm hh y).denom ^ m.pred, begin
    convert mul_mem (hl hm hh y).num_mem (set_like.graded_monoid.pow_mem m.pred (hl hm hh y).denom_mem),
    exact calc m * (hl hm hh y).deg
            = (m.pred + 1) * (hl hm hh y).deg
            : begin
              congr,
              conv_lhs { rw ←nat.succ_pred_eq_of_pos hm },
            end
        ... = m.pred * (hl hm hh y).deg +
              1 * (hl hm hh y).deg
            : by rw add_mul
        ... = _ : begin
          rw [add_comm, one_mul],
          congr,
        end,
  end⟩, rfl⟩⟩

def denom (y : unop U) : A⁰_ f_deg :=
⟨mk ((hl hm hh y).denom ^ m) ⟨f^(hl hm hh y).deg, ⟨_, rfl⟩⟩,
  ⟨(hl hm hh y).deg, ⟨_, set_like.graded_monoid.pow_mem m (hl hm hh y).denom_mem⟩, rfl⟩⟩

lemma denom.not_mem (y : unop U) : denom hm hh y ∉ y.1.as_ideal := λ r,
begin
  have prop1 := (hl hm hh y).denom_not_mem,
  change _ ∉ (Proj_iso_Spec_Top_component.from_Spec.to_fun f_deg hm y.1).1.as_homogeneous_ideal at prop1,
  contrapose! prop1,
  change ∀ _, _,

  contrapose! prop1,
  obtain ⟨n, hn⟩ := prop1,

  have eq1 : (hl hm hh y).deg = n,
  { -- n ≠ i, contradiction,
    by_contra ineq,
    simp only [graded_algebra.proj_apply, direct_sum.decompose_of_mem_ne 𝒜 ((hl hm hh y).denom_mem) ineq, zero_pow hm, mk_zero] at hn,
    apply hn,
    exact submodule.zero_mem _, },
  apply hn,
  convert r,

  rw [graded_algebra.proj_apply, ←eq1, direct_sum.decompose_of_mem_same],
  exact (hl hm hh y).denom_mem,
  exact eq1.symm,
end

def fmk (y : unop U) : localization.at_prime y.1.as_ideal :=
mk (num hm hh y) ⟨denom hm hh y, denom.not_mem hm hh y⟩

lemma fmk.one (y : unop U) : fmk hm 1 y = 1 :=
begin
  unfold fmk,
  dsimp only,
  rw [show (1 : structure_sheaf.localizations (A⁰_ f_deg) y.val) =
    localization.mk 1 1, begin
      erw localization.mk_self 1,
    end, localization.mk_eq_mk', is_localization.eq],

  have eq1 := (hl hm 1 y).eq_num_div_denom,
  rw [hl.one, homogeneous_localization.one_val] at eq1,
  erw [show (1 : localization.at_prime ((Proj_iso_Spec_Top_component hm f_deg).inv y.1).1.as_homogeneous_ideal.to_ideal) =
    mk 1 1,
      begin
        symmetry,
        convert localization.mk_self _,
        refl,
      end, localization.mk_eq_mk', is_localization.eq] at eq1,
  obtain ⟨⟨c, hc1⟩, eq1⟩ := eq1,

  change ¬(∀ i : ℕ, _ ∈ _) at hc1,
  rw not_forall at hc1,
  obtain ⟨j, hc1⟩ := hc1,
  rw [one_mul, submonoid.coe_one, mul_one] at eq1,
  simp only [←subtype.val_eq_coe] at eq1,
  rw [← hl.one] at eq1,
  have eq2 : graded_algebra.proj 𝒜 ((hl hm 1 y).deg + j) ((hl hm 1 y).denom * c)
    = graded_algebra.proj 𝒜 ((hl hm 1 y).deg + j) ((hl hm 1 y).num * c),
  { exact congr_arg _ eq1, },

  have eq3 : graded_algebra.proj 𝒜 ((hl hm 1 y).deg + j) ((hl hm 1 y).denom * c)
    = (hl hm 1 y).denom * (graded_algebra.proj 𝒜 j c),
  { apply graded_algebra.proj_hom_mul,
    exact (hl hm 1 y).denom_mem,
    intro rid,
    apply hc1,
    simp only [rid, zero_pow hm, localization.mk_zero],
    exact submodule.zero_mem _, },

  have eq4 : graded_algebra.proj 𝒜 ((hl hm 1 y).deg + j)
    ((hl hm 1 y).num * c)
    = (hl hm 1 y).num * (graded_algebra.proj 𝒜 j c),
  { apply graded_algebra.proj_hom_mul,
    exact (hl hm 1 y).num_mem,
    intro rid,
    apply hc1,
    simp only [rid, zero_pow hm, localization.mk_zero],
    exact submodule.zero_mem _, },

  erw [eq3, eq4] at eq2,

  use mk ((graded_algebra.proj 𝒜 j c)^m) ⟨f^j, ⟨_, rfl⟩⟩,
  rw [submonoid.coe_one, one_mul, mul_one, ← subtype.val_eq_coe, ← subtype.val_eq_coe],
  dsimp only,

  unfold num denom,
  rw [subtype.ext_iff, subring.coe_mul],
  dsimp only [subtype.coe_mk],
  rw [mk_mul, subring.coe_mul],
  dsimp only [subtype.coe_mk],
  rw [mk_mul],
  congr' 1,
  exact calc (hl hm 1 y).num * (hl hm 1 y).denom ^ m.pred * (graded_algebra.proj 𝒜 j) c ^ m
          = (hl hm 1 y).num * (hl hm 1 y).denom ^ m.pred * (graded_algebra.proj 𝒜 j) c ^ (m.pred + 1)
          : begin
            congr',
            symmetry,
            apply nat.succ_pred_eq_of_pos,
            exact hm
          end
      ... = (hl hm 1 y).num * (hl hm 1 y).denom ^ m.pred * ((graded_algebra.proj 𝒜 j) c ^ m.pred * graded_algebra.proj 𝒜 j c)
          : by ring_exp
      ... = ((hl hm 1 y).num * graded_algebra.proj 𝒜 j c) * ((hl hm 1 y).denom ^ m.pred * (graded_algebra.proj 𝒜 j) c ^ m.pred)
          : by ring
      ... = ((hl hm 1 y).denom * graded_algebra.proj 𝒜 j c) * ((hl hm 1 y).denom ^ m.pred * (graded_algebra.proj 𝒜 j) c ^ m.pred)
          : by rw eq2
      ... = ((hl hm 1 y).denom * graded_algebra.proj 𝒜 j c) ^ (1 + m.pred)
          : by ring_exp
      ... = ((hl hm 1 y).denom * graded_algebra.proj 𝒜 j c) ^ m
          : begin
            congr' 1,
            rw [add_comm],
            convert nat.succ_pred_eq_of_pos hm,
          end
      ... = _ : by rw mul_pow,
end

lemma fmk.zero (y : unop U) : fmk hm 0 y = 0 :=
begin
  unfold fmk,
  rw [show (0 : structure_sheaf.localizations (A⁰_ f_deg) y.val) =
    localization.mk 0 1, begin
      rw localization.mk_zero,
    end, localization.mk_eq_mk', is_localization.eq],
  dsimp only,

  have eq1 := (hl hm 0 y).eq_num_div_denom,
  rw [hl.zero, homogeneous_localization.zero_val] at eq1,
  erw [show (0 : localization.at_prime ((Proj_iso_Spec_Top_component hm f_deg).inv y.1).1.as_homogeneous_ideal.to_ideal) =
    localization.mk 0 1,
      begin
        rw localization.mk_zero,
      end, localization.mk_eq_mk', is_localization.eq] at eq1,
  obtain ⟨⟨c, hc1⟩, eq1⟩ := eq1,
  rw [zero_mul, zero_mul, submonoid.coe_one, mul_one] at eq1,
  simp only [←subtype.val_eq_coe] at eq1,
  dsimp only at eq1,

  change c ∉ Proj_iso_Spec_Top_component.from_Spec.carrier _ at hc1,
  change ¬(∀ i : ℕ, _ ∈ _) at hc1,
  rw not_forall at hc1,
  obtain ⟨j, hc1⟩ := hc1,
  replace eq1 := eq1.symm,
  have eq2 : graded_algebra.proj 𝒜 ((hl hm 0 y).deg + j) ((hl hm 0 y).num * c) = 0,
  { erw [eq1, linear_map.map_zero], },
  have eq3 : graded_algebra.proj 𝒜 ((hl hm 0 y).deg + j) ((hl hm 0 y).num * c)
    = (hl hm 0 y).num * graded_algebra.proj 𝒜 j c,
  { apply graded_algebra.proj_hom_mul,
    exact (hl hm 0 y).num_mem,
    intro rid,
    apply hc1,
    simp only [rid, zero_pow hm, mk_zero],
    exact submodule.zero_mem _, },
    erw eq3 at eq2,

  use mk ((graded_algebra.proj 𝒜 j c)^m) ⟨f^j, ⟨_, rfl⟩⟩,
  unfold num,
  dsimp only [subtype.coe_mk],
  rw [subtype.ext_iff, subring.coe_mul, subring.coe_mul, subring.coe_mul, subring.coe_mul,
    add_submonoid_class.coe_zero, zero_mul, submonoid.coe_one, subring.coe_one, mul_one, zero_mul],
  dsimp only [subtype.coe_mk],
  rw [mk_mul],
  convert mk_zero _,
  exact calc (hl hm 0 y).num * (hl hm 0 y).denom ^ m.pred * (graded_algebra.proj 𝒜 j) c ^ m
          = (hl hm 0 y).num * (hl hm 0 y).denom ^ m.pred * (graded_algebra.proj 𝒜 j) c ^ (m.pred + 1)
          : begin
            congr',
            symmetry,
            apply nat.succ_pred_eq_of_pos,
            exact hm
          end
      ... = (hl hm 0 y).num * (hl hm 0 y).denom ^ m.pred * ((graded_algebra.proj 𝒜 j) c ^ m.pred * graded_algebra.proj 𝒜 j c)
          : by rw [pow_add, pow_one]
      ... = ((hl hm 0 y).num * graded_algebra.proj 𝒜 j c)
            * ((hl hm 0 y).denom ^ m.pred * (graded_algebra.proj 𝒜 j) c ^ m.pred) : by ring
      ... = 0 * ((hl hm 0 y).denom ^ m.pred * (graded_algebra.proj 𝒜 j) c ^ m.pred) : by rw eq2
      ... = 0 : by rw zero_mul,
end

lemma fmk.add (x y : (pf_sheaf (Proj| (pbo f))).obj U) (z : unop U) :
  fmk hm (x + y) z = fmk hm x z + fmk hm y z :=
begin
  unfold fmk,
  rw [localization.add_mk],

  have eq_xz := (hl hm x z).eq_num_div_denom,
  have eq_yz := (hl hm y z).eq_num_div_denom,
  have eq_addz := (hl hm (x + y) z).eq_num_div_denom,
  rw [hl.add, homogeneous_localization.add_val, eq_xz, eq_yz, localization.add_mk, localization.mk_eq_mk', is_localization.eq] at eq_addz,
  obtain ⟨⟨c, hc⟩, eq_addz⟩ := eq_addz,
  rw [submonoid.coe_mul] at eq_addz,
  simp only [←subtype.val_eq_coe] at eq_addz,

  set d_x := (hl hm x z).denom with dx_eq,
  set n_x := (hl hm x z).num with nx_eq,
  set d_y := (hl hm y z).denom with dy_eq,
  set n_y := (hl hm y z).num with ny_eq,
  set d_xy := (hl hm (x + y) z).denom with dxy_eq,
  set n_xy := (hl hm (x + y) z).num with nxy_eq,
  set i_x := (hl hm x z).deg with ix_eq,
  set i_y := (hl hm y z).deg with iy_eq,
  set i_xy := (hl hm (x + y) z).deg with ixy_eq,

  unfold num denom,
  simp only [←dx_eq, ←nx_eq, ←dy_eq, ←ny_eq, ←dxy_eq, ←nxy_eq, ←i_x, ←i_y, ←i_xy] at eq_addz ⊢,
  rw [localization.mk_eq_mk', is_localization.eq],

  change ¬(∀ i : ℕ, _ ∈ _) at hc,
  rw not_forall at hc,
  obtain ⟨j, hc⟩ := hc,

  use localization.mk ((graded_algebra.proj 𝒜 j c)^m) ⟨f^j, ⟨_, rfl⟩⟩,
  rw [submonoid.coe_mul],
  simp only [subtype.ext_iff, subring.coe_mul, add_mem_class.coe_add, mk_mul, add_mk,
    subtype.coe_mk],
  rw [localization.mk_eq_mk', is_localization.eq],
  use 1,
  simp only [submonoid.coe_one, submonoid.mk_mul_mk, set_like.coe_mk, mul_one, ← pow_add],

  rw calc (f ^ (i_x + i_y) * (d_y ^ m * (n_x * d_x ^ m.pred))
          + f ^ (i_y + i_x) * (d_x ^ m * (n_y * d_y ^ m.pred)))
          * d_xy ^ m
          * (graded_algebra.proj 𝒜 j) c ^ m
          * f ^ (i_xy + (i_x + i_y) + j)
        = (f ^ (i_x + i_y) * (d_y ^ m * (n_x * d_x ^ m.pred))
            + f ^ (i_x + i_y) * (d_x ^ m * (n_y * d_y ^ m.pred)))
          * d_xy ^ m
          * (graded_algebra.proj 𝒜 j) c ^ m
          * f ^ (i_xy + (i_x + i_y) + j)
        : begin
          congr' 4,
          rw add_comm,
        end
    ... = (f ^ (i_x + i_y) * (d_y ^ m * (n_x * d_x ^ m.pred) + d_x ^ m * (n_y * d_y ^ m.pred)))
          * d_xy ^ m
          * (graded_algebra.proj 𝒜 j) c ^ m
          * f ^ (i_xy + (i_x + i_y) + j)
        : begin
          congr' 3,
          rw mul_add,
        end
    ... = (d_y ^ m * (n_x * d_x ^ m.pred) + d_x ^ m * (n_y * d_y ^ m.pred))
          * d_xy ^ m
          * (graded_algebra.proj 𝒜 j) c ^ m
          * (f ^ (i_x + i_y) * f ^ (i_xy + (i_x + i_y) + j)) : by ring
    ... = (d_y ^ m * (n_x * d_x ^ m.pred) + d_x ^ m * (n_y * d_y ^ m.pred))
          * d_xy ^ m
          * (graded_algebra.proj 𝒜 j) c ^ m
          * (f ^ (i_x + i_y + (i_xy + (i_x + i_y) + j)))
        : begin
          congr' 1,
          rw [←pow_add],
        end
    ... = (d_y ^ m * (n_x * d_x ^ m.pred) + d_x ^ m * (n_y * d_y ^ m.pred))
          * d_xy ^ m
          * (graded_algebra.proj 𝒜 j) c ^ m
          * (f ^ (i_x + i_y + (i_y + i_x) + i_xy + j))
        : begin
          congr' 2,
          ring,
        end,
  congr' 1,
  suffices EQ : (d_x * n_y + d_y * n_x) * d_xy * graded_algebra.proj 𝒜 j c = n_xy * (d_x * d_y) * graded_algebra.proj 𝒜 j c,
  { rw calc n_xy * d_xy ^ m.pred * (d_x ^ m * d_y ^ m) * (graded_algebra.proj 𝒜 j) c ^ m
          = n_xy * d_xy ^ m.pred * (d_x ^ m * d_y ^ m) * (graded_algebra.proj 𝒜 j) c ^ (m.pred + 1)
          : begin
            congr',
            symmetry,
            apply nat.succ_pred_eq_of_pos hm,
          end
      ... = n_xy * d_xy ^ m.pred * (d_x ^ (m.pred + 1) * d_y ^ m) * (graded_algebra.proj 𝒜 j) c ^ (m.pred + 1)
          : begin
            congr',
            symmetry,
            apply nat.succ_pred_eq_of_pos hm,
          end
      ... = n_xy * d_xy ^ m.pred * (d_x ^ (m.pred + 1) * d_y ^ (m.pred + 1)) * (graded_algebra.proj 𝒜 j) c ^ (m.pred + 1)
          : begin
            congr',
            symmetry,
            apply nat.succ_pred_eq_of_pos hm,
          end
      ... = n_xy * d_xy ^ m.pred * (d_x ^ m.pred * d_x * (d_y ^ m.pred * d_y))
            * ((graded_algebra.proj 𝒜 j) c ^ m.pred * (graded_algebra.proj 𝒜 j) c)
          : begin
            simp only [pow_add, pow_one],
          end
      ... = (n_xy * (d_x * d_y) * graded_algebra.proj 𝒜 j c)
            * (d_xy ^ m.pred * d_x ^ m.pred * d_y ^ m.pred * (graded_algebra.proj 𝒜 j c) ^ m.pred)
          : by ring
      ... = ((d_x * n_y + d_y * n_x) * d_xy * (graded_algebra.proj 𝒜 j) c)
            * (d_xy ^ m.pred * d_x ^ m.pred * d_y ^ m.pred * (graded_algebra.proj 𝒜 j c) ^ m.pred)
          : by rw EQ
      ... = (d_x * n_y + d_y * n_x)
            * ((d_xy ^ m.pred * d_xy) * d_x ^ m.pred * d_y ^ m.pred
              * ((graded_algebra.proj 𝒜 j c) ^ m.pred * (graded_algebra.proj 𝒜 j c)))
          : by ring
      ... = (d_x * n_y + d_y * n_x)
            * (d_xy ^ m * d_x ^ m.pred * d_y ^ m.pred
              * (graded_algebra.proj 𝒜 j c) ^ m)
          : begin
            congr';
            conv_rhs { rw [show m = m.pred + 1, from (nat.succ_pred_eq_of_pos hm).symm] };
            rw [pow_add, pow_one],
          end
      ... = (d_x * n_y + d_y * n_x)
            * d_x ^ m.pred * d_y ^ m.pred * d_xy ^ m
            * (graded_algebra.proj 𝒜 j c) ^ m : by ring,
    congr',

    exact calc (d_x * n_y + d_y * n_x) * d_x ^ m.pred * d_y ^ m.pred
          = (d_y ^ m.pred * d_y) * (n_x * d_x ^ m.pred) + (d_x ^ m.pred * d_x) * (n_y * d_y ^ m.pred)
          : by ring
      ... = (d_y ^ m.pred * d_y^1) * (n_x * d_x ^ m.pred) + (d_x ^ m.pred * d_x ^ 1) * (n_y * d_y ^ m.pred)
          : by simp only [pow_one]
      ... = (d_y ^ (m.pred + 1)) * (n_x * d_x ^ m.pred) + (d_x ^ (m.pred + 1)) * (n_y * d_y ^ m.pred)
          : by simp only [pow_add]
      ... = d_y ^ m * (n_x * d_x ^ m.pred) + d_x ^ m * (n_y * d_y ^ m.pred)
          : begin
            congr';
            apply nat.succ_pred_eq_of_pos hm,
          end, },

  replace eq_addz := congr_arg (graded_algebra.proj 𝒜 ((i_x + i_y) + i_xy + j)) eq_addz,
  have eq1 : (graded_algebra.proj 𝒜 (i_x + i_y + i_xy + j)) ((d_x * n_y + d_y * n_x) * d_xy * c)
    = (d_x * n_y + d_y * n_x) * d_xy * graded_algebra.proj 𝒜 j c,
  { apply graded_algebra.proj_hom_mul,
    { apply set_like.graded_monoid.mul_mem,
      apply submodule.add_mem _ _ _,
      apply set_like.graded_monoid.mul_mem,
      exact (hl hm x z).denom_mem,
      exact (hl hm y z).num_mem,
      rw add_comm,
      apply set_like.graded_monoid.mul_mem,
      exact (hl hm y z).denom_mem,
      exact (hl hm x z).num_mem,
      exact (hl hm (x + y) z).denom_mem, },
    intro rid,
    apply hc,
    simp only [rid, zero_pow hm, localization.mk_zero],
    exact submodule.zero_mem _, },
  erw eq1 at eq_addz,
  clear eq1,

  have eq2 : (graded_algebra.proj 𝒜 (i_x + i_y + i_xy + j)) (n_xy * (d_x * d_y) * c)
    = n_xy * (d_x * d_y) * graded_algebra.proj 𝒜 j c,
  { apply graded_algebra.proj_hom_mul,
    { rw show i_x + i_y + i_xy = i_xy + (i_x + i_y), by ring,
      apply set_like.graded_monoid.mul_mem,
      exact (hl hm (x + y) z).num_mem,
      apply set_like.graded_monoid.mul_mem,
      exact (hl hm _ z).denom_mem,
      exact (hl hm _ z).denom_mem, },
    intro rid,
    apply hc,
    simp only [rid, zero_pow hm, localization.mk_zero],
    exact submodule.zero_mem _, },
  erw eq2 at eq_addz,
  exact eq_addz,
end

lemma fmk.mul (x y : (pf_sheaf (Proj| (pbo f))).obj U) (z : unop U) :
  fmk hm (x * y) z = fmk hm x z * fmk hm y z :=
begin
  unfold fmk,
  rw [mk_mul],

  have eq_xz := (hl hm x z).eq_num_div_denom,
  have eq_yz := (hl hm y z).eq_num_div_denom,
  have eq_mulz := (hl hm (x * y) z).eq_num_div_denom,
  rw [hl.mul, homogeneous_localization.mul_val, eq_xz, eq_yz, mk_mul, mk_eq_mk', is_localization.eq] at eq_mulz,
  obtain ⟨⟨c, hc⟩, eq_mulz⟩ := eq_mulz,
  simp only [submonoid.coe_mul] at eq_mulz,
  simp only [← subtype.val_eq_coe] at eq_mulz,

  set d_x := (hl hm x z).denom with dx_eq,
  set n_x := (hl hm x z).num with nx_eq,
  set d_y := (hl hm y z).denom with dy_eq,
  set n_y := (hl hm y z).num with ny_eq,
  set d_xy := (hl hm (x * y) z).denom with dxy_eq,
  set n_xy := (hl hm (x * y) z).num with nxy_eq,
  set i_x := (hl hm x z).deg with ix_eq,
  set i_y := (hl hm y z).deg with iy_eq,
  set i_xy := (hl hm (x * y) z).deg with ixy_eq,

  unfold num denom,
  simp only [←dx_eq, ←nx_eq, ←dy_eq, ←ny_eq, ←dxy_eq, ←nxy_eq, ←i_x, ←i_y, ←i_xy] at eq_mulz ⊢,
  rw [localization.mk_eq_mk', is_localization.eq],

  change ¬(∀ i : ℕ, _ ∈ _) at hc,
  erw not_forall at hc,
  obtain ⟨j, hc⟩ := hc,

  use mk ((graded_algebra.proj 𝒜 j c)^m) ⟨f^j, ⟨_, rfl⟩⟩,
  simp only [submonoid.coe_mul],
  simp only [← subtype.val_eq_coe, subtype.ext_iff, subring.coe_mul, mk_mul],
  simp only [mk_eq_mk', is_localization.eq],

  use 1,
  simp only [submonoid.coe_one, submonoid.coe_mul, mul_one],
  simp only [← subtype.val_eq_coe, ← pow_add],

  suffices EQ : n_x * n_y * d_xy * graded_algebra.proj 𝒜 j c = n_xy * (d_x * d_y) * graded_algebra.proj 𝒜 j c,

  rw calc n_xy * d_xy ^ m.pred * (d_x ^ m * d_y ^ m)
          * (graded_algebra.proj 𝒜 j) c ^ m
          * f ^ (i_x + i_y + i_xy + j)
        = n_xy * d_xy ^ m.pred * (d_x ^ m * d_y ^ m)
          * (graded_algebra.proj 𝒜 j) c ^ (m.pred + 1)
          * f ^ (i_x + i_y + i_xy + j)
        : begin
          congr',
          symmetry,
          apply nat.succ_pred_eq_of_pos hm,
        end
    ... = n_xy * d_xy ^ m.pred * (d_x ^ m * d_y ^ m)
          * ((graded_algebra.proj 𝒜 j) c ^ m.pred * (graded_algebra.proj 𝒜 j) c)
          * f ^ (i_x + i_y + i_xy + j)
        : by ring_exp
    ... = n_xy * d_xy ^ m.pred * (d_x ^ (m.pred + 1) * d_y ^ (m.pred + 1))
          * ((graded_algebra.proj 𝒜 j) c ^ m.pred * (graded_algebra.proj 𝒜 j) c)
          * f ^ (i_x + i_y + i_xy + j)
        : begin
          congr',
          all_goals { symmetry, apply nat.succ_pred_eq_of_pos hm, },
        end
    ... = (n_xy * (d_x * d_y) * graded_algebra.proj 𝒜 j c) * (d_xy^m.pred * d_x^m.pred * d_y^m.pred * (graded_algebra.proj 𝒜 j c)^m.pred)
          * f ^ (i_x + i_y + i_xy + j)
        : by ring_exp
    ... = (n_x * n_y * d_xy * graded_algebra.proj 𝒜 j c) * (d_xy^m.pred * d_x^m.pred * d_y^m.pred * (graded_algebra.proj 𝒜 j c)^m.pred)
          * f ^ (i_x + i_y + i_xy + j)
        : by rw EQ
    ... = (n_x * n_y * d_xy) * (d_xy^m.pred * d_x^m.pred * d_y^m.pred * ((graded_algebra.proj 𝒜 j c)^m.pred * graded_algebra.proj 𝒜 j c))
          * f ^ (i_x + i_y + i_xy + j) : by ring
    ... = (n_x * n_y * d_xy) * (d_xy^m.pred * d_x^m.pred * d_y^m.pred * ((graded_algebra.proj 𝒜 j c)^m.pred * (graded_algebra.proj 𝒜 j c)^1))
          * f ^ (i_x + i_y + i_xy + j) : by rw pow_one
    ... = (n_x * n_y * d_xy) * (d_xy^m.pred * d_x^m.pred * d_y^m.pred * ((graded_algebra.proj 𝒜 j c)^(m.pred + 1)))
          * f ^ (i_x + i_y + i_xy + j)
        : by ring_exp
    ... = (n_x * n_y * d_xy) * (d_xy^m.pred * d_x^m.pred * d_y^m.pred * ((graded_algebra.proj 𝒜 j c)^m))
          * f ^ (i_x + i_y + i_xy + j)
        : begin
          congr',
          exact nat.succ_pred_eq_of_pos hm,
        end
    ... = (n_x * n_y) * ((d_xy^m.pred * d_xy) * d_x^m.pred * d_y^m.pred * ((graded_algebra.proj 𝒜 j c)^m))
          * f ^ (i_x + i_y + i_xy + j) : by ring
    ... = (n_x * n_y) * ((d_xy^m.pred * d_xy^1) * d_x^m.pred * d_y^m.pred * ((graded_algebra.proj 𝒜 j c)^m))
          * f ^ (i_x + i_y + i_xy + j) : by rw pow_one
    ... = (n_x * n_y) * ((d_xy^(m.pred + 1)) * d_x^m.pred * d_y^m.pred * ((graded_algebra.proj 𝒜 j c)^m))
          * f ^ (i_x + i_y + i_xy + j)
        : by ring_exp
    ... = (n_x * n_y) * (d_xy^m * d_x^m.pred * d_y^m.pred * ((graded_algebra.proj 𝒜 j c)^m))
          * f ^ (i_x + i_y + i_xy + j)
        : begin
          congr',
          exact nat.succ_pred_eq_of_pos hm,
        end,
  ring_nf,

  have INEQ : graded_algebra.proj 𝒜 j c ≠ 0,
  { intro rid,
    apply hc,
    simp only [rid, zero_pow hm, localization.mk_zero],
    exact submodule.zero_mem _, },
  replace eq_mulz := congr_arg (graded_algebra.proj 𝒜 (i_x + i_y + i_xy + j)) eq_mulz,
  rw [graded_algebra.proj_hom_mul, graded_algebra.proj_hom_mul] at eq_mulz,
  exact eq_mulz,

  have : (hl hm x z * hl hm y z).num * (d_x * d_y) ∈ 𝒜 (i_xy + (i_x + i_y)),
  { apply set_like.graded_monoid.mul_mem,
    rw [← hl.mul],
    exact (hl hm (x * y) z).num_mem,
    apply set_like.graded_monoid.mul_mem,
    exact (hl hm x z).denom_mem,
    exact (hl hm y z).denom_mem, },
  convert this using 2,
  ring,

  exact INEQ,

  apply set_like.graded_monoid.mul_mem,
  apply set_like.graded_monoid.mul_mem,
  exact (hl hm x z).num_mem,
  exact (hl hm y z).num_mem,
  rw [← hl.mul],
  exact (hl hm (x * y) z).denom_mem,

  exact INEQ,
end

namespace is_locally_quotient

variables {α : Type*} (p : α → Prop)

variable (f_deg)
def open_set (V : opens Proj.T) : opens (Spec.T (A⁰_ f_deg)) :=
⟨homeo_of_iso (Proj_iso_Spec_Top_component hm f_deg) ''
  {z | @coe (subtype _) ↥((Proj.to_LocallyRingedSpace (λ {m : ℕ}, 𝒜 m)).to_Top) _ z ∈ V.1}, begin
  have := Proj.T,
  rw [homeomorph.is_open_image, is_open_induced_iff],
  refine ⟨V.1, V.2, _⟩,
  ext z, split; intro hz,
  { rw set.mem_preimage at hz,
    exact hz, },
  { rw set.mem_preimage,
    exact hz, }
end⟩

lemma open_set_is_subset
  (V : opens Proj.T) (y : unop U)
  (subset1 : V ⟶ ((@opens.open_embedding Proj.T (pbo f)).is_open_map.functor.op.obj
            ((opens.map (Proj_iso_Spec_Top_component hm f_deg).hom).op.obj U)).unop) :
  (open_set 𝒜 hm f_deg V) ⟶ unop U := hom_of_le
begin
  have subset2 := le_of_hom subset1,
  rintros z z_mem,
  obtain ⟨z, z_mem, rfl⟩ := z_mem,
  dsimp only [set.mem_set_of] at z_mem,
  specialize subset2 z_mem,
  obtain ⟨a, a_mem, eq2⟩ := subset2,
  erw set.mem_preimage at a_mem,
  rw homeo_of_iso_apply,
  change _ ∈ (unop U).val,
  convert a_mem,
  rw subtype.ext_iff,
  rw ←eq2,
  refl,
end

lemma mem_open_subset_of_inv_mem (V : opens Proj.T) (y : unop U)
  (mem1 : (((Proj_iso_Spec_Top_component hm f_deg).inv) y.val).val ∈ V) :
  y.1 ∈ open_set 𝒜 hm f_deg V  :=
begin
  refine ⟨(Proj_iso_Spec_Top_component hm f_deg).inv y.1, mem1, _⟩,
  rw [homeo_of_iso_apply],
  convert Proj_iso_Spec_Top_component.to_Spec_from_Spec _ _ _ _,
end

/--
For b ∈ 𝒜 i
z ∈ V and b ∉ z, then b^m / f^i ∉ forward f
-/
lemma not_mem
  (V : opens Proj.T)
  -- (subset1 : V ⟶ ((@opens.open_embedding Proj.T (pbo f)).is_open_map.functor.op.obj
  --           ((opens.map (Top_component hm f_deg).hom).op.obj U)).unop)
  (b : A) (degree : ℕ) (b_mem : b ∈ 𝒜 degree)
  (z : Proj.T| (pbo f))
  (z_mem : z.1 ∈ V.1)
  (b_not_mem : b ∉ z.1.as_homogeneous_ideal) :
  (⟨localization.mk (b^m) ⟨f^degree, ⟨_, rfl⟩⟩,
    ⟨degree, ⟨_, set_like.graded_monoid.pow_mem _ b_mem⟩, rfl⟩⟩ : A⁰_ f_deg)
  ∉ ((homeo_of_iso (Proj_iso_Spec_Top_component hm f_deg)) z).as_ideal := λ rid,
begin
  classical,

  rw homeo_of_iso_apply at rid,
  erw Proj_iso_Spec_Top_component.to_Spec.mem_carrier_iff at rid,
  dsimp only at rid,

  erw [←ideal.submodule_span_eq, finsupp.span_eq_range_total, set.mem_range] at rid,
  obtain ⟨c, eq1⟩ := rid,
  erw [finsupp.total_apply, finsupp.sum] at eq1,
  dsimp only [subtype.coe_mk] at eq1,
  obtain ⟨N, hN⟩ := clear_denominator (finset.image (λ i, c i * i.1) c.support),
  -- N is the common denom
  choose after_clear_denominator hacd using hN,
  have prop1 : ∀ i, i ∈ c.support → c i * i.1 ∈ (finset.image (λ i, c i * i.1) c.support),
  { intros i hi, rw finset.mem_image, refine ⟨_, hi, rfl⟩, },
  have eq3 := calc (localization.mk (b^m) 1 : localization.away f) * localization.mk (f^N) 1
          = localization.mk (b^m) ⟨f^degree, ⟨_, rfl⟩⟩ * localization.mk (f^degree) 1 * localization.mk (f^N) 1
          : begin
            congr,
            rw [localization.mk_mul, localization.mk_eq_mk', is_localization.eq],
            use 1,
            erw [mul_one, mul_one, mul_one, mul_one, ←subtype.val_eq_coe],
          end
      ... = localization.mk (f^degree) 1 * localization.mk (b^m) ⟨f^degree, ⟨_, rfl⟩⟩ * localization.mk (f^N) 1
          : by ring
      ... = localization.mk (f^degree) 1 * localization.mk (f^N) 1 * ∑ i in c.support, c i * i.1
          : begin
            erw eq1, ring,
          end
      ... = localization.mk (f^degree) 1 * (localization.mk (f^N) 1 * ∑ i in c.support, c i * i.1) : by ring
      ... = localization.mk (f^degree) 1 * ∑ i in c.support, (localization.mk (f^N) 1) * (c i * i.1)
          : begin
            congr' 1,
            rw finset.mul_sum,
          end
      ... = localization.mk (f^degree) 1 * ∑ i in c.support.attach, (localization.mk (f^N) 1) * (c i.1 * i.1.1)
          : begin
            congr' 1,
            symmetry,
            convert finset.sum_attach,
            refl,
          end
      ... = localization.mk (f^degree) 1 * ∑ i in c.support.attach, (localization.mk (after_clear_denominator (c i.1 * i.1.1) (prop1 i.1 i.2)) 1)
          : begin
            congr' 1,
            rw finset.sum_congr rfl (λ j hj, _),
            have eq2 := (hacd (c j.1 * j.1.1) (prop1 j.1 j.2)).2,
            dsimp only at eq2,
            erw eq2,
            rw mul_comm,
          end
      ... = ∑ i in c.support.attach, (localization.mk (f^degree) 1) * (localization.mk (after_clear_denominator (c i.1 * i.1.1) (prop1 i.1 i.2)) 1)
          : begin
            rw finset.mul_sum,
          end
      ... = ∑ i in c.support.attach, localization.mk (f^degree * (after_clear_denominator (c i.1 * i.1.1) (prop1 i.1 i.2))) 1
          : begin
            rw finset.sum_congr rfl (λ j hj, _),
            erw [localization.mk_mul, one_mul],
          end
      ... = localization.mk (∑ i in c.support.attach, (f^degree * (after_clear_denominator (c i.1 * i.1.1) (prop1 i.1 i.2)))) 1
          : begin
            induction c.support.attach using finset.induction_on with y s hy ih,
            rw [finset.sum_empty, finset.sum_empty, localization.mk_zero],
            rw [finset.sum_insert hy, finset.sum_insert hy, ih, localization.add_mk, mul_one, ←subtype.val_eq_coe,
              show (1 : submonoid.powers f).1 = 1, from rfl, one_mul, one_mul, add_comm],
          end,
  erw [localization.mk_mul, one_mul] at eq3,
  simp only [localization.mk_eq_mk', is_localization.eq] at eq3,
  obtain ⟨⟨_, ⟨l, rfl⟩⟩, eq3⟩ := eq3,
  erw [mul_one, ←subtype.val_eq_coe, mul_one] at eq3,
  dsimp only at eq3,
  suffices : (∑ i in c.support.attach, (f^degree * (after_clear_denominator (c i.1 * i.1.1) (prop1 i.1 i.2)))) * f^l ∈ z.1.as_homogeneous_ideal,
  erw ←eq3 at this,
  rcases z.1.is_prime.mem_or_mem this with H1 | H3,
  rcases z.1.is_prime.mem_or_mem H1 with H1 | H2,
  { apply b_not_mem,
    rw z.1.is_prime.pow_mem_iff_mem at H1,
    exact H1,
    exact hm, },
  { have mem3 := z.2,
    have mem4 := z.1.is_prime.mem_of_pow_mem _ H2,
    erw projective_spectrum.mem_basic_open at mem3,
    apply mem3,
    exact mem4, },
  { have mem3 := z.2,
    have mem4 := z.1.is_prime.mem_of_pow_mem _ H3,
    erw projective_spectrum.mem_basic_open at mem3,
    apply mem3,
    exact mem4, },
  apply ideal.mul_mem_right,
  apply ideal.sum_mem,
  intros j hj,
  apply ideal.mul_mem_left,
  set g := classical.some j.1.2 with g_eq,
  have mem3 : g ∈ z.1.as_homogeneous_ideal := (classical.some_spec j.1.2).1,
  have eq3 : j.1.1 = localization.mk g 1 := (classical.some_spec j.1.2).2.symm,
  have eq4 := (hacd (c j.1 * j.1.1) (prop1 j.1 j.2)).2,
  dsimp only at eq4,
  have eq5 : ∃ (a : A) (zz : ℕ), c j.1 = localization.mk a ⟨f^zz, ⟨zz, rfl⟩⟩,
  { induction (c j.1) using localization.induction_on with data,
    rcases data with ⟨a, ⟨_, ⟨zz, rfl⟩⟩⟩,
    refine ⟨a, zz, rfl⟩, },
  obtain ⟨α, zz, hzz⟩ := eq5,
  have eq6 := calc localization.mk (after_clear_denominator (c j.1 * j.1.1) (prop1 j.1 j.2)) 1
          = c j.1 * j.1.1 * localization.mk (f^N) 1 : eq4
      ... = (localization.mk α ⟨f^zz, ⟨zz, rfl⟩⟩ : localization.away f) * j.1.1 * localization.mk (f^N) 1
          : by erw hzz
      ... = (localization.mk α ⟨f^zz, ⟨zz, rfl⟩⟩ : localization.away f) * localization.mk g 1 * localization.mk (f^N) 1
          : by erw eq3
      ... = localization.mk (α * g * f^N) ⟨f^zz, ⟨zz, rfl⟩⟩
          : begin
            erw [localization.mk_mul, localization.mk_mul, mul_one, mul_one],
          end,
  simp only [localization.mk_eq_mk', is_localization.eq] at eq6,
  obtain ⟨⟨_, ⟨v, rfl⟩⟩, eq6⟩ := eq6,
  erw [←subtype.val_eq_coe, ←subtype.val_eq_coe, mul_one] at eq6,
  dsimp only at eq6,
  have mem4 : α * g * f ^ N * f ^ v ∈ z.1.as_homogeneous_ideal,
  { apply ideal.mul_mem_right,
    apply ideal.mul_mem_right,
    apply ideal.mul_mem_left,
    exact mem3, },
  erw ←eq6 at mem4,
  rcases z.1.is_prime.mem_or_mem mem4 with H1 | H3,
  rcases z.1.is_prime.mem_or_mem H1 with H1 | H2,
  { exact H1 },
  { exfalso,
    have mem3 := z.2,
    have mem4 := z.1.is_prime.mem_of_pow_mem _ H2,
    erw projective_spectrum.mem_basic_open at mem3,
    apply mem3,
    exact mem4, },
  { exfalso,
    have mem3 := z.2,
    have mem4 := z.1.is_prime.mem_of_pow_mem _ H3,
    erw projective_spectrum.mem_basic_open at mem3,
    apply mem3,
    exact mem4, },
end

include hm
lemma mk_proj_pow_not_mem
  (V : opens (projective_spectrum.Top 𝒜))
  (z : Proj .restrict (@opens.open_embedding (projective_spectrum.Top 𝒜)
    (projective_spectrum.basic_open 𝒜 f)))
  (C : A) (j : ℕ) (hj : graded_algebra.proj 𝒜 j C ∉ z.1.as_homogeneous_ideal) :
  (localization.mk ((graded_algebra.proj 𝒜 j) C ^ m) ⟨f ^ j, ⟨j, rfl⟩⟩ : localization.away f) ∉
    ideal.span ((algebra_map A (away f)) '' ↑(projective_spectrum.as_homogeneous_ideal z.val)) :=
begin
  haveI : decidable_eq (away f) := classical.dec_eq _,

  intro rid,
  erw [←ideal.submodule_span_eq, finsupp.span_eq_range_total, set.mem_range] at rid,
  obtain ⟨c, eq1⟩ := rid,
  erw [finsupp.total_apply, finsupp.sum] at eq1,
  obtain ⟨N, hN⟩ := clear_denominator (finset.image (λ i, c i * i.1) c.support),
  -- N is the common denom
  choose after_clear_denominator hacd using hN,
  have prop1 : ∀ i, i ∈ c.support → c i * i.1 ∈ (finset.image (λ i, c i * i.1) c.support),
  { intros i hi, rw finset.mem_image, refine ⟨_, hi, rfl⟩, },
  have eq3 := calc (localization.mk ((graded_algebra.proj 𝒜 j) C ^ m) 1 : localization.away f) * localization.mk (f^N) 1
          = localization.mk ((graded_algebra.proj 𝒜 j) C ^ m) ⟨f^j, ⟨_, rfl⟩⟩ * localization.mk (f^j) 1 * localization.mk (f^N) 1
          : begin
            congr,
            rw [localization.mk_mul, localization.mk_eq_mk', is_localization.eq],
            use 1,
            erw [mul_one, mul_one, mul_one, mul_one, ←subtype.val_eq_coe],
          end
      ... = localization.mk (f^j) 1 * localization.mk ((graded_algebra.proj 𝒜 j) C ^ m) ⟨f^j, ⟨_, rfl⟩⟩ * localization.mk (f^N) 1
          : by ring
      ... = localization.mk (f^j) 1 * localization.mk (f^N) 1 * ∑ i in c.support, c i * i.1
          : begin
            erw eq1, ring,
          end
      ... = localization.mk (f^j) 1 * (localization.mk (f^N) 1 * ∑ i in c.support, c i * i.1) : by ring
      ... = localization.mk (f^j) 1 * ∑ i in c.support, (localization.mk (f^N) 1) * (c i * i.1)
          : begin
            congr' 1,
            rw finset.mul_sum,
          end
      ... = localization.mk (f^j) 1 * ∑ i in c.support.attach, (localization.mk (f^N) 1) * (c i.1 * i.1.1)
          : begin
            congr' 1,
            symmetry,
            convert finset.sum_attach,
            refl,
          end
      ... = localization.mk (f^j) 1 * ∑ i in c.support.attach, (localization.mk (after_clear_denominator (c i.1 * i.1.1) (prop1 i.1 i.2)) 1)
          : begin
            congr' 1,
            rw finset.sum_congr rfl (λ j hj, _),
            have eq2' := (hacd (c j.1 * j.1.1) (prop1 j.1 j.2)).2,
            dsimp only at eq2',
            erw eq2',
            rw mul_comm,
          end
      ... = ∑ i in c.support.attach, (localization.mk (f^j) 1) * (localization.mk (after_clear_denominator (c i.1 * i.1.1) (prop1 i.1 i.2)) 1)
          : begin
            rw finset.mul_sum,
          end
      ... = ∑ i in c.support.attach, localization.mk (f^j * (after_clear_denominator (c i.1 * i.1.1) (prop1 i.1 i.2))) 1
          : begin
            rw finset.sum_congr rfl (λ j hj, _),
            erw [localization.mk_mul, one_mul],
          end
      ... = localization.mk (∑ i in c.support.attach, (f^j * (after_clear_denominator (c i.1 * i.1.1) (prop1 i.1 i.2)))) 1
          : begin
            induction c.support.attach using finset.induction_on with y s hy ih,
            rw [finset.sum_empty, finset.sum_empty, localization.mk_zero],
            erw [finset.sum_insert hy, finset.sum_insert hy, ih, localization.add_mk, mul_one, one_mul, one_mul, add_comm],
          end,
  erw [localization.mk_mul, one_mul] at eq3,
  simp only [localization.mk_eq_mk', is_localization.eq] at eq3,
  obtain ⟨⟨_, ⟨l, rfl⟩⟩, eq3⟩ := eq3,
  erw [mul_one, ←subtype.val_eq_coe, mul_one] at eq3,
  dsimp only at eq3,
  suffices : (∑ i in c.support.attach, (f^j * (after_clear_denominator (c i.1 * i.1.1) (prop1 i.1 i.2)))) * f^l ∈ z.1.as_homogeneous_ideal,
  erw ←eq3 at this,
  rcases z.1.is_prime.mem_or_mem this with H1 | H3,
  rcases z.1.is_prime.mem_or_mem H1 with H1 | H2,
  { apply hj,
    rw z.1.is_prime.pow_mem_iff_mem at H1,
    exact H1,
    exact hm, },
  { have mem3 := z.2,
    have mem4 := z.1.is_prime.mem_of_pow_mem _ H2,
    erw projective_spectrum.mem_basic_open at mem3,
    apply mem3,
    exact mem4, },
  { have mem3 := z.2,
    have mem4 := z.1.is_prime.mem_of_pow_mem _ H3,
    erw projective_spectrum.mem_basic_open at mem3,
    apply mem3,
    exact mem4, },
  apply ideal.mul_mem_right,
  apply ideal.sum_mem,
  intros j hj,
  apply ideal.mul_mem_left,
  set g := classical.some j.1.2 with g_eq,
  have mem3 : g ∈ z.1.as_homogeneous_ideal := (classical.some_spec j.1.2).1,
  have eq3 : j.1.1 = localization.mk g 1 := (classical.some_spec j.1.2).2.symm,
  have eq4 := (hacd (c j.1 * j.1.1) (prop1 j.1 j.2)).2,
  dsimp only at eq4,

  have eq5 : ∃ (a : A) (zz : ℕ), c j.1 = localization.mk a ⟨f^zz, ⟨zz, rfl⟩⟩,
  { induction (c j.1) using localization.induction_on with data,
    rcases data with ⟨a, ⟨_, ⟨zz, rfl⟩⟩⟩,
    refine ⟨a, zz, rfl⟩, },
  obtain ⟨α, zz, hzz⟩ := eq5,

  have eq6 := calc localization.mk (after_clear_denominator (c j.1 * j.1.1) (prop1 j.1 j.2)) 1
          = c j.1 * j.1.1 * localization.mk (f^N) 1 : eq4
      ... = (localization.mk α ⟨f^zz, ⟨zz, rfl⟩⟩ : localization.away f) * j.1.1 * localization.mk (f^N) 1
          : by erw hzz
      ... = (localization.mk α ⟨f^zz, ⟨zz, rfl⟩⟩ : localization.away f) * localization.mk g 1 * localization.mk (f^N) 1
          : by erw eq3
      ... = localization.mk (α * g * f^N) ⟨f^zz, ⟨zz, rfl⟩⟩
          : begin
            erw [localization.mk_mul, localization.mk_mul, mul_one, mul_one],
          end,
  simp only [localization.mk_eq_mk', is_localization.eq] at eq6,
  obtain ⟨⟨_, ⟨v, rfl⟩⟩, eq6⟩ := eq6,
  erw [←subtype.val_eq_coe, ←subtype.val_eq_coe, mul_one] at eq6,
  dsimp only at eq6,

  have mem4 : α * g * f ^ N * f ^ v ∈ z.1.as_homogeneous_ideal,
  { apply ideal.mul_mem_right,
    apply ideal.mul_mem_right,
    apply ideal.mul_mem_left,
    exact mem3, },
  erw ←eq6 at mem4,

  rcases z.1.is_prime.mem_or_mem mem4 with H1 | H3,
  rcases z.1.is_prime.mem_or_mem H1 with H1 | H2,
  { exact H1 },
  { exfalso,
    have mem3 := z.2,
    have mem4 := z.1.is_prime.mem_of_pow_mem _ H2,
    erw projective_spectrum.mem_basic_open at mem3,
    apply mem3,
    exact mem4, },
  { exfalso,
    have mem3 := z.2,
    have mem4 := z.1.is_prime.mem_of_pow_mem _ H3,
    erw projective_spectrum.mem_basic_open at mem3,
    apply mem3,
    exact mem4, }
end

omit hm
lemma final_eq
  (d_hh n_hh a b C : A) (degree i_hh j : ℕ) (INEQ : graded_algebra.proj 𝒜 j C ≠ 0)
  (d_hh_mem : d_hh ∈ 𝒜 i_hh) (n_hh_mem : n_hh ∈ 𝒜 i_hh)
  (a_hom : a ∈ 𝒜 degree) (b_hom : b ∈ 𝒜 degree)
  (eq1 : n_hh * b * C = a * d_hh * C) : n_hh * b * graded_algebra.proj 𝒜 j C = a * d_hh * graded_algebra.proj 𝒜 j C :=
begin
  have eq2 := congr_arg (graded_algebra.proj 𝒜 (i_hh + degree + j)) eq1,
  rw [graded_algebra.proj_hom_mul, graded_algebra.proj_hom_mul] at eq2,
  exact eq2,

  rw add_comm,
  apply set_like.graded_monoid.mul_mem,
  exact a_hom,
  exact d_hh_mem,
  exact INEQ,

  apply set_like.graded_monoid.mul_mem,
  exact n_hh_mem,
  exact b_hom,
  exact INEQ,
end

lemma inv_hom_mem_bo (V : opens Proj.T) (z : Proj.T| (pbo f))
  (subset2 : open_set 𝒜 hm f_deg V ⟶ unop U) (z_mem : z.1 ∈ V) :
  (((Proj_iso_Spec_Top_component hm f_deg).inv)
    (subset2 ⟨(homeo_of_iso (Proj_iso_Spec_Top_component hm f_deg)) z, begin
    erw [set.mem_preimage],
    refine ⟨z, z_mem, rfl⟩,
  end⟩).val).val ∈ projective_spectrum.basic_open 𝒜 f :=
begin
  erw projective_spectrum.mem_basic_open,
  intro rid,
  change ∀ _, _ at rid,
  specialize rid m,
  simp only [graded_algebra.proj_apply, direct_sum.decompose_of_mem_same 𝒜 f_deg] at rid,
  change _ ∈ ((homeo_of_iso (Proj_iso_Spec_Top_component hm f_deg)) z).1 at rid,
  have rid2 : (1 : A⁰_ f_deg) ∈ ((homeo_of_iso (Proj_iso_Spec_Top_component hm f_deg)) z).1,
  { convert rid,
    rw subtype.ext_iff,
    dsimp only [subtype.coe_mk],
    erw localization.mk_self (⟨f^m, ⟨_, rfl⟩⟩ : submonoid.powers f),
    refl, },
  rw homeo_of_iso_apply at rid2,
  apply (((Proj_iso_Spec_Top_component hm f_deg).hom) z).is_prime.1,
  rw ideal.eq_top_iff_one,
  exact rid2,
end

lemma inv_hom_mem2
  (V : opens Proj.T)
  (z : Proj.T| (pbo f))
  (subset2 : open_set 𝒜 hm f_deg V ⟶ unop U)
  (z_mem : z.1 ∈ V) :
  (((Proj_iso_Spec_Top_component hm f_deg).inv)
    (subset2 ⟨(homeo_of_iso (Proj_iso_Spec_Top_component hm f_deg)) z, begin
    erw [set.mem_preimage],
    refine ⟨z, z_mem, rfl⟩,
  end⟩).val).val ∈
  ((@opens.open_embedding (projective_spectrum.Top 𝒜) (projective_spectrum.basic_open 𝒜 f)).is_open_map.functor.op.obj
    ((opens.map (Proj_iso_Spec_Top_component hm f_deg).hom).op.obj U)).unop :=
begin
  simp only [unop_op, functor.op_obj],
  set z' := (((Proj_iso_Spec_Top_component hm f_deg).inv)
    (subset2 ⟨(homeo_of_iso (Proj_iso_Spec_Top_component hm f_deg)) z, begin
    erw [set.mem_preimage],
    refine ⟨z, z_mem, rfl⟩,
  end⟩).val).val with z'_eq,
  refine ⟨⟨z', _⟩, _, rfl⟩,
  have mem_z' : z' ∈ projective_spectrum.basic_open 𝒜 f,
  erw projective_spectrum.mem_basic_open,
  intro rid,
  erw z'_eq at rid,
  change ∀ _, _ at rid,
  specialize rid m,
  simp only [graded_algebra.proj_apply, direct_sum.decompose_of_mem_same 𝒜 f_deg] at rid,
  change _ ∈ ((homeo_of_iso (Proj_iso_Spec_Top_component hm f_deg)) z).1 at rid,
  have rid2 : (1 : A⁰_ f_deg) ∈ ((homeo_of_iso (Proj_iso_Spec_Top_component hm f_deg)) z).1,
  { convert rid,
    rw subtype.ext_iff,
    dsimp only [subtype.coe_mk],
    erw localization.mk_self (⟨f^m, ⟨_, rfl⟩⟩ : submonoid.powers f),
    refl, },
  rw homeo_of_iso_apply at rid2,
  apply (((Proj_iso_Spec_Top_component hm f_deg).hom) z).is_prime.1,
  rw ideal.eq_top_iff_one,
  exact rid2,
  exact mem_z',
  erw [set.mem_preimage],
  have subset3 := le_of_hom subset2,
  suffices : ((Proj_iso_Spec_Top_component hm f_deg).hom) ⟨z', _⟩ ∈ open_set 𝒜 hm f_deg V,
  apply subset3,
  exact this,

  refine ⟨z, z_mem, _⟩,
  simp only [homeo_of_iso_apply],
  congr',
  rw subtype.ext_iff,
  dsimp only [subtype.coe_mk],
  rw z'_eq,
  change z.1 = (Proj_iso_Spec_Top_component.from_Spec hm f_deg (Proj_iso_Spec_Top_component.to_Spec _ _ _)).1,
  congr',
  symmetry,
  apply Proj_iso_Spec_Top_component.from_Spec_to_Spec 𝒜 hm f_deg z,
end

end is_locally_quotient

variables (hm f_deg)
lemma fmk_is_locally_quotient (y : unop U) :
  ∃ (V : opens (Spec.T (A⁰_ f_deg))) (mem : y.val ∈ V) (i : V ⟶ unop U) (r s : (A⁰_ f_deg)),
    ∀ (z : V),
      ∃ (s_not_mem : s ∉ prime_spectrum.as_ideal z.val),
        fmk hm hh ⟨(i z).1, (i z).2⟩ = mk r ⟨s, s_not_mem⟩ :=
begin
  classical,

  obtain ⟨V, mem1, subset1, degree, ⟨a, a_mem⟩, ⟨b, b_mem⟩, eq1⟩ := hh.2 ⟨((Proj_iso_Spec_Top_component hm f_deg).inv y.1).1, inv_mem y⟩,
  set VVo : opens (Spec.T (A⁰_ f_deg)) := is_locally_quotient.open_set 𝒜 hm f_deg V with VVo_eq,
  have subset2 : VVo ⟶ unop U := is_locally_quotient.open_set_is_subset 𝒜 hm f_deg V y subset1,
  have y_mem1 : y.1 ∈ VVo,
  { convert is_locally_quotient.mem_open_subset_of_inv_mem 𝒜 hm f_deg V y mem1 },
  refine ⟨VVo, y_mem1, subset2,
    ⟨localization.mk (a * b^m.pred) ⟨f^degree, ⟨_, rfl⟩⟩, ⟨degree, ⟨_, begin
      have mem1 : b^m.pred ∈ 𝒜 (m.pred * degree) := set_like.graded_monoid.pow_mem _ b_mem,
      have mem2 := set_like.graded_monoid.mul_mem a_mem mem1,
      convert mem2,
      exact calc m * degree
              = (m.pred + 1) * degree
              : begin
                congr' 1,
                symmetry,
                apply nat.succ_pred_eq_of_pos hm,
              end
          ... = m.pred * degree + 1 * degree : by rw add_mul
          ... = m.pred * degree + degree : by rw one_mul
          ... = degree + m.pred * degree : by rw add_comm,
    end⟩, rfl⟩⟩,
    ⟨localization.mk (b^m) ⟨f^degree, ⟨_, rfl⟩⟩, ⟨degree, ⟨_, set_like.graded_monoid.pow_mem _ b_mem⟩, rfl⟩⟩, _⟩,

  rintros ⟨z, z_mem⟩,
  obtain ⟨z, z_mem, rfl⟩ := z_mem,
  specialize eq1 ⟨z.1, z_mem⟩,
  obtain ⟨b_not_mem, eq1⟩ := eq1,

  refine ⟨is_locally_quotient.not_mem 𝒜 hm f_deg V b degree b_mem z z_mem b_not_mem, _⟩,

  have eq2 := (hh.val (subset1 ⟨z.val, z_mem⟩)).eq_num_div_denom,
  dsimp only at eq1,
  rw [homogeneous_localization.ext_iff_val] at eq1,
  rw [eq2, homogeneous_localization.val_mk'] at eq1,
  simp only [← subtype.val_eq_coe] at eq1,
  rw [localization.mk_eq_mk', is_localization.eq] at eq1,
  obtain ⟨⟨C, hC⟩, eq1⟩ := eq1,
  unfold fmk,
  rw [localization.mk_eq_mk', is_localization.eq],
  simp only [←subtype.val_eq_coe] at eq1,
  set degree_hh := (hh.val (subset1 ⟨z.val, z_mem⟩)).deg with degree_hh_eq,
  have mem_C : ∃ (j : ℕ), graded_algebra.proj 𝒜 j C ∉ z.1.as_homogeneous_ideal,
  { by_contra rid,
    rw not_exists at rid,
    apply hC,
    rw ←direct_sum.sum_support_decompose 𝒜 C,
    apply ideal.sum_mem,
    intros j hj,
    specialize rid j,
    rw not_not at rid,
    apply rid, },
  obtain ⟨j, hj⟩ := mem_C,
  refine ⟨⟨⟨localization.mk ((graded_algebra.proj 𝒜 j C)^m) ⟨f^j, ⟨_, rfl⟩⟩,
    ⟨j, ⟨(graded_algebra.proj 𝒜 j C)^m, set_like.graded_monoid.pow_mem _ (submodule.coe_mem _)⟩, rfl⟩⟩, _⟩, _⟩,
  { change _ ∉ _,
    simp only [← subtype.val_eq_coe],
    erw Proj_iso_Spec_Top_component.to_Spec.mem_carrier_iff,
    apply is_locally_quotient.mk_proj_pow_not_mem hm V z C j hj, },

  set z' := (((Proj_iso_Spec_Top_component hm f_deg).inv)
    (subset2 ⟨(homeo_of_iso (Proj_iso_Spec_Top_component hm f_deg)) z, begin
    erw [set.mem_preimage],
    refine ⟨z, z_mem, rfl⟩,
  end⟩).val).val with z'_eq,

  have z'_mem : z' ∈ (((@opens.open_embedding Proj.T) (pbo f)).is_open_map.functor.op.obj
        ((opens.map (Proj_iso_Spec_Top_component hm f_deg).hom).op.obj U)).unop,
  { convert is_locally_quotient.inv_hom_mem2 𝒜 hm f_deg V z subset2 z_mem },

  have eq_pt : (subset1 ⟨z.1, z_mem⟩) = ⟨z', z'_mem⟩,
  { rw subtype.ext_iff,
    change z.1 = (Proj_iso_Spec_Top_component.from_Spec hm f_deg (Proj_iso_Spec_Top_component.to_Spec m f_deg _)).1,
    congr',
    symmetry,
    apply Proj_iso_Spec_Top_component.from_Spec_to_Spec 𝒜 hm f_deg z, },
  erw [eq_pt] at eq1,

  unfold num denom,
  simp only [←subtype.val_eq_coe, subtype.ext_iff, subring.coe_mul, localization.mk_mul],
  rw [localization.mk_eq_mk', is_localization.eq],
  use 1,
  simp only [submonoid.coe_mul, submonoid.coe_one],
  simp only [←subtype.val_eq_coe, one_mul, mul_one, ←pow_add],

  set d_hh := (hh.val ⟨z', z'_mem⟩).denom with d_hh_eq,
  set n_hh := (hh.val ⟨z', z'_mem⟩).num with n_hh_eq,
  set i_hh := (hh.val ⟨z', z'_mem⟩).deg with i_hh_eq,
  simp only [←d_hh_eq, ←n_hh_eq, ←i_hh_eq] at eq1,

  suffices : n_hh * d_hh ^ m.pred * b ^ m * (graded_algebra.proj 𝒜 j) C ^ m * f ^ (degree + i_hh + j)
    = a * b ^ m.pred * d_hh ^ m * (graded_algebra.proj 𝒜 j) C ^ m * f ^ (i_hh + degree + j),
  convert this,

  suffices EQ : n_hh * b * graded_algebra.proj 𝒜 j C = a * d_hh * graded_algebra.proj 𝒜 j C,
  erw calc n_hh * d_hh ^ m.pred * b ^ m * (graded_algebra.proj 𝒜 j) C ^ m * f ^ (degree + i_hh + j)
        = n_hh * d_hh ^ m.pred * b ^ (m.pred + 1) * (graded_algebra.proj 𝒜 j) C^(m.pred + 1) * f^(degree + i_hh + j)
        : begin
          congr';
          symmetry;
          apply nat.succ_pred_eq_of_pos hm,
        end
    ... = n_hh * d_hh ^ m.pred * (b ^ m.pred * b) * ((graded_algebra.proj 𝒜 j C) ^ m.pred * (graded_algebra.proj 𝒜 j C)) * f^(degree + i_hh + j)
        : begin
          congr',
          all_goals { rw [pow_add, pow_one], },
        end
    ... = (n_hh * b * graded_algebra.proj 𝒜 j C) * (d_hh ^ m.pred * b ^ m.pred * (graded_algebra.proj 𝒜 j C)^m.pred) * f^(degree + i_hh + j)  : by ring
    ... = (a * d_hh * graded_algebra.proj 𝒜 j C) * (d_hh ^ m.pred * b ^ m.pred * (graded_algebra.proj 𝒜 j C)^m.pred) * f^(degree + i_hh + j)  : by rw EQ
    ... = a * b ^ m.pred * (d_hh ^ m.pred * d_hh) * ((graded_algebra.proj 𝒜 j C)^m.pred * graded_algebra.proj 𝒜 j C) * f^(degree + i_hh + j)  : by ring
    ... = a * b ^ m.pred * (d_hh ^ m.pred * d_hh^1) * ((graded_algebra.proj 𝒜 j C)^m.pred * graded_algebra.proj 𝒜 j C ^ 1) * f^(degree + i_hh + j)
        : by rw [pow_one, pow_one]
    ... =  a * b ^ m.pred * (d_hh ^ (m.pred + 1)) * ((graded_algebra.proj 𝒜 j C)^(m.pred + 1)) * f^(degree + i_hh + j)
        : by simp only [pow_add]
    ... = a * b ^ m.pred * d_hh ^ m * (graded_algebra.proj 𝒜 j C)^m * f^(degree + i_hh + j)
        : begin
          congr',
          all_goals { apply nat.succ_pred_eq_of_pos hm, },
        end
    ... = a * b ^ m.pred * d_hh ^ m * (graded_algebra.proj 𝒜 j C)^m * f^(i_hh + degree + j)
        : begin
          congr' 1,
          rw add_comm i_hh degree,
        end,
  have INEQ : graded_algebra.proj 𝒜 j C ≠ 0,
  { intro rid,
    apply hj,
    rw rid,
    exact submodule.zero_mem _, },

  have eq2 := congr_arg (graded_algebra.proj 𝒜 (i_hh + degree + j)) eq1,
  rw [graded_algebra.proj_hom_mul, graded_algebra.proj_hom_mul] at eq2,
  exact eq2,

  rw add_comm,
  apply set_like.graded_monoid.mul_mem,
  exact a_mem,
  exact (hh.val ⟨z', z'_mem⟩).denom_mem,
  exact INEQ,

  apply set_like.graded_monoid.mul_mem,
  exact (hh.val ⟨z', z'_mem⟩).num_mem,
  exact b_mem,
  exact INEQ,
end

variable (U)
def to_fun : (pf_sheaf (Proj| (pbo f))).obj U ⟶ (Spec (A⁰_ f_deg)).presheaf.obj U :=
{ to_fun := λ hh, ⟨λ y, fmk hm hh y, begin
    rw algebraic_geometry.structure_sheaf.is_locally_fraction_pred',
    exact fmk_is_locally_quotient hm f_deg hh,
  end⟩,
  map_one' := begin
    rw subtype.ext_iff,
    dsimp only [subtype.coe_mk],
    ext y,
    rw [fmk.one hm],
    convert pi.one_apply _,
  end,
  map_mul' := λ x y, begin
    rw subtype.ext_iff,
    dsimp only [subtype.coe_mk],
    ext z,
    rw [fmk.mul hm],
    change _ * _ = _ * _,
    dsimp only,
    refl,
  end,
  map_zero' := begin
    rw subtype.ext_iff,
    dsimp only [subtype.coe_mk],
    ext y,
    rw [fmk.zero hm],
    convert pi.zero_apply _,
  end,
  map_add' := λ x y, begin
    rw subtype.ext_iff,
    dsimp only [subtype.coe_mk],
    ext z,
    rw [fmk.add hm],
    change _ + _ = fmk hm x z + fmk hm y z,
    dsimp only,
    refl
  end }

end to_Spec

section

def to_Spec {f : A} {m : ℕ} (hm : 0 < m) (f_deg : f ∈ 𝒜 m):
  ((Proj_iso_Spec_Top_component hm f_deg).hom _* (Proj| (pbo f)).presheaf) ⟶ (Spec (A⁰_ f_deg)).presheaf :=
{ app := λ U, to_Spec.to_fun hm f_deg U,
  naturality' := λ U V subset1, begin
    ext1 z,
    simp only [comp_apply, ring_hom.coe_mk, functor.op_map, presheaf.pushforward_obj_map],
    refl,
  end }

end

end Proj_iso_Spec_Sheaf_component

end algebraic_geometry