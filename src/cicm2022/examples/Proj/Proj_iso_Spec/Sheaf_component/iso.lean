import cicm2022.examples.Proj.degree_zero_part
import cicm2022.examples.Proj.structure_sheaf
import cicm2022.examples.Proj.lemmas
import cicm2022.examples.Proj.Proj_iso_Spec.Sheaf_component.from_Spec
import cicm2022.examples.Proj.Proj_iso_Spec.Sheaf_component.to_Spec


import algebraic_geometry.structure_sheaf
import algebraic_geometry.Spec

noncomputable theory

namespace algebraic_geometry

open_locale direct_sum big_operators pointwise big_operators
open direct_sum set_like.graded_monoid localization finset (hiding mk_zero)

variables {R A : Type*}
variables [comm_ring R] [comm_ring A] [algebra R A]

variables (๐ : โ โ submodule R A)
variables [graded_algebra ๐]

open Top topological_space
open category_theory opposite
open projective_spectrum.structure_sheaf

local notation `Proj` := Proj.to_LocallyRingedSpace ๐
-- `Proj` as a locally ringed space
local notation `Proj.T` := Proj .1.1.1
-- the underlying topological space of `Proj`
local notation `Proj| ` U := Proj .restrict (opens.open_embedding (U : opens Proj.T))
-- `Proj` restrict to some open set
local notation `Proj.T| ` U :=
  (Proj .restrict (opens.open_embedding (U : opens Proj.T))).to_SheafedSpace.to_PresheafedSpace.1
-- the underlying topological space of `Proj` restricted to some open set
local notation `pbo` x := projective_spectrum.basic_open ๐ x
-- basic open sets in `Proj`
local notation `sbo` f := prime_spectrum.basic_open f
-- basic open sets in `Spec`
local notation `Spec` ring := Spec.LocallyRingedSpace_obj (CommRing.of ring)
-- `Spec` as a locally ringed space
local notation `Spec.T` ring :=
  (Spec.LocallyRingedSpace_obj (CommRing.of ring)).to_SheafedSpace.to_PresheafedSpace.1
-- the underlying topological space of `Spec`
local notation `Aโฐ_` f_deg := degree_zero_part f_deg

namespace Proj_iso_Spec_Sheaf_component

namespace from_Spec_to_Spec

variables {๐} {m : โ} {f : A} (hm : 0 < m) (f_deg : f โ ๐ m) (V : (opens (Spec.T (Aโฐ_ f_deg)))แตแต)
variables (hh : ((Proj_iso_Spec_Top_component hm f_deg).hom _* (Proj| (pbo f)).presheaf).obj V)
variables (z : (((@opens.open_embedding Proj.T (pbo f)).is_open_map.functor.op.obj ((opens.map (Proj_iso_Spec_Top_component hm f_deg).hom).op.obj V)).unop))

lemma section_congr
  (hh : ((Spec (Aโฐ_ f_deg)).presheaf).obj V) (x y : unop V) (h1 : x = y)
  (a : _) (b : x.1.as_ideal.prime_compl)
  (h2 : (hh.1 x) = localization.mk a b) : (hh.1 y) = localization.mk a โจb.1, begin
    intro rid,
    apply b.2,
    simp only [h1],
    exact rid
  endโฉ :=
begin
  induction h1,
  convert h2,
  rw subtype.ext_iff_val,
end

lemma inv_hom_apply_eq :
  ((Proj_iso_Spec_Top_component hm f_deg).inv ((Proj_iso_Spec_Top_component hm f_deg).hom โจz.1, from_Spec.data_prop1 hm f_deg _ _โฉ)).1 = z.1 :=
begin
  change (Proj_iso_Spec_Top_component.from_Spec.to_fun f_deg hm (Proj_iso_Spec_Top_component.to_Spec.to_fun ๐ f_deg _)).1 = z.1,
  rw Proj_iso_Spec_Top_component.from_Spec_to_Spec,
end

lemma pt_eq :
  z = โจ((Proj_iso_Spec_Top_component hm f_deg).inv ((Proj_iso_Spec_Top_component hm f_deg).hom โจz.1, from_Spec.data_prop1 hm f_deg _ _โฉ)).1, begin
    simpa only [inv_hom_apply_eq hm f_deg V z] using z.2,
  endโฉ :=
begin
  rw [subtype.ext_iff_val, inv_hom_apply_eq],
end

lemma C_not_mem (C : A) (L1 : โ) (C_mem : C โ ๐ (m * L1))
  (hC : (โจlocalization.mk C โจf ^ L1, โจ_, rflโฉโฉ, โจL1, โจ_, C_memโฉ, rflโฉโฉ : Aโฐ_ f_deg) โ 
    ((Proj_iso_Spec_Top_component hm f_deg).hom โจz.1, from_Spec.data_prop1 hm f_deg V _โฉ).as_ideal) :
  C โ z.1.as_homogeneous_ideal :=
begin
  intro rid,
  have eq1 : (localization.mk C โจf ^ L1, โจ_, rflโฉโฉ : localization.away f) =
    (localization.mk 1 โจf^L1, โจ_, rflโฉโฉ : localization.away f) * localization.mk C 1,
    rw [localization.mk_mul, one_mul, mul_one],
  simp only [eq1] at hC,
  apply hC,
  erw Proj_iso_Spec_Top_component.to_Spec.mem_carrier_iff,
  dsimp only,
  convert ideal.mul_mem_left _ _ _,
  apply ideal.subset_span,
  refine โจC, rid, rflโฉ,
end 

lemma C_not_mem2
  (C : A) (ฮน L1 L2 : โ) (C_mem : C โ ๐ (m * L1))
  (hC : (โจlocalization.mk C โจf ^ L1, โจ_, rflโฉโฉ, โจL1, โจ_, C_memโฉ, rflโฉโฉ : Aโฐ_ f_deg) โ 
    ((Proj_iso_Spec_Top_component hm f_deg).hom โจz.1, from_Spec.data_prop1 hm f_deg V _โฉ).as_ideal)
  (ฮฒ : A) 
  (ฮฒ_not_in : ฮฒ โ (((Proj_iso_Spec_Top_component hm f_deg).inv)
      ((Proj_iso_Spec_Top_component hm f_deg).hom โจz.1, from_Spec.data_prop1 hm f_deg V _โฉ)).1.as_homogeneous_ideal) :
  C * ฮฒ^m.pred * f^(ฮน+L1+L2) โ z.1.as_homogeneous_ideal :=
begin
  intro rid,
  rcases z.1.is_prime.mem_or_mem rid with H1 | H3,
  rcases z.1.is_prime.mem_or_mem H1 with H1 | H2,
  apply C_not_mem hm f_deg,
  exact hC,
  exact H1,
  replace H2 := z.1.is_prime.mem_of_pow_mem _ H2,
  apply ฮฒ_not_in,
  have eq1 : (((Proj_iso_Spec_Top_component hm f_deg).inv) ((Proj_iso_Spec_Top_component hm f_deg).hom โจz.1, from_Spec.data_prop1 hm f_deg V _โฉ)).1 = z.1,
  { change (Proj_iso_Spec_Top_component.from_Spec.to_fun f_deg hm (Proj_iso_Spec_Top_component.to_Spec.to_fun ๐ _ _)).1 = z.1,
    rw Proj_iso_Spec_Top_component.from_Spec_to_Spec, },
  erw eq1,
  exact H2,
  replace H3 := z.1.is_prime.mem_of_pow_mem _ H3,
  have mem2 := z.2,
  obtain โจโจa, haโฉ, ha2, ha3โฉ := mem2,
  change a = z.1 at ha3,
  apply ha,
  rw ha3,
  exact H3,
end

include hm
lemma final_eq
  (a ฮฑ ฮฒ b C : A) (ฮน ii jj L1 L2 : โ)
  (data_eq2 : ฮฑ * ฮฒ ^ m.pred * b * C * f ^ (ii + ฮน + L1) * f ^ L2 = a * ฮฒ ^ m * C * f ^ (ฮน + jj + L1) * f ^ L2) :
  a * f ^ jj * ฮฒ * (C * ฮฒ ^ m.pred * f ^ (ฮน + L1 + L2)) = ฮฑ * (b * f ^ ii) * (C * ฮฒ ^ m.pred * f ^ (ฮน + L1 + L2)) :=
begin
  symmetry,
  rw calc ฮฑ * (b * f ^ ii) * (C * ฮฒ ^ m.pred * f ^ (ฮน + L1 + L2))
        = ฮฑ * ฮฒ ^ m.pred * b * C * (f^ii * f^(ฮน + L1 + L2)) : by ring
    ... = ฮฑ * ฮฒ ^ m.pred * b * C * (f^ii * (f^ฮน * f^L1 * f^L2)) : by simp only [pow_add]
    ... = ฮฑ * ฮฒ ^ m.pred * b * C * (f ^ ii * f^ฮน * f^L1) * f ^ L2 : by ring
    ... = ฮฑ * ฮฒ ^ m.pred * b * C * (f ^ (ii + ฮน + L1)) * f ^ L2 : by simp only [pow_add]
    ... = a * ฮฒ ^ m * C * f ^ (ฮน + jj + L1) * f ^ L2 : by rw data_eq2
    ... = a * ฮฒ ^ (m.pred + 1) * C * f ^ (ฮน + jj + L1) * f ^ L2
        : begin
          congr',
          symmetry,
          apply nat.succ_pred_eq_of_pos hm,
        end,
  simp only [pow_add, pow_one],
  ring,
end

section

omit hm
lemma _root_.algebraic_geometry.Proj_iso_Spec_Sheaf_component.from_Spec_to_Spec :
  from_Spec.bmk hm f_deg V
    (((to_Spec ๐ hm f_deg).app V) hh) z = hh.1 z :=
begin
  unfold from_Spec.bmk,
  rw [homogeneous_localization.ext_iff_val, homogeneous_localization.val_mk'],
  simp only [โ subtype.val_eq_coe],

  set hom_z := (Proj_iso_Spec_Top_component hm f_deg).hom โจz.1, from_Spec.data_prop1 hm f_deg V _โฉ with hom_z_eq,
  have hom_z_mem_V : hom_z โ unop V,
  { apply from_Spec.data_prop2 hm f_deg V _, },

  set data := from_Spec.data hm f_deg (((to_Spec ๐ hm f_deg).app V) hh) z with data_eq,
  have data_eq1 := data_eq,
  replace data_eq1 : data = to_Spec.fmk hm hh โจhom_z, hom_z_mem_Vโฉ,
  { convert data_eq1, },
  unfold to_Spec.fmk to_Spec.num to_Spec.denom at data_eq1,

  have data_eq2 := from_Spec.data.eq_num_div_denom hm f_deg (((to_Spec ๐ hm f_deg).app V) hh) z,
  rw [โdata_eq, data_eq1] at data_eq2,
  set ฮฑ := (hh.1 โจ((Proj_iso_Spec_Top_component hm f_deg).inv hom_z).1, to_Spec.inv_mem โจhom_z, hom_z_mem_Vโฉโฉ).num with ฮฑ_eq,
  set ฮฒ := (hh.1 โจ((Proj_iso_Spec_Top_component hm f_deg).inv hom_z).1, to_Spec.inv_mem โจhom_z, hom_z_mem_Vโฉโฉ).denom with ฮฒ_eq,
  set ฮน := (hh.1 โจ((Proj_iso_Spec_Top_component hm f_deg).inv hom_z).1, to_Spec.inv_mem โจhom_z, hom_z_mem_Vโฉโฉ).deg with ฮน_eq,
  have ฮฒ_not_in : ฮฒ โ (((Proj_iso_Spec_Top_component hm f_deg).inv)
      ((Proj_iso_Spec_Top_component hm f_deg).hom โจz.1, from_Spec.data_prop1 hm f_deg V _โฉ)).1.as_homogeneous_ideal,
  { exact (hh.1 โจ((Proj_iso_Spec_Top_component hm f_deg).inv hom_z).1, to_Spec.inv_mem โจhom_z, hom_z_mem_Vโฉโฉ).denom_not_mem, },
  have hartshorne_eq : (hh.1 โจ((Proj_iso_Spec_Top_component hm f_deg).inv hom_z).1, to_Spec.inv_mem โจhom_z, hom_z_mem_Vโฉโฉ).val
    = localization.mk ฮฑ โจฮฒ, ฮฒ_not_inโฉ,
  { exact (hh.1 โจ((Proj_iso_Spec_Top_component hm f_deg).inv hom_z).1, to_Spec.inv_mem โจhom_z, hom_z_mem_Vโฉโฉ).eq_num_div_denom, },
  
  have eq0 : (hh.1 z).val = localization.mk ฮฑ โจฮฒ, begin
    rw inv_hom_apply_eq at ฮฒ_not_in,
    convert ฮฒ_not_in,
  endโฉ,
  { have := (pt_eq hm f_deg V z),
    convert hartshorne_eq;
    rw pt_eq hm f_deg V z,
    refl,
    ext,
    refl, },
  rw eq0,

  simp only [โฮฑ_eq, โฮฒ_eq, โฮน_eq] at data_eq2,
  erw [localization.mk_eq_mk', is_localization.eq] at data_eq2,
  obtain โจโจโจ_, โจL1, โจC, C_memโฉ, rflโฉโฉ, hCโฉ, data_eq2โฉ := data_eq2,
  simp only [subtype.ext_iff, subring.coe_mul, subtype.coe_mk] at data_eq2,
  rw [degree_zero_part.eq, degree_zero_part.eq] at data_eq2,
  set a := degree_zero_part.num (from_Spec.data.num hm f_deg (((to_Spec ๐ hm f_deg).app V) hh) z) with a_eq,
  set b := degree_zero_part.num (from_Spec.data.denom hm f_deg (((to_Spec ๐ hm f_deg).app V) hh) z) with b_eq,
  set ii := degree_zero_part.deg (from_Spec.data.num hm f_deg (((to_Spec ๐ hm f_deg).app V) hh) z) with ii_eq,
  set jj := degree_zero_part.deg (from_Spec.data.denom hm f_deg (((to_Spec ๐ hm f_deg).app V) hh) z) with jj_eq,
  simp only [localization.mk_mul, subtype.coe_mk] at data_eq2,
  rw [localization.mk_eq_mk', is_localization.eq] at data_eq2,
  obtain โจโจ_, โจL2, rflโฉโฉ, data_eq2โฉ := data_eq2,
  simp only [submonoid.coe_mul, โpow_add, subtype.coe_mk] at data_eq2,
  unfold from_Spec.num from_Spec.denom,
  dsimp only,
  rw [localization.mk_eq_mk', is_localization.eq],

  refine โจโจC * ฮฒ^m.pred * f^(ฮน+L1+L2), by { apply C_not_mem2, exact hC, exact ฮฒ_not_in }โฉ, _โฉ,
  { simp only [โsubtype.val_eq_coe],
    apply final_eq,
    exact hm,
    exact data_eq2 },
end

end

end from_Spec_to_Spec

namespace to_Spec_from_Spec

variables {๐} {m : โ} {f : A} (hm : 0 < m) (f_deg : f โ ๐ m) (V : (opens ((Spec.T (Aโฐ_ f_deg))))แตแต)
variables  (hh : ((Spec (Aโฐ_ f_deg)).presheaf.obj V)) (z : V.unop)

lemma inv_mem :
((Proj_iso_Spec_Top_component hm f_deg).inv z).1 โ
  ((@opens.open_embedding Proj.T (pbo f)).is_open_map.functor.op.obj
    ((opens.map (Proj_iso_Spec_Top_component hm f_deg).hom).op.obj V)).unop :=
begin
  have mem1 := ((Proj_iso_Spec_Top_component hm f_deg).inv z).2,
  refine โจ((Proj_iso_Spec_Top_component hm f_deg).inv z), _, rflโฉ,
  erw set.mem_preimage,
  convert z.2,
  convert Proj_iso_Spec_Top_component.to_Spec_from_Spec _ _ _ _,
end

lemma inv_mem_pbo :
    ((Proj_iso_Spec_Top_component hm f_deg).inv z).1 โ pbo f :=
begin
  intro rid,
  obtain โจโจa, ha1โฉ, ha2, ha3โฉ := inv_mem hm f_deg V z,
  change a = ((Proj_iso_Spec_Top_component hm f_deg).inv z).1 at ha3,
  erw โha3 at rid,
  apply ha1,
  exact rid,
end

lemma dd_not_mem_z
  (dd : (prime_spectrum.as_ideal
    (((Proj_iso_Spec_Top_component hm f_deg).hom) โจ((Proj_iso_Spec_Top_component hm f_deg).inv z).1, inv_mem_pbo hm f_deg V zโฉ)).prime_compl) :
  dd.1 โ z.1.as_ideal :=
begin
  have mem1 := dd.2,
  change dd.1 โ (((Proj_iso_Spec_Top_component hm f_deg).hom) โจ((Proj_iso_Spec_Top_component hm f_deg).inv z).val, _โฉ).as_ideal at mem1,
  convert mem1,
  change z.1 = Proj_iso_Spec_Top_component.to_Spec.to_fun ๐ f_deg (Proj_iso_Spec_Top_component.from_Spec.to_fun f_deg hm _),
  rw Proj_iso_Spec_Top_component.to_Spec_from_Spec,
  refl,
end

lemma eq0
  (dd : (prime_spectrum.as_ideal
    (((Proj_iso_Spec_Top_component hm f_deg).hom) โจ((Proj_iso_Spec_Top_component hm f_deg).inv z).1, inv_mem_pbo hm f_deg V zโฉ)).prime_compl)
  (nn : Aโฐ_ f_deg)
  (data_eq1 : localization.mk nn dd =
    hh.val โจ((Proj_iso_Spec_Top_component hm f_deg).hom)
    โจ((Proj_iso_Spec_Top_component hm f_deg).inv z).val, _โฉ, begin
      convert z.2,
      change (Proj_iso_Spec_Top_component.to_Spec.to_fun ๐ f_deg (Proj_iso_Spec_Top_component.from_Spec.to_fun f_deg hm _)) = z.1,
      rw Proj_iso_Spec_Top_component.to_Spec_from_Spec,
      refl,
    endโฉ) :
  (hh.1 z) = localization.mk nn โจdd.1, dd_not_mem_z hm f_deg V z ddโฉ :=
begin
  convert from_Spec_to_Spec.section_congr f_deg V hh _ _ _ nn โจdd.1, _โฉ _,
  refine โจ((Proj_iso_Spec_Top_component hm f_deg).hom) โจ(((Proj_iso_Spec_Top_component hm f_deg).inv) โz).val, _โฉ, _โฉ,
  apply inv_mem_pbo,
  convert z.2,
  convert Proj_iso_Spec_Top_component.to_Spec_from_Spec _ _ _ _,
  rw subtype.ext_iff_val,
  convert Proj_iso_Spec_Top_component.to_Spec_from_Spec _ _ _ _,
  exact dd.2,
  rw โ data_eq1,
  congr' 1,
  rw subtype.ext_iff_val,
end

lemma not_mem1
  (C : A) (j : โ) (hj : (graded_algebra.proj ๐ j) C โ (((Proj_iso_Spec_Top_component hm f_deg).inv z)).1.as_homogeneous_ideal) :
  (โจlocalization.mk ((graded_algebra.proj ๐ j) C ^ m) โจf ^ j, โจj, rflโฉโฉ,
    โจj, โจ(graded_algebra.proj ๐ j C)^m, set_like.graded_monoid.pow_mem m (submodule.coe_mem _)โฉ, rflโฉโฉ : Aโฐ_ f_deg) โ
  (prime_spectrum.as_ideal z.val).prime_compl :=
begin
  intro rid,
  change graded_algebra.proj ๐ j C โ Proj_iso_Spec_Top_component.from_Spec.carrier _ at hj,
  apply hj,
  intro k,
  by_cases ineq : j = k,
  { rw โineq,
    convert rid using 1,
    rw subtype.ext_iff_val,
    dsimp only,
    congr' 1,
    rw [graded_algebra.proj_apply, direct_sum.decompose_of_mem_same],
    exact submodule.coe_mem _, },
  { convert submodule.zero_mem _ using 1,
    rw subtype.ext_iff_val,
    dsimp only,
    rw [graded_algebra.proj_apply, direct_sum.decompose_of_mem_ne],
    rw [zero_pow hm, localization.mk_zero],
    refl,
    exact submodule.coe_mem _,
    exact ineq, }
end

lemma eq1
  (hart : homogeneous_localization ๐ ((Proj_iso_Spec_Top_component hm f_deg).inv z).1.as_homogeneous_ideal.to_ideal)
  (C : A) (j : โ) (hj : (graded_algebra.proj ๐ j) C โ
    projective_spectrum.as_homogeneous_ideal (((Proj_iso_Spec_Top_component hm f_deg).inv z)).val)
  (dd : (prime_spectrum.as_ideal
   (((Proj_iso_Spec_Top_component hm f_deg).hom) โจ((Proj_iso_Spec_Top_component hm f_deg).inv z).1, inv_mem_pbo hm f_deg V zโฉ)).prime_compl)
  (nn : Aโฐ_ f_deg)
  (EQ : hart.num * (degree_zero_part.num dd.val * f ^ degree_zero_part.deg nn) * graded_algebra.proj ๐ j C =
        degree_zero_part.num nn * f ^ degree_zero_part.deg dd.val * hart.denom * graded_algebra.proj ๐ j C) :
  hart.num * hart.denom ^ m.pred * degree_zero_part.num dd.val * (graded_algebra.proj ๐ j) C ^ m *
    f ^ (degree_zero_part.deg nn + hart.deg + j) =
  degree_zero_part.num nn * hart.denom ^ m * (graded_algebra.proj ๐ j) C ^ m *
    f ^ (hart.deg + degree_zero_part.deg dd.val + j) :=
begin
  rw calc hart.num * hart.denom ^ m.pred * degree_zero_part.num dd.val
            * (graded_algebra.proj ๐ j) C ^ m * f ^ (degree_zero_part.deg nn + hart.deg + j)
          = hart.num * hart.denom ^ m.pred * degree_zero_part.num dd.val
            * (graded_algebra.proj ๐ j) C ^ (m.pred + 1) * f ^ (degree_zero_part.deg nn + hart.deg + j)
          : begin
            congr',
            symmetry,
            apply nat.succ_pred_eq_of_pos hm,
          end
      ... = hart.num * hart.denom ^ m.pred * degree_zero_part.num dd.val
            * ((graded_algebra.proj ๐ j) C ^ m.pred * graded_algebra.proj ๐ j C)
            * f ^ (degree_zero_part.deg nn + hart.deg + j) : by simp only [pow_add, pow_one]
      ... = hart.num * hart.denom ^ m.pred * degree_zero_part.num dd.val
            * ((graded_algebra.proj ๐ j) C ^ m.pred * graded_algebra.proj ๐ j C)
            * (f ^ degree_zero_part.deg nn * f ^ hart.deg * f^j) : by simp only [pow_add]
      ... = (hart.num * (degree_zero_part.num dd.val * f ^ degree_zero_part.deg nn) * graded_algebra.proj ๐ j C)
            * (hart.denom ^ m.pred * graded_algebra.proj ๐ j C ^ m.pred * f ^ hart.deg * f ^ j) : by ring
      ... = (degree_zero_part.num nn * f ^ degree_zero_part.deg dd.val * hart.denom * graded_algebra.proj ๐ j C)
            * (hart.denom ^ m.pred * graded_algebra.proj ๐ j C ^ m.pred * f ^ hart.deg * f ^ j) : by rw EQ
      ... = (degree_zero_part.num nn * f ^ degree_zero_part.deg dd.val)
            * (graded_algebra.proj ๐ j C ^ m.pred * graded_algebra.proj ๐ j C)
            * (hart.denom ^ m.pred * hart.denom) * (f ^ hart.deg * f ^ j) : by ring
      ... = (degree_zero_part.num nn * f ^ degree_zero_part.deg dd.val)
            * (graded_algebra.proj ๐ j C ^ m.pred * graded_algebra.proj ๐ j C ^ 1)
            * (hart.denom ^ m.pred * hart.denom ^ 1) * (f ^ hart.deg * f ^ j) : by simp only [pow_one]
      ... = (degree_zero_part.num nn * f ^ degree_zero_part.deg dd.val)
            * (graded_algebra.proj ๐ j C ^ (m.pred + 1))
            * (hart.denom ^ (m.pred + 1)) * (f ^ hart.deg * f ^ j) : by simp only [pow_add]
      ... = (degree_zero_part.num nn * f ^ degree_zero_part.deg dd.val)
            * (graded_algebra.proj ๐ j C ^ m)
            * (hart.denom ^ m) * (f ^ hart.deg * f ^ j)
          : begin
            congr';
            apply nat.succ_pred_eq_of_pos hm,
          end,
    simp only [pow_add],
    ring,
end

lemma eq2
  (hart : homogeneous_localization ๐ ((Proj_iso_Spec_Top_component hm f_deg).inv z).1.as_homogeneous_ideal.to_ideal)
  (C : A) (j : โ) (hj : (graded_algebra.proj ๐ j) C โ
    projective_spectrum.as_homogeneous_ideal (((Proj_iso_Spec_Top_component hm f_deg).inv z)).val)
  (proj_C_ne_zero : graded_algebra.proj ๐ j C โ? 0)
  (dd : (prime_spectrum.as_ideal
   (((Proj_iso_Spec_Top_component hm f_deg).hom) โจ((Proj_iso_Spec_Top_component hm f_deg).inv z).1, inv_mem_pbo hm f_deg V zโฉ)).prime_compl)
  (nn : Aโฐ_ f_deg)
  (eq1 : hart.num * (degree_zero_part.num dd.val * f ^ degree_zero_part.deg nn) * C =
    degree_zero_part.num nn * f ^ degree_zero_part.deg dd.val * hart.denom * C) :
  hart.num * (degree_zero_part.num dd.val * f ^ degree_zero_part.deg nn) * graded_algebra.proj ๐ j C =
  degree_zero_part.num nn * f ^ degree_zero_part.deg dd.val * hart.denom * graded_algebra.proj ๐ j C :=
begin
  have mem1 := degree_zero_part.num_mem dd.1,
  have mem2 := degree_zero_part.num_mem nn,
  have eq2 := congr_arg
    (graded_algebra.proj ๐ (hart.deg + m * degree_zero_part.deg dd.1 + m * degree_zero_part.deg nn + j)) eq1,
  rw graded_algebra.proj_hom_mul at eq2,
  rw graded_algebra.proj_hom_mul at eq2,
  exact eq2,

  rw show degree_zero_part.num nn * f ^ degree_zero_part.deg dd.val * hart.denom =
    hart.denom * f ^ degree_zero_part.deg dd.1 * degree_zero_part.num nn, by ring,
  apply set_like.graded_monoid.mul_mem,
  apply set_like.graded_monoid.mul_mem,
  apply hart.denom_mem,
  rw nat.mul_comm,
  apply set_like.graded_monoid.pow_mem _ f_deg,
  exact mem2,
  exact proj_C_ne_zero,

  rw โmul_assoc,
  apply set_like.graded_monoid.mul_mem,
  apply set_like.graded_monoid.mul_mem,
  apply hart.num_mem,
  exact mem1,
  rw nat.mul_comm,
  apply set_like.graded_monoid.pow_mem _ f_deg,
  exact proj_C_ne_zero,
end

lemma _root_.algebraic_geometry.Proj_iso_Spec_Sheaf_component.to_Spec_from_Spec {m : โ} {f : A} (f_deg : f โ ๐ m) (hm : 0 < m) (V hh z) :
  to_Spec.fmk hm (((from_Spec ๐ hm f_deg).app V) hh) z =
  hh.val z :=
begin
  classical,

  set b_hh := ((from_Spec ๐ hm f_deg).app V hh) with b_hh_eq,
  unfold to_Spec.fmk to_Spec.num to_Spec.denom,
  set inv_z := ((Proj_iso_Spec_Top_component hm f_deg).inv z) with inv_z_eq,
  have inv_z_mem : inv_z.1 โ
    ((@opens.open_embedding Proj.T (pbo f)).is_open_map.functor.op.obj
    ((opens.map (Proj_iso_Spec_Top_component hm f_deg).hom).op.obj V)).unop,
  { apply to_Spec_from_Spec.inv_mem, },

  have inv_z_mem_bo : inv_z.1 โ projective_spectrum.basic_open ๐ f,
  { apply to_Spec_from_Spec.inv_mem_pbo, },

  set hart := b_hh.1 โจinv_z.1, inv_z_memโฉ with hart_eq,
  rw homogeneous_localization.ext_iff_val at hart_eq,
  have hart_eq1 := hart.eq_num_div_denom,
  rw hart_eq at hart_eq1,

  rw b_hh_eq at hart_eq,
  replace hart_eq : hart.val = (from_Spec.bmk hm f_deg V hh โจinv_z.val, inv_z_memโฉ).val,
  { convert hart_eq },
  unfold from_Spec.bmk at hart_eq,
  rw [homogeneous_localization.val_mk'] at hart_eq,
  simp only [โ subtype.val_eq_coe] at hart_eq,
  unfold from_Spec.num from_Spec.denom at hart_eq,

  set data := from_Spec.data hm f_deg hh โจinv_z.val, inv_z_memโฉ with data_eq,
  have data_eq1 := data_eq,
  unfold from_Spec.data at data_eq1,
  erw from_Spec.data.eq_num_div_denom at data_eq,
  erw data_eq at data_eq1,
  set nn := from_Spec.data.num hm f_deg hh โจinv_z.val, inv_z_memโฉ with nn_eq,
  set dd := from_Spec.data.denom hm f_deg hh โจinv_z.val, inv_z_memโฉ with dd_eq,
  dsimp only at hart_eq,

  rw hart.eq_num_div_denom at hart_eq,
  rw [localization.mk_eq_mk', is_localization.eq] at hart_eq,
  obtain โจโจC, hCโฉ, eq1โฉ := hart_eq,
  simp only [โsubtype.val_eq_coe] at eq1,
  have hC2 : โ j : โ, graded_algebra.proj ๐ j C โ inv_z.1.as_homogeneous_ideal,
  { by_contra rid,
    rw not_exists at rid,
    apply hC,
    rw โdirect_sum.sum_support_decompose ๐ C,
    apply ideal.sum_mem inv_z.1.as_homogeneous_ideal.1,
    intros j hj,
    specialize rid j,
    rw not_not at rid,
    exact rid, },
  obtain โจj, hjโฉ := hC2,

  have proj_C_ne_zero : graded_algebra.proj ๐ j C โ? 0,
  { intro rid,
    rw rid at hj,
    apply hj,
    exact submodule.zero_mem _, },

  have dd_not_mem_z : dd โ z.val.as_ideal,
  { apply to_Spec_from_Spec.dd_not_mem_z, },

  have eq0 : (hh.1 z) = localization.mk nn โจdd, dd_not_mem_zโฉ,
  { convert to_Spec_from_Spec.eq0 hm f_deg _ hh z โจdd, _โฉ nn data_eq1, },
  rw [eq0, localization.mk_eq_mk', is_localization.eq],
  simp only [subtype.ext_iff, subring.coe_mul, subtype.coe_mk],
  rw [degree_zero_part.eq, degree_zero_part.eq, localization.mk_mul, localization.mk_mul],
  simp only [subtype.coe_mk],

  refine โจโจโจlocalization.mk ((graded_algebra.proj ๐ j C)^m) โจf^j, โจj, rflโฉโฉ,
    โจj, โจ(graded_algebra.proj ๐ j C)^m, set_like.graded_monoid.pow_mem _ (submodule.coe_mem _)โฉ, rflโฉโฉ,
    to_Spec_from_Spec.not_mem1 hm f_deg V z C j hjโฉ, _โฉ,
  simp only [subtype.coe_mk],
  { rw [localization.mk_mul, localization.mk_mul, localization.mk_eq_mk', is_localization.eq],
    use 1,
    simp only [โsubtype.val_eq_coe,
      show โ (p q : submonoid.powers f), (p * q).1 = p.1 * q.1, from ฮป _ _, rfl, โpow_add,
      show (1 : submonoid.powers f).1 = 1, from rfl, mul_one, one_mul],
    apply to_Spec_from_Spec.eq1,
    exact hj,
    apply to_Spec_from_Spec.eq2;
    assumption, }
end

end to_Spec_from_Spec

end Proj_iso_Spec_Sheaf_component

def Sheaf_component {m : โ} {f : A} (f_deg : f โ ๐ m) (hm : 0 < m) :
  (Proj_iso_Spec_Top_component hm f_deg).hom _* (Proj| (pbo f)).presheaf โ (Spec (Aโฐ_ f_deg)).presheaf :=
{ hom := Proj_iso_Spec_Sheaf_component.to_Spec ๐ hm f_deg,
  inv := Proj_iso_Spec_Sheaf_component.from_Spec ๐ hm f_deg,
  hom_inv_id' := begin
    ext1,
    ext1 V,
    ext1 hh,
    erw [nat_trans.comp_app, nat_trans.id_app, comp_apply, id_apply, subtype.ext_iff_val],
    ext1 z,
    apply Proj_iso_Spec_Sheaf_component.from_Spec_to_Spec,
  end,
  inv_hom_id' := begin
    ext1, ext1 V, ext1 hh,
    erw [nat_trans.comp_app, nat_trans.id_app, comp_apply, id_apply],
    rw subtype.ext_iff_val,
    ext1 z,
    apply Proj_iso_Spec_Sheaf_component.to_Spec_from_Spec,
  end }

def SheafedSpace.iso_of_PresheafedSpace_iso 
  {C : Type*} [category C] [limits.has_products C] 
  (X Y : @@SheafedSpace C _ (by assumption : limits.has_products C)) (H : X.to_PresheafedSpace โ Y.to_PresheafedSpace) : X โ Y :=
 { hom := H.hom,
   inv := H.inv,
   hom_inv_id' := H.hom_inv_id',
   inv_hom_id' := H.inv_hom_id' }

def Proj_iso_Spec_Sheaf_component.iso {m : โ} {f : A} (f_deg : f โ ๐ m) (hm : 0 < m) :
  (Proj| (pbo f)) โ Spec (Aโฐ_ f_deg) :=
LocallyRingedSpace.iso_of_SheafedSpace_iso $ SheafedSpace.iso_of_PresheafedSpace_iso _ _ $ 
@PresheafedSpace.iso_of_components _ _ 
(Proj| (pbo f)).to_PresheafedSpace 
(Spec (Aโฐ_ f_deg)).to_PresheafedSpace 
(Proj_iso_Spec_Top_component hm f_deg) (Sheaf_component ๐ f_deg hm)

end algebraic_geometry