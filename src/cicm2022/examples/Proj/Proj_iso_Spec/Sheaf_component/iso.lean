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

namespace from_Spec_to_Spec

variables {𝒜} {m : ℕ} {f : A} (hm : 0 < m) (f_deg : f ∈ 𝒜 m) (V : (opens (Spec.T (A⁰_ f_deg)))ᵒᵖ)
variables (hh : ((Proj_iso_Spec_Top_component hm f_deg).hom _* (Proj| (pbo f)).presheaf).obj V)
variables (z : (((@opens.open_embedding Proj.T (pbo f)).is_open_map.functor.op.obj ((opens.map (Proj_iso_Spec_Top_component hm f_deg).hom).op.obj V)).unop))

lemma section_congr
  (hh : ((Spec (A⁰_ f_deg)).presheaf).obj V) (x y : unop V) (h1 : x = y)
  (a : _) (b : x.1.as_ideal.prime_compl)
  (h2 : (hh.1 x) = localization.mk a b) : (hh.1 y) = localization.mk a ⟨b.1, begin
    intro rid,
    apply b.2,
    simp only [h1],
    exact rid
  end⟩ :=
begin
  induction h1,
  convert h2,
  rw subtype.ext_iff_val,
end

lemma inv_hom_apply_eq :
  ((Proj_iso_Spec_Top_component hm f_deg).inv ((Proj_iso_Spec_Top_component hm f_deg).hom ⟨z.1, from_Spec.data_prop1 hm f_deg _ _⟩)).1 = z.1 :=
begin
  change (Proj_iso_Spec_Top_component.from_Spec.to_fun f_deg hm (Proj_iso_Spec_Top_component.to_Spec.to_fun 𝒜 f_deg _)).1 = z.1,
  rw Proj_iso_Spec_Top_component.from_Spec_to_Spec,
end

lemma pt_eq :
  z = ⟨((Proj_iso_Spec_Top_component hm f_deg).inv ((Proj_iso_Spec_Top_component hm f_deg).hom ⟨z.1, from_Spec.data_prop1 hm f_deg _ _⟩)).1, begin
    simpa only [inv_hom_apply_eq hm f_deg V z] using z.2,
  end⟩ :=
begin
  rw [subtype.ext_iff_val, inv_hom_apply_eq],
end

lemma C_not_mem (C : A) (L1 : ℕ) (C_mem : C ∈ 𝒜 (m * L1))
  (hC : (⟨localization.mk C ⟨f ^ L1, ⟨_, rfl⟩⟩, ⟨L1, ⟨_, C_mem⟩, rfl⟩⟩ : A⁰_ f_deg) ∉ 
    ((Proj_iso_Spec_Top_component hm f_deg).hom ⟨z.1, from_Spec.data_prop1 hm f_deg V _⟩).as_ideal) :
  C ∉ z.1.as_homogeneous_ideal :=
begin
  intro rid,
  have eq1 : (localization.mk C ⟨f ^ L1, ⟨_, rfl⟩⟩ : localization.away f) =
    (localization.mk 1 ⟨f^L1, ⟨_, rfl⟩⟩ : localization.away f) * localization.mk C 1,
    rw [localization.mk_mul, one_mul, mul_one],
  simp only [eq1] at hC,
  apply hC,
  erw Proj_iso_Spec_Top_component.to_Spec.mem_carrier_iff,
  dsimp only,
  convert ideal.mul_mem_left _ _ _,
  apply ideal.subset_span,
  refine ⟨C, rid, rfl⟩,
end 

lemma C_not_mem2
  (C : A) (ι L1 L2 : ℕ) (C_mem : C ∈ 𝒜 (m * L1))
  (hC : (⟨localization.mk C ⟨f ^ L1, ⟨_, rfl⟩⟩, ⟨L1, ⟨_, C_mem⟩, rfl⟩⟩ : A⁰_ f_deg) ∉ 
    ((Proj_iso_Spec_Top_component hm f_deg).hom ⟨z.1, from_Spec.data_prop1 hm f_deg V _⟩).as_ideal)
  (β : A) 
  (β_not_in : β ∉ (((Proj_iso_Spec_Top_component hm f_deg).inv)
      ((Proj_iso_Spec_Top_component hm f_deg).hom ⟨z.1, from_Spec.data_prop1 hm f_deg V _⟩)).1.as_homogeneous_ideal) :
  C * β^m.pred * f^(ι+L1+L2) ∉ z.1.as_homogeneous_ideal :=
begin
  intro rid,
  rcases z.1.is_prime.mem_or_mem rid with H1 | H3,
  rcases z.1.is_prime.mem_or_mem H1 with H1 | H2,
  apply C_not_mem hm f_deg,
  exact hC,
  exact H1,
  replace H2 := z.1.is_prime.mem_of_pow_mem _ H2,
  apply β_not_in,
  have eq1 : (((Proj_iso_Spec_Top_component hm f_deg).inv) ((Proj_iso_Spec_Top_component hm f_deg).hom ⟨z.1, from_Spec.data_prop1 hm f_deg V _⟩)).1 = z.1,
  { change (Proj_iso_Spec_Top_component.from_Spec.to_fun f_deg hm (Proj_iso_Spec_Top_component.to_Spec.to_fun 𝒜 _ _)).1 = z.1,
    rw Proj_iso_Spec_Top_component.from_Spec_to_Spec, },
  erw eq1,
  exact H2,
  replace H3 := z.1.is_prime.mem_of_pow_mem _ H3,
  have mem2 := z.2,
  obtain ⟨⟨a, ha⟩, ha2, ha3⟩ := mem2,
  change a = z.1 at ha3,
  apply ha,
  rw ha3,
  exact H3,
end

include hm
lemma final_eq
  (a α β b C : A) (ι ii jj L1 L2 : ℕ)
  (data_eq2 : α * β ^ m.pred * b * C * f ^ (ii + ι + L1) * f ^ L2 = a * β ^ m * C * f ^ (ι + jj + L1) * f ^ L2) :
  a * f ^ jj * β * (C * β ^ m.pred * f ^ (ι + L1 + L2)) = α * (b * f ^ ii) * (C * β ^ m.pred * f ^ (ι + L1 + L2)) :=
begin
  symmetry,
  rw calc α * (b * f ^ ii) * (C * β ^ m.pred * f ^ (ι + L1 + L2))
        = α * β ^ m.pred * b * C * (f^ii * f^(ι + L1 + L2)) : by ring
    ... = α * β ^ m.pred * b * C * (f^ii * (f^ι * f^L1 * f^L2)) : by simp only [pow_add]
    ... = α * β ^ m.pred * b * C * (f ^ ii * f^ι * f^L1) * f ^ L2 : by ring
    ... = α * β ^ m.pred * b * C * (f ^ (ii + ι + L1)) * f ^ L2 : by simp only [pow_add]
    ... = a * β ^ m * C * f ^ (ι + jj + L1) * f ^ L2 : by rw data_eq2
    ... = a * β ^ (m.pred + 1) * C * f ^ (ι + jj + L1) * f ^ L2
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
    (((to_Spec 𝒜 hm f_deg).app V) hh) z = hh.1 z :=
begin
  unfold from_Spec.bmk,
  rw [homogeneous_localization.ext_iff_val, homogeneous_localization.val_mk'],
  simp only [← subtype.val_eq_coe],

  set hom_z := (Proj_iso_Spec_Top_component hm f_deg).hom ⟨z.1, from_Spec.data_prop1 hm f_deg V _⟩ with hom_z_eq,
  have hom_z_mem_V : hom_z ∈ unop V,
  { apply from_Spec.data_prop2 hm f_deg V _, },

  set data := from_Spec.data hm f_deg (((to_Spec 𝒜 hm f_deg).app V) hh) z with data_eq,
  have data_eq1 := data_eq,
  replace data_eq1 : data = to_Spec.fmk hm hh ⟨hom_z, hom_z_mem_V⟩,
  { convert data_eq1, },
  unfold to_Spec.fmk to_Spec.num to_Spec.denom at data_eq1,

  have data_eq2 := from_Spec.data.eq_num_div_denom hm f_deg (((to_Spec 𝒜 hm f_deg).app V) hh) z,
  rw [←data_eq, data_eq1] at data_eq2,
  set α := (hh.1 ⟨((Proj_iso_Spec_Top_component hm f_deg).inv hom_z).1, to_Spec.inv_mem ⟨hom_z, hom_z_mem_V⟩⟩).num with α_eq,
  set β := (hh.1 ⟨((Proj_iso_Spec_Top_component hm f_deg).inv hom_z).1, to_Spec.inv_mem ⟨hom_z, hom_z_mem_V⟩⟩).denom with β_eq,
  set ι := (hh.1 ⟨((Proj_iso_Spec_Top_component hm f_deg).inv hom_z).1, to_Spec.inv_mem ⟨hom_z, hom_z_mem_V⟩⟩).deg with ι_eq,
  have β_not_in : β ∉ (((Proj_iso_Spec_Top_component hm f_deg).inv)
      ((Proj_iso_Spec_Top_component hm f_deg).hom ⟨z.1, from_Spec.data_prop1 hm f_deg V _⟩)).1.as_homogeneous_ideal,
  { exact (hh.1 ⟨((Proj_iso_Spec_Top_component hm f_deg).inv hom_z).1, to_Spec.inv_mem ⟨hom_z, hom_z_mem_V⟩⟩).denom_not_mem, },
  have hartshorne_eq : (hh.1 ⟨((Proj_iso_Spec_Top_component hm f_deg).inv hom_z).1, to_Spec.inv_mem ⟨hom_z, hom_z_mem_V⟩⟩).val
    = localization.mk α ⟨β, β_not_in⟩,
  { exact (hh.1 ⟨((Proj_iso_Spec_Top_component hm f_deg).inv hom_z).1, to_Spec.inv_mem ⟨hom_z, hom_z_mem_V⟩⟩).eq_num_div_denom, },
  
  have eq0 : (hh.1 z).val = localization.mk α ⟨β, begin
    rw inv_hom_apply_eq at β_not_in,
    convert β_not_in,
  end⟩,
  { have := (pt_eq hm f_deg V z),
    convert hartshorne_eq;
    rw pt_eq hm f_deg V z,
    refl,
    ext,
    refl, },
  rw eq0,

  simp only [←α_eq, ←β_eq, ←ι_eq] at data_eq2,
  erw [localization.mk_eq_mk', is_localization.eq] at data_eq2,
  obtain ⟨⟨⟨_, ⟨L1, ⟨C, C_mem⟩, rfl⟩⟩, hC⟩, data_eq2⟩ := data_eq2,
  simp only [←subtype.val_eq_coe, subtype.ext_iff_val, degree_zero_part.mul_val] at data_eq2,
  rw [degree_zero_part.eq, degree_zero_part.eq] at data_eq2,
  set a := degree_zero_part.num (from_Spec.data.num hm f_deg (((to_Spec 𝒜 hm f_deg).app V) hh) z) with a_eq,
  set b := degree_zero_part.num (from_Spec.data.denom hm f_deg (((to_Spec 𝒜 hm f_deg).app V) hh) z) with b_eq,
  set ii := degree_zero_part.deg (from_Spec.data.num hm f_deg (((to_Spec 𝒜 hm f_deg).app V) hh) z) with ii_eq,
  set jj := degree_zero_part.deg (from_Spec.data.denom hm f_deg (((to_Spec 𝒜 hm f_deg).app V) hh) z) with jj_eq,
  simp only [localization.mk_mul] at data_eq2,
  rw [localization.mk_eq_mk', is_localization.eq] at data_eq2,
  obtain ⟨⟨_, ⟨L2, rfl⟩⟩, data_eq2⟩ := data_eq2,
  simp only [←subtype.val_eq_coe, show ∀ (p q : submonoid.powers f), (p * q).1 = p.1 * q.1, from λ _ _, rfl,
    ←pow_add] at data_eq2,
  unfold from_Spec.num from_Spec.denom,
  dsimp only,
  rw [localization.mk_eq_mk', is_localization.eq],

  refine ⟨⟨C * β^m.pred * f^(ι+L1+L2), by { apply C_not_mem2, exact hC, exact β_not_in }⟩, _⟩,
  { simp only [←subtype.val_eq_coe],
    apply final_eq,
    exact hm,
    exact data_eq2 },
end

end

end from_Spec_to_Spec

namespace to_Spec_from_Spec

variables {𝒜} {m : ℕ} {f : A} (hm : 0 < m) (f_deg : f ∈ 𝒜 m) (V : (opens ((Spec.T (A⁰_ f_deg))))ᵒᵖ)
variables  (hh : ((Spec (A⁰_ f_deg)).presheaf.obj V)) (z : V.unop)

lemma inv_mem :
((Proj_iso_Spec_Top_component hm f_deg).inv z).1 ∈
  ((@opens.open_embedding Proj.T (pbo f)).is_open_map.functor.op.obj
    ((opens.map (Proj_iso_Spec_Top_component hm f_deg).hom).op.obj V)).unop :=
begin
  have mem1 := ((Proj_iso_Spec_Top_component hm f_deg).inv z).2,
  refine ⟨((Proj_iso_Spec_Top_component hm f_deg).inv z), _, rfl⟩,
  erw set.mem_preimage,
  convert z.2,
  convert Proj_iso_Spec_Top_component.to_Spec_from_Spec _ _ _ _,
end

lemma inv_mem_pbo :
    ((Proj_iso_Spec_Top_component hm f_deg).inv z).1 ∈ pbo f :=
begin
  intro rid,
  obtain ⟨⟨a, ha1⟩, ha2, ha3⟩ := inv_mem hm f_deg V z,
  change a = ((Proj_iso_Spec_Top_component hm f_deg).inv z).1 at ha3,
  erw ←ha3 at rid,
  apply ha1,
  exact rid,
end

lemma dd_not_mem_z
  (dd : (prime_spectrum.as_ideal
    (((Proj_iso_Spec_Top_component hm f_deg).hom) ⟨((Proj_iso_Spec_Top_component hm f_deg).inv z).1, inv_mem_pbo hm f_deg V z⟩)).prime_compl) :
  dd.1 ∉ z.1.as_ideal :=
begin
  have mem1 := dd.2,
  change dd.1 ∉ (((Proj_iso_Spec_Top_component hm f_deg).hom) ⟨((Proj_iso_Spec_Top_component hm f_deg).inv z).val, _⟩).as_ideal at mem1,
  convert mem1,
  change z.1 = Proj_iso_Spec_Top_component.to_Spec.to_fun 𝒜 f_deg (Proj_iso_Spec_Top_component.from_Spec.to_fun f_deg hm _),
  rw Proj_iso_Spec_Top_component.to_Spec_from_Spec,
  refl,
end

lemma eq0
  (dd : (prime_spectrum.as_ideal
    (((Proj_iso_Spec_Top_component hm f_deg).hom) ⟨((Proj_iso_Spec_Top_component hm f_deg).inv z).1, inv_mem_pbo hm f_deg V z⟩)).prime_compl)
  (nn : A⁰_ f_deg)
  (data_eq1 : localization.mk nn dd =
    hh.val ⟨((Proj_iso_Spec_Top_component hm f_deg).hom)
    ⟨((Proj_iso_Spec_Top_component hm f_deg).inv z).val, _⟩, begin
      convert z.2,
      change (Proj_iso_Spec_Top_component.to_Spec.to_fun 𝒜 f_deg (Proj_iso_Spec_Top_component.from_Spec.to_fun f_deg hm _)) = z.1,
      rw Proj_iso_Spec_Top_component.to_Spec_from_Spec,
      refl,
    end⟩) :
  (hh.1 z) = localization.mk nn ⟨dd.1, dd_not_mem_z hm f_deg V z dd⟩ :=
begin
  convert from_Spec_to_Spec.section_congr f_deg V hh _ _ _ nn ⟨dd.1, _⟩ _,
  refine ⟨((Proj_iso_Spec_Top_component hm f_deg).hom) ⟨(((Proj_iso_Spec_Top_component hm f_deg).inv) ↑z).val, _⟩, _⟩,
  apply inv_mem_pbo,
  convert z.2,
  convert Proj_iso_Spec_Top_component.to_Spec_from_Spec _ _ _ _,
  rw subtype.ext_iff_val,
  convert Proj_iso_Spec_Top_component.to_Spec_from_Spec _ _ _ _,
  exact dd.2,
  rw ← data_eq1,
  congr' 1,
  rw subtype.ext_iff_val,
end

lemma not_mem1
  (C : A) (j : ℕ) (hj : (graded_algebra.proj 𝒜 j) C ∉ (((Proj_iso_Spec_Top_component hm f_deg).inv z)).1.as_homogeneous_ideal) :
  (⟨localization.mk ((graded_algebra.proj 𝒜 j) C ^ m) ⟨f ^ j, ⟨j, rfl⟩⟩,
    ⟨j, ⟨(graded_algebra.proj 𝒜 j C)^m, set_like.graded_monoid.pow_mem m (submodule.coe_mem _)⟩, rfl⟩⟩ : A⁰_ f_deg) ∈
  (prime_spectrum.as_ideal z.val).prime_compl :=
begin
  intro rid,
  change graded_algebra.proj 𝒜 j C ∉ Proj_iso_Spec_Top_component.from_Spec.carrier _ at hj,
  apply hj,
  intro k,
  by_cases ineq : j = k,
  { rw ←ineq,
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
  (hart : homogeneous_localization 𝒜 ((Proj_iso_Spec_Top_component hm f_deg).inv z).1.as_homogeneous_ideal.to_ideal)
  (C : A) (j : ℕ) (hj : (graded_algebra.proj 𝒜 j) C ∉
    projective_spectrum.as_homogeneous_ideal (((Proj_iso_Spec_Top_component hm f_deg).inv z)).val)
  (dd : (prime_spectrum.as_ideal
   (((Proj_iso_Spec_Top_component hm f_deg).hom) ⟨((Proj_iso_Spec_Top_component hm f_deg).inv z).1, inv_mem_pbo hm f_deg V z⟩)).prime_compl)
  (nn : A⁰_ f_deg)
  (EQ : hart.num * (degree_zero_part.num dd.val * f ^ degree_zero_part.deg nn) * graded_algebra.proj 𝒜 j C =
        degree_zero_part.num nn * f ^ degree_zero_part.deg dd.val * hart.denom * graded_algebra.proj 𝒜 j C) :
  hart.num * hart.denom ^ m.pred * degree_zero_part.num dd.val * (graded_algebra.proj 𝒜 j) C ^ m *
    f ^ (degree_zero_part.deg nn + hart.deg + j) =
  degree_zero_part.num nn * hart.denom ^ m * (graded_algebra.proj 𝒜 j) C ^ m *
    f ^ (hart.deg + degree_zero_part.deg dd.val + j) :=
begin
  rw calc hart.num * hart.denom ^ m.pred * degree_zero_part.num dd.val
            * (graded_algebra.proj 𝒜 j) C ^ m * f ^ (degree_zero_part.deg nn + hart.deg + j)
          = hart.num * hart.denom ^ m.pred * degree_zero_part.num dd.val
            * (graded_algebra.proj 𝒜 j) C ^ (m.pred + 1) * f ^ (degree_zero_part.deg nn + hart.deg + j)
          : begin
            congr',
            symmetry,
            apply nat.succ_pred_eq_of_pos hm,
          end
      ... = hart.num * hart.denom ^ m.pred * degree_zero_part.num dd.val
            * ((graded_algebra.proj 𝒜 j) C ^ m.pred * graded_algebra.proj 𝒜 j C)
            * f ^ (degree_zero_part.deg nn + hart.deg + j) : by simp only [pow_add, pow_one]
      ... = hart.num * hart.denom ^ m.pred * degree_zero_part.num dd.val
            * ((graded_algebra.proj 𝒜 j) C ^ m.pred * graded_algebra.proj 𝒜 j C)
            * (f ^ degree_zero_part.deg nn * f ^ hart.deg * f^j) : by simp only [pow_add]
      ... = (hart.num * (degree_zero_part.num dd.val * f ^ degree_zero_part.deg nn) * graded_algebra.proj 𝒜 j C)
            * (hart.denom ^ m.pred * graded_algebra.proj 𝒜 j C ^ m.pred * f ^ hart.deg * f ^ j) : by ring
      ... = (degree_zero_part.num nn * f ^ degree_zero_part.deg dd.val * hart.denom * graded_algebra.proj 𝒜 j C)
            * (hart.denom ^ m.pred * graded_algebra.proj 𝒜 j C ^ m.pred * f ^ hart.deg * f ^ j) : by rw EQ
      ... = (degree_zero_part.num nn * f ^ degree_zero_part.deg dd.val)
            * (graded_algebra.proj 𝒜 j C ^ m.pred * graded_algebra.proj 𝒜 j C)
            * (hart.denom ^ m.pred * hart.denom) * (f ^ hart.deg * f ^ j) : by ring
      ... = (degree_zero_part.num nn * f ^ degree_zero_part.deg dd.val)
            * (graded_algebra.proj 𝒜 j C ^ m.pred * graded_algebra.proj 𝒜 j C ^ 1)
            * (hart.denom ^ m.pred * hart.denom ^ 1) * (f ^ hart.deg * f ^ j) : by simp only [pow_one]
      ... = (degree_zero_part.num nn * f ^ degree_zero_part.deg dd.val)
            * (graded_algebra.proj 𝒜 j C ^ (m.pred + 1))
            * (hart.denom ^ (m.pred + 1)) * (f ^ hart.deg * f ^ j) : by simp only [pow_add]
      ... = (degree_zero_part.num nn * f ^ degree_zero_part.deg dd.val)
            * (graded_algebra.proj 𝒜 j C ^ m)
            * (hart.denom ^ m) * (f ^ hart.deg * f ^ j)
          : begin
            congr';
            apply nat.succ_pred_eq_of_pos hm,
          end,
    simp only [pow_add],
    ring,
end

lemma eq2
  (hart : homogeneous_localization 𝒜 ((Proj_iso_Spec_Top_component hm f_deg).inv z).1.as_homogeneous_ideal.to_ideal)
  (C : A) (j : ℕ) (hj : (graded_algebra.proj 𝒜 j) C ∉
    projective_spectrum.as_homogeneous_ideal (((Proj_iso_Spec_Top_component hm f_deg).inv z)).val)
  (proj_C_ne_zero : graded_algebra.proj 𝒜 j C ≠ 0)
  (dd : (prime_spectrum.as_ideal
   (((Proj_iso_Spec_Top_component hm f_deg).hom) ⟨((Proj_iso_Spec_Top_component hm f_deg).inv z).1, inv_mem_pbo hm f_deg V z⟩)).prime_compl)
  (nn : A⁰_ f_deg)
  (eq1 : hart.num * (degree_zero_part.num dd.val * f ^ degree_zero_part.deg nn) * C =
    degree_zero_part.num nn * f ^ degree_zero_part.deg dd.val * hart.denom * C) :
  hart.num * (degree_zero_part.num dd.val * f ^ degree_zero_part.deg nn) * graded_algebra.proj 𝒜 j C =
  degree_zero_part.num nn * f ^ degree_zero_part.deg dd.val * hart.denom * graded_algebra.proj 𝒜 j C :=
begin
  have mem1 := degree_zero_part.num_mem dd.1,
  have mem2 := degree_zero_part.num_mem nn,
  have eq2 := congr_arg
    (graded_algebra.proj 𝒜 (hart.deg + m * degree_zero_part.deg dd.1 + m * degree_zero_part.deg nn + j)) eq1,
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

  rw ←mul_assoc,
  apply set_like.graded_monoid.mul_mem,
  apply set_like.graded_monoid.mul_mem,
  apply hart.num_mem,
  exact mem1,
  rw nat.mul_comm,
  apply set_like.graded_monoid.pow_mem _ f_deg,
  exact proj_C_ne_zero,
end

lemma _root_.algebraic_geometry.Proj_iso_Spec_Sheaf_component.to_Spec_from_Spec {m : ℕ} {f : A} (f_deg : f ∈ 𝒜 m) (hm : 0 < m) (V hh z) :
  to_Spec.fmk hm (((from_Spec 𝒜 hm f_deg).app V) hh) z =
  hh.val z :=
begin
  classical,

  set b_hh := ((from_Spec 𝒜 hm f_deg).app V hh) with b_hh_eq,
  unfold to_Spec.fmk to_Spec.num to_Spec.denom,
  set inv_z := ((Proj_iso_Spec_Top_component hm f_deg).inv z) with inv_z_eq,
  have inv_z_mem : inv_z.1 ∈
    ((@opens.open_embedding Proj.T (pbo f)).is_open_map.functor.op.obj
    ((opens.map (Proj_iso_Spec_Top_component hm f_deg).hom).op.obj V)).unop,
  { apply to_Spec_from_Spec.inv_mem, },

  have inv_z_mem_bo : inv_z.1 ∈ projective_spectrum.basic_open 𝒜 f,
  { apply to_Spec_from_Spec.inv_mem_pbo, },

  set hart := b_hh.1 ⟨inv_z.1, inv_z_mem⟩ with hart_eq,
  rw homogeneous_localization.ext_iff_val at hart_eq,
  have hart_eq1 := hart.eq_num_div_denom,
  rw hart_eq at hart_eq1,

  rw b_hh_eq at hart_eq,
  replace hart_eq : hart.val = (from_Spec.bmk hm f_deg V hh ⟨inv_z.val, inv_z_mem⟩).val,
  { convert hart_eq },
  unfold from_Spec.bmk at hart_eq,
  rw [homogeneous_localization.val_mk'] at hart_eq,
  simp only [← subtype.val_eq_coe] at hart_eq,
  unfold from_Spec.num from_Spec.denom at hart_eq,

  set data := from_Spec.data hm f_deg hh ⟨inv_z.val, inv_z_mem⟩ with data_eq,
  have data_eq1 := data_eq,
  unfold from_Spec.data at data_eq1,
  erw from_Spec.data.eq_num_div_denom at data_eq,
  erw data_eq at data_eq1,
  set nn := from_Spec.data.num hm f_deg hh ⟨inv_z.val, inv_z_mem⟩ with nn_eq,
  set dd := from_Spec.data.denom hm f_deg hh ⟨inv_z.val, inv_z_mem⟩ with dd_eq,
  dsimp only at hart_eq,

  rw hart.eq_num_div_denom at hart_eq,
  rw [localization.mk_eq_mk', is_localization.eq] at hart_eq,
  obtain ⟨⟨C, hC⟩, eq1⟩ := hart_eq,
  simp only [←subtype.val_eq_coe] at eq1,
  have hC2 : ∃ j : ℕ, graded_algebra.proj 𝒜 j C ∉ inv_z.1.as_homogeneous_ideal,
  { by_contra rid,
    rw not_exists at rid,
    apply hC,
    rw ←direct_sum.sum_support_decompose 𝒜 C,
    apply ideal.sum_mem inv_z.1.as_homogeneous_ideal.1,
    intros j hj,
    specialize rid j,
    rw not_not at rid,
    exact rid, },
  obtain ⟨j, hj⟩ := hC2,

  have proj_C_ne_zero : graded_algebra.proj 𝒜 j C ≠ 0,
  { intro rid,
    rw rid at hj,
    apply hj,
    exact submodule.zero_mem _, },

  have dd_not_mem_z : dd ∉ z.val.as_ideal,
  { apply to_Spec_from_Spec.dd_not_mem_z, },

  have eq0 : (hh.1 z) = localization.mk nn ⟨dd, dd_not_mem_z⟩,
  { convert to_Spec_from_Spec.eq0 hm f_deg _ hh z ⟨dd, _⟩ nn data_eq1, },
  rw [eq0, localization.mk_eq_mk', is_localization.eq],
  simp only [←subtype.val_eq_coe, subtype.ext_iff_val, degree_zero_part.mul_val],
  rw [degree_zero_part.eq, degree_zero_part.eq, localization.mk_mul, localization.mk_mul],

  refine ⟨⟨⟨localization.mk ((graded_algebra.proj 𝒜 j C)^m) ⟨f^j, ⟨j, rfl⟩⟩,
    ⟨j, ⟨(graded_algebra.proj 𝒜 j C)^m, set_like.graded_monoid.pow_mem _ (submodule.coe_mem _)⟩, rfl⟩⟩,
    to_Spec_from_Spec.not_mem1 hm f_deg V z C j hj⟩, _⟩,
  { rw [localization.mk_mul, localization.mk_mul, localization.mk_eq_mk', is_localization.eq],
    use 1,
    simp only [←subtype.val_eq_coe,
      show ∀ (p q : submonoid.powers f), (p * q).1 = p.1 * q.1, from λ _ _, rfl, ←pow_add,
      show (1 : submonoid.powers f).1 = 1, from rfl, mul_one, one_mul],
    apply to_Spec_from_Spec.eq1,
    exact hj,
    apply to_Spec_from_Spec.eq2;
    assumption, }
end

end to_Spec_from_Spec

end Proj_iso_Spec_Sheaf_component

def Sheaf_component {m : ℕ} {f : A} (f_deg : f ∈ 𝒜 m) (hm : 0 < m) :
  (Proj_iso_Spec_Top_component hm f_deg).hom _* (Proj| (pbo f)).presheaf ≅ (Spec (A⁰_ f_deg)).presheaf :=
{ hom := Proj_iso_Spec_Sheaf_component.to_Spec 𝒜 hm f_deg,
  inv := Proj_iso_Spec_Sheaf_component.from_Spec 𝒜 hm f_deg,
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
  (X Y : @@SheafedSpace C _ (by assumption : limits.has_products C)) (H : X.to_PresheafedSpace ≅ Y.to_PresheafedSpace) : X ≅ Y :=
 { hom := H.hom,
   inv := H.inv,
   hom_inv_id' := H.hom_inv_id',
   inv_hom_id' := H.inv_hom_id' }

def Proj_iso_Spec_Sheaf_component.iso {m : ℕ} {f : A} (f_deg : f ∈ 𝒜 m) (hm : 0 < m) :
  (Proj| (pbo f)) ≅ Spec (A⁰_ f_deg) :=
LocallyRingedSpace.iso_of_SheafedSpace_iso $ SheafedSpace.iso_of_PresheafedSpace_iso _ _ $ 
@PresheafedSpace.iso_of_components _ _ 
(Proj| (pbo f)).to_PresheafedSpace 
(Spec (A⁰_ f_deg)).to_PresheafedSpace 
(Proj_iso_Spec_Top_component hm f_deg) (Sheaf_component 𝒜 f_deg hm)

end algebraic_geometry