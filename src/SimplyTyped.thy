theory SimplyTyped
imports Main Permutation
begin

type_synonym tvar = nat

datatype type =
  TVar tvar
| TArr type type

datatype 'a pretrm =
  Var 'a
| App "'a pretrm" "'a pretrm"
| Fn 'a type "'a pretrm"

fun FV :: "'a pretrm \<Rightarrow> 'a set" where
  "FV (Var x) = {x}"
| "FV (App A B) = FV A \<union> FV B"
| "FV (Fn x _ A) = FV A - {x}"

fun pretrm_apply_prm :: "'a prm \<Rightarrow> 'a pretrm \<Rightarrow> 'a pretrm" (infixr "\<cdot>" 150) where
  "pretrm_apply_prm \<pi> (Var x) = Var (\<pi> $ x)"
| "pretrm_apply_prm \<pi> (App A B) = App (pretrm_apply_prm \<pi> A) (pretrm_apply_prm \<pi> B)"
| "pretrm_apply_prm \<pi> (Fn x T A) = Fn (\<pi> $ x) T (pretrm_apply_prm \<pi> A)"

inductive pretrm_alpha_equiv :: "'a pretrm \<Rightarrow> 'a pretrm \<Rightarrow> bool" (infix "=a" 100) where
  var:        "(Var x) =a (Var x)"
| app:        "\<lbrakk>A =a B; C =a D\<rbrakk> \<Longrightarrow> (App A C) =a (App B D)"
| fn1:        "A =a B \<Longrightarrow> (Fn x T A) =a (Fn x T B)"
| fn2:        "\<lbrakk>a \<noteq> b; A =a [a \<leftrightarrow> b] \<cdot> B; a \<notin> FV B\<rbrakk> \<Longrightarrow> (Fn a T A) =a (Fn b T B)"

fun pretrm_size :: "'a pretrm \<Rightarrow> nat" where
  "pretrm_size (Var _) = 1"
| "pretrm_size (App A B) = size A + size B"
| "pretrm_size (Fn x T A) = size A + 1"

inductive_cases varE: "Var x =a Y"
inductive_cases appE: "App A B =a Y"
inductive_cases fnE:  "Fn x T A =a Y"

lemma pretrm_prm_apply_id:
  shows "\<epsilon> \<cdot> X = X"
by(induction X, simp_all add: prm_apply_id)

lemma pretrm_prm_apply_compose:
  shows "\<pi> \<cdot> \<sigma> \<cdot> X = (\<pi> \<circ> \<sigma>) \<cdot> X"
by(induction X, simp_all add: prm_apply_composition)

lemma pretrm_prm_fvs:
  shows "FV (\<pi> \<cdot> X) = \<pi> {$} FV X"
unfolding prm_apply_set_def proof(induction X)
  case (Var x)
    thus ?case by auto
  next
oops

lemma pretrm_alpha_equiv_fvs:
  assumes "X =a Y"
  shows "FV X = FV Y"
sorry

lemma pretrm_alpha_equiv_prm:
  assumes "X =a Y"
  shows "\<pi> \<cdot> X =a \<pi> \<cdot> Y"
using assms proof(induction)
  case (var x)
    have "\<pi> \<cdot> Var x = Var (\<pi> $ x)" by simp
    thus ?case using pretrm_alpha_equiv.var by metis
  next
  case (app A B C D)
    have "\<pi> \<cdot> App A C = App (\<pi> \<cdot> A) (\<pi> \<cdot> C)" and "\<pi> \<cdot> App B D = App (\<pi> \<cdot> B) (\<pi> \<cdot> D)" by simp_all
    thus ?case using app.IH pretrm_alpha_equiv.app by metis
  next
  case (fn1 A B x T)
    have "\<pi> \<cdot> (Fn x T A) = Fn (\<pi> $ x) T (\<pi> \<cdot> A)" and "\<pi> \<cdot> (Fn x T B) = Fn (\<pi> $ x) T (\<pi> \<cdot> B)"
      by simp_all
    thus ?case using fn1.IH pretrm_alpha_equiv.fn1 by metis
  next
  case (fn2 a b A B T)
    have A_simp: "\<pi> \<cdot> Fn a T A = Fn (\<pi> $ a) T (\<pi> \<cdot> A)"
    and  B_simp: "\<pi> \<cdot> Fn b T B = Fn (\<pi> $ b) T (\<pi> \<cdot> B)" by simp_all
    
    thus ?case using pretrm_alpha_equiv.fn2 sorry
  next
qed

lemma pretrm_swp_transfer:
  assumes "[a \<leftrightarrow> b] \<cdot> X =a Y"
  shows "X =a [a \<leftrightarrow> b] \<cdot> Y"
proof -
  have "[a \<leftrightarrow> b] \<cdot> [a \<leftrightarrow> b] \<cdot> X =a [a \<leftrightarrow> b] \<cdot> Y"
    using assms pretrm_alpha_equiv_prm by metis
  hence "([a \<leftrightarrow> b] \<circ> [a \<leftrightarrow> b]) \<cdot> X =a [a \<leftrightarrow> b] \<cdot> Y" using pretrm_prm_apply_compose
    by metis
  hence "\<epsilon> \<cdot> X =a [a \<leftrightarrow> b] \<cdot> Y" using prm_unit_involution by metis
  thus ?thesis using pretrm_prm_apply_id by metis
qed

lemma pretrm_alpha_equiv_fvs_transfer:
  assumes "A =a [a \<leftrightarrow> b] \<cdot> B" and "a \<notin> FV B"
  shows "b \<notin> FV A"
sorry

lemma pretrm_alpha_equiv_reflexive:
  shows "M =a M"
by(induction M, (metis pretrm_alpha_equiv.intros)+)

corollary pretrm_alpha_equiv_reflp:
  shows "reflp pretrm_alpha_equiv"
unfolding reflp_def using pretrm_alpha_equiv_reflexive by auto

lemma pretrm_alpha_equiv_symmetric:
  assumes "X =a Y"
  shows "Y =a X"
using assms proof(induction rule: pretrm_alpha_equiv.induct, (metis pretrm_alpha_equiv.intros)+)
  case (fn2 a b A B T)
    have "b \<noteq> a" using `a \<noteq> b` by auto
    have "B =a [b \<leftrightarrow> a] \<cdot> A" using `[a \<leftrightarrow> b] \<cdot> B =a A`
      using pretrm_swp_transfer prm_unit_commutes by metis

    have "b \<notin> FV A" using `a \<notin> FV B` `A =a [a \<leftrightarrow> b] \<cdot> B`
      using pretrm_alpha_equiv_fvs_transfer  by metis

    show ?case using `b \<noteq> a` `B =a [b \<leftrightarrow> a] \<cdot> A` `b \<notin> FV A`
      using pretrm_alpha_equiv.fn2 by metis
  next
qed

corollary pretrm_alpha_equiv_symp:
  shows "symp pretrm_alpha_equiv"
unfolding symp_def using pretrm_alpha_equiv_symmetric by auto

lemma pretrm_alpha_equiv_transitive:
  assumes "X =a Y" and "Y =a Z"
  shows "X =a Z"
using assms proof(induction X arbitrary: Y Z)
  case (Var x)
    hence "Y = Var x" using varE by metis
    hence "Var x =a Z" using `Y =a Z` by simp
    hence "Z = Var x" using varE by metis
    thus ?case using pretrm_alpha_equiv.var by metis
  next
  case (App A B)
    obtain C D where "Y = App C D" and "A =a C" and "B =a D" using appE App.prems by metis
    hence "App C D =a Z" using App.prems by simp
    from this obtain E F where "Z = App E F" and "C =a E" and "D =a F" using appE by metis
    hence "A =a E" using App.IH `A =a C` `C =a E` by metis
    hence "B =a F" using App.IH `B =a D` `D =a F` by metis
    
    show ?case using `Z = App E F` `A =a E` `B =a F` pretrm_alpha_equiv.app by metis
  next
  case (Fn x T A)
    obtain y B where "Y = Fn y T B"
      and Y_cases: "(x = y \<and> A =a B) \<or> (x \<noteq> y \<and> A =a [x \<leftrightarrow> y] \<cdot> B \<and> x \<notin> FV B)"
      using fnE Fn.prems by metis
    obtain z C where Z: "Z = Fn z T C"
      and Z_cases: "(y = z \<and> B =a C) \<or> (y \<noteq> z \<and> B =a [y \<leftrightarrow> z] \<cdot> C \<and> y \<notin> FV C)"
      using fnE Fn.prems `Y = Fn y T B` by metis

    consider
      "x = y" "A =a B" and "y = z" "B =a C"
    | "x = y" "A =a B" and "y \<noteq> z" "B =a [y \<leftrightarrow> z] \<cdot> C" "y \<notin> FV C"
    | "x \<noteq> y" "A =a [x \<leftrightarrow> y] \<cdot> B" "x \<notin> FV B" and "y = z" "B =a C"
    | "x \<noteq> y" "A =a [x \<leftrightarrow> y] \<cdot> B" "x \<notin> FV B" and "y \<noteq> z" "B =a [y \<leftrightarrow> z] \<cdot> C" "y \<notin> FV C"
      using Y_cases Z_cases by auto

    thus ?case proof(cases)
      case 1
        have "A =a C" using `A =a B` `B =a C` Fn.IH by metis
        have "x = z" using `x = y` `y = z` by metis
        show ?thesis using `A =a C` `x = z` Z
          using pretrm_alpha_equiv.fn1 by metis
      next
      case 2
        have "x \<noteq> z" using `x = y` `y \<noteq> z` by metis
        have "A =a [x \<leftrightarrow> z] \<cdot> C" using `A =a B` `B =a [y \<leftrightarrow> z] \<cdot> C` `x = y` Fn.IH by metis
        have "x \<notin> FV C" using `x = y` `y \<notin> FV C` by metis
        thus ?thesis using `x \<noteq> z` `A =a [x \<leftrightarrow> z] \<cdot> C` `x \<notin> FV C` Z
          using pretrm_alpha_equiv.fn2 by metis
      next
      case 3
        have "x \<noteq> z" using `x \<noteq> y` `y = z` by metis
        have "[x \<leftrightarrow> y] \<cdot> B =a [x \<leftrightarrow> y] \<cdot> C" using `B =a C` pretrm_alpha_equiv_prm by metis
        have "A =a [x \<leftrightarrow> z] \<cdot> C"
          using `A =a [x \<leftrightarrow> y] \<cdot> B` `[x \<leftrightarrow> y] \<cdot> B =a [x \<leftrightarrow> y] \<cdot> C` `y = z` Fn.IH
          by metis
        have "x \<notin> FV C" using `B =a C` `x \<notin> FV B` pretrm_alpha_equiv_fvs by metis
        thus ?thesis using `x \<noteq> z` `A =a [x \<leftrightarrow> z] \<cdot> C` `x \<notin> FV C` Z
          using pretrm_alpha_equiv.fn2 by metis
      next
      case 4
        thus ?thesis proof(cases "x = z")
          case True
            have "[x \<leftrightarrow> y] \<cdot> B =a [x \<leftrightarrow> y] \<cdot> [y \<leftrightarrow> z] \<cdot> C"
              using `B =a [y \<leftrightarrow> z] \<cdot> C` pretrm_alpha_equiv_prm by metis
            hence "A =a [x \<leftrightarrow> y] \<cdot> [y \<leftrightarrow> z] \<cdot> C"
              using `A =a [x \<leftrightarrow> y] \<cdot> B` Fn.IH by metis
            hence "A =a ([x \<leftrightarrow> y] \<circ> [y \<leftrightarrow> z]) \<cdot> C" using pretrm_prm_apply_compose by metis
            hence "A =a ([x \<leftrightarrow> y] \<circ> [y \<leftrightarrow> x]) \<cdot> C" using `x = z` by metis
            hence "A =a ([x \<leftrightarrow> y] \<circ> [x \<leftrightarrow> y]) \<cdot> C" using prm_unit_commutes by metis
            hence "A =a \<epsilon> \<cdot> C" using `x = z` prm_unit_involution by metis
            hence "A =a C" using pretrm_prm_apply_id by metis

            thus ?thesis using `x = z` `A =a C` Z
              using pretrm_alpha_equiv.fn1 by metis
          next
          case False
            have "A =a [x \<leftrightarrow> y] \<cdot> [y \<leftrightarrow> z] \<cdot> C"
              using `A =a [x \<leftrightarrow> y] \<cdot> B` `B =a [y \<leftrightarrow> z] \<cdot> C` pretrm_alpha_equiv_prm Fn.IH by metis
            hence "A =a ([x \<leftrightarrow> y] \<circ> [y \<leftrightarrow> z]) \<cdot> C" using pretrm_prm_apply_compose by metis
            hence "A =a [x \<leftrightarrow> z] \<cdot> C" sorry

            have "x \<notin> FV C" sorry
            show ?thesis using `x \<noteq> z` `A =a [x \<leftrightarrow> z] \<cdot> C` `x \<notin> FV C` Z
              using pretrm_alpha_equiv.fn2 by metis
          next
        qed
      next
    qed
  next
qed

corollary pretrm_alpha_equiv_transp:
  shows "transp pretrm_alpha_equiv"
unfolding transp_def using pretrm_alpha_equiv_transitive by auto

type_synonym 'a typing_ctx = "'a \<rightharpoonup> type"

fun pretrm_infer_type :: "'a typing_ctx \<Rightarrow> 'a pretrm \<Rightarrow> type option" where
  "pretrm_infer_type \<Gamma> (Var x) = \<Gamma> x"
| "pretrm_infer_type \<Gamma> (App A B) = (case pretrm_infer_type \<Gamma> A of
     Some (TArr \<tau> \<sigma>) \<Rightarrow> (case pretrm_infer_type \<Gamma> B of
       Some \<tau>' \<Rightarrow> (if \<tau> = \<tau>' then Some \<sigma> else None)
     | _ \<Rightarrow> None)
   | _ \<Rightarrow> None)"
| "pretrm_infer_type \<Gamma> (Fn x \<tau> A) = (case pretrm_infer_type (\<Gamma>(x := Some \<tau>)) A of
     Some \<sigma> \<Rightarrow> Some (TArr \<tau> \<sigma>)
   | _ \<Rightarrow> None)"

lemma pretrm_inference_ctx_invariant:
  assumes "A =a B" "pretrm_infer_type \<Gamma> A = pretrm_infer_type \<Gamma> B"
  shows "pretrm_infer_type (\<Gamma>(x := Some \<tau>)) A = pretrm_infer_type (\<Gamma>(x := Some \<tau>)) B"
sorry

quotient_type 'a trm = "'a pretrm" / pretrm_alpha_equiv
proof(rule equivpI)
  show "reflp  pretrm_alpha_equiv" using pretrm_alpha_equiv_reflp.
  show "symp   pretrm_alpha_equiv" using pretrm_alpha_equiv_symp.
  show "transp pretrm_alpha_equiv" using pretrm_alpha_equiv_transp.
qed

lift_definition infer_type :: "'a typing_ctx \<Rightarrow> 'a trm \<Rightarrow> type option" is pretrm_infer_type
proof -
  fix p1 p2 :: "'a pretrm" and \<Gamma> :: "'a typing_ctx"
  assume "p1 =a p2"
  thus "pretrm_infer_type \<Gamma> p1 = pretrm_infer_type \<Gamma> p2"

  proof(induction rule: pretrm_alpha_equiv.induct)
    case (var x)
      thus ?case by auto
    next
    case (app A B C D)
      thus ?case proof(cases "pretrm_infer_type \<Gamma> A")
        case None
          thus ?thesis using app.IH by auto
        next
        case (Some T)
          thus ?thesis proof(cases T)
            case (TVar t)
              thus ?thesis using `pretrm_infer_type \<Gamma> A = Some T` app.IH by auto
            next
            case (TArr \<tau> \<sigma>)
              thus ?thesis proof(cases "pretrm_infer_type \<Gamma> B")
                case None
                  thus ?thesis using `pretrm_infer_type \<Gamma> A = Some T` app.IH by auto
                next
                case (Some T')
                  thus ?thesis proof(cases "T' = \<tau>")
                    case False
                      thus ?thesis using
                        `pretrm_infer_type \<Gamma> A = Some T`
                        `T = TArr \<tau> \<sigma>`
                        `pretrm_infer_type \<Gamma> B = Some T'`
                        app.IH by auto
                    next
                    case True
                      thus ?thesis using
                        `pretrm_infer_type \<Gamma> A = Some T`
                        `T = TArr \<tau> \<sigma>`
                        `pretrm_infer_type \<Gamma> B = Some T'`
                        app.IH by (metis option.simps(5) pretrm_infer_type.simps(2) type.simps(6))
                    next
                  qed
                next
              qed
            next
          qed
        next
      qed
    next
    case (fn1 A B x \<tau>)
      thus ?case using pretrm_inference_ctx_invariant using pretrm_infer_type.simps by fastforce
    next
    case (fn2 a b A B \<tau>)
      thus ?case sorry
    next
  qed
qed

end